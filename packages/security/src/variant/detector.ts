/**
 * @fileoverview Vulnerability Detector - Taint analysis and pattern matching
 * @module @nahisaho/musubix-security/variant/detector
 * @trace TSK-024, REQ-SEC-VARIANT-002
 */

import type { CodeDB } from '../codedb/database.js';
import type { ASTNode, DFGNode, TaintPath } from '../types/codedb.js';
import type {
  VulnerabilityModel,
  SourcePattern,
  SinkPattern,
  SanitizerPattern,
  VulnerabilityFinding,
  TaintFlow,
  FlowStep,
  DetectorOptions,
  DetectorResult,
} from '../types/variant.js';
import { VulnerabilityModelManager } from './model.js';

/**
 * Default detector options
 */
const DEFAULT_DETECTOR_OPTIONS: DetectorOptions = {
  maxPathLength: 20,
  maxPathsPerSink: 100,
  timeout: 30000,
  enableInterProc: true,
  trackImplicitFlows: false,
};

/**
 * Taint state for a variable/expression
 */
interface TaintState {
  readonly nodeId: string;
  readonly source: ASTNode;
  readonly sourceModel: VulnerabilityModel;
  readonly taintedAt: number;
  readonly path: FlowStep[];
}

/**
 * Vulnerability Detector
 */
export class VulnerabilityDetector {
  private readonly modelManager: VulnerabilityModelManager;
  private readonly options: DetectorOptions;
  private findings: VulnerabilityFinding[] = [];
  private taintStates: Map<string, TaintState[]> = new Map();

  constructor(
    modelManager?: VulnerabilityModelManager,
    options?: Partial<DetectorOptions>,
  ) {
    this.modelManager = modelManager ?? new VulnerabilityModelManager();
    this.options = { ...DEFAULT_DETECTOR_OPTIONS, ...options };
  }

  /**
   * Detect vulnerabilities in CodeDB
   */
  async detect(db: CodeDB, language: string): Promise<DetectorResult> {
    const startTime = Date.now();
    this.findings = [];
    this.taintStates.clear();

    const models = this.modelManager.getModelsForLanguage(language);

    // Phase 1: Pattern-based detection (non-taint)
    for (const model of models) {
      if (model.patterns && model.patterns.length > 0) {
        await this.detectPatterns(db, model);
      }
    }

    // Phase 2: Taint analysis
    for (const model of models.filter((m) => m.sources.length > 0)) {
      await this.detectTaintFlows(db, model);
    }

    const executionTime = Date.now() - startTime;

    return {
      findings: this.findings,
      stats: {
        modelsChecked: models.length,
        findingsCount: this.findings.length,
        executionTime,
        pathsAnalyzed: this.countPathsAnalyzed(),
      },
    };
  }

  /**
   * Detect pattern-based vulnerabilities
   */
  private async detectPatterns(db: CodeDB, model: VulnerabilityModel): Promise<void> {
    if (!model.patterns) return;

    // Query all AST nodes with string values
    const nodes = db.queryAST({});

    for (const node of nodes) {
      const text = this.getNodeText(node);
      if (!text) continue;

      for (const pattern of model.patterns) {
        if (pattern.test(text)) {
          this.findings.push(this.createFinding(model, node, null, 'pattern'));
          break;
        }
      }
    }
  }

  /**
   * Detect taint-based vulnerabilities
   */
  private async detectTaintFlows(db: CodeDB, model: VulnerabilityModel): Promise<void> {
    const startTime = Date.now();

    // Step 1: Find sources
    const sources = await this.findSources(db, model);

    // Step 2: For each source, perform taint propagation
    for (const source of sources) {
      if (Date.now() - startTime > this.options.timeout) {
        break; // Timeout
      }

      const taintState: TaintState = {
        nodeId: source.id,
        source,
        sourceModel: model,
        taintedAt: 0,
        path: [this.createFlowStep(source, 'source')],
      };

      this.taintStates.set(source.id, [taintState]);

      // Propagate taint
      await this.propagateTaint(db, model, source, taintState);
    }
  }

  /**
   * Find source nodes matching model
   */
  private async findSources(
    db: CodeDB,
    model: VulnerabilityModel,
  ): Promise<ASTNode[]> {
    const sources: ASTNode[] = [];

    for (const sourcePattern of model.sources) {
      const matchingNodes = await this.findMatchingNodes(db, sourcePattern);
      sources.push(...matchingNodes);
    }

    return sources;
  }

  /**
   * Find AST nodes matching a pattern
   */
  private async findMatchingNodes(
    db: CodeDB,
    pattern: SourcePattern | SinkPattern,
  ): Promise<ASTNode[]> {
    const results: ASTNode[] = [];

    // Query by pattern type
    let nodeType: string;
    switch (pattern.type) {
      case 'function_call':
        nodeType = 'call_expression';
        break;
      case 'method_call':
        nodeType = 'call_expression';
        break;
      case 'property_access':
        nodeType = 'member_expression';
        break;
      case 'parameter':
        nodeType = 'parameter';
        break;
      case 'variable':
        nodeType = 'variable_declaration';
        break;
      case 'string_literal':
        nodeType = 'string';
        break;
      case 'configuration':
        nodeType = 'call_expression';
        break;
      case 'validation':
        nodeType = 'if_statement';
        break;
      default:
        nodeType = 'call_expression';
    }

    const candidates = db.queryAST({ type: nodeType });

    for (const node of candidates) {
      const text = this.getNodeText(node);
      if (text && pattern.patterns.some((p) => p.test(text))) {
        results.push(node);
      }
    }

    return results;
  }

  /**
   * Propagate taint from source to sinks
   */
  private async propagateTaint(
    db: CodeDB,
    model: VulnerabilityModel,
    source: ASTNode,
    initialState: TaintState,
  ): Promise<void> {
    const visited = new Set<string>();
    const worklist: TaintState[] = [initialState];

    while (worklist.length > 0) {
      const current = worklist.pop()!;

      if (visited.has(current.nodeId)) continue;
      visited.add(current.nodeId);

      if (current.path.length > this.options.maxPathLength) continue;

      // Check if current node is a sink
      if (await this.isSink(db, current.nodeId, model)) {
        const sinkNode = db.queryAST({ id: current.nodeId })[0];
        if (sinkNode && !this.isSanitized(current.path, model)) {
          this.findings.push(
            this.createFinding(model, source, sinkNode, 'taint', current.path),
          );
        }
        continue;
      }

      // Get data flow successors
      const successors = this.getDataFlowSuccessors(db, current.nodeId);

      for (const succ of successors) {
        // Check for sanitizer
        if (await this.isSanitizer(db, succ, model)) {
          continue; // Taint is sanitized
        }

        const succNode = db.queryAST({ id: succ })[0];
        if (!succNode) continue;

        const newState: TaintState = {
          nodeId: succ,
          source: current.source,
          sourceModel: current.sourceModel,
          taintedAt: current.taintedAt + 1,
          path: [...current.path, this.createFlowStep(succNode, 'step')],
        };

        worklist.push(newState);
      }
    }
  }

  /**
   * Get data flow successors
   */
  private getDataFlowSuccessors(db: CodeDB, nodeId: string): string[] {
    const dfgNodes = db.queryDataFlow({ astNodeId: nodeId });
    const successors: string[] = [];

    for (const node of dfgNodes) {
      if (node.successors) {
        // Get AST node IDs from DFG successors
        for (const succId of node.successors) {
          const succDfg = db.queryDataFlow({ id: succId });
          for (const succ of succDfg) {
            if (succ.astNodeId) {
              successors.push(succ.astNodeId);
            }
          }
        }
      }
    }

    // Also check call graph for inter-procedural flow
    if (this.options.enableInterProc) {
      const callees = db.getCallees(nodeId);
      successors.push(...callees);
    }

    return successors;
  }

  /**
   * Check if node is a sink
   */
  private async isSink(
    db: CodeDB,
    nodeId: string,
    model: VulnerabilityModel,
  ): Promise<boolean> {
    const nodes = db.queryAST({ id: nodeId });
    if (nodes.length === 0) return false;

    const node = nodes[0];
    const text = this.getNodeText(node);
    if (!text) return false;

    for (const sinkPattern of model.sinks) {
      if (sinkPattern.patterns.some((p) => p.test(text))) {
        return true;
      }
    }

    return false;
  }

  /**
   * Check if node is a sanitizer
   */
  private async isSanitizer(
    db: CodeDB,
    nodeId: string,
    model: VulnerabilityModel,
  ): Promise<boolean> {
    const nodes = db.queryAST({ id: nodeId });
    if (nodes.length === 0) return false;

    const node = nodes[0];
    const text = this.getNodeText(node);
    if (!text) return false;

    for (const sanitizerPattern of model.sanitizers) {
      if (sanitizerPattern.patterns.some((p) => p.test(text))) {
        return true;
      }
    }

    return false;
  }

  /**
   * Check if taint flow is sanitized
   */
  private isSanitized(path: FlowStep[], model: VulnerabilityModel): boolean {
    for (const step of path) {
      const text = step.codeSnippet;
      if (!text) continue;

      for (const sanitizerPattern of model.sanitizers) {
        if (sanitizerPattern.patterns.some((p) => p.test(text))) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Get text representation of AST node
   */
  private getNodeText(node: ASTNode): string | undefined {
    return node.name ?? node.value ?? undefined;
  }

  /**
   * Create flow step from AST node
   */
  private createFlowStep(
    node: ASTNode,
    kind: 'source' | 'step' | 'sink',
  ): FlowStep {
    return {
      nodeId: node.id,
      location: node.location
        ? {
            file: node.location.file,
            line: node.location.start.line,
            column: node.location.start.column,
          }
        : undefined,
      codeSnippet: this.getNodeText(node),
      kind,
    };
  }

  /**
   * Create vulnerability finding
   */
  private createFinding(
    model: VulnerabilityModel,
    source: ASTNode,
    sink: ASTNode | null,
    detectionMethod: 'taint' | 'pattern',
    path?: FlowStep[],
  ): VulnerabilityFinding {
    const finding: VulnerabilityFinding = {
      id: `${model.id}-${Date.now()}-${Math.random().toString(36).substring(7)}`,
      modelId: model.id,
      modelName: model.name,
      cweId: model.cweId,
      severity: model.severity,
      category: model.category,
      description: this.generateDescription(model, source, sink),
      location: source.location
        ? {
            file: source.location.file,
            startLine: source.location.start.line,
            endLine: source.location.end.line,
            startColumn: source.location.start.column,
            endColumn: source.location.end.column,
          }
        : { file: 'unknown', startLine: 0, endLine: 0, startColumn: 0, endColumn: 0 },
      detectionMethod,
      confidence: this.calculateConfidence(model, path),
    };

    if (path && sink) {
      finding.taintFlow = {
        source: {
          nodeId: source.id,
          location: source.location
            ? {
                file: source.location.file,
                line: source.location.start.line,
                column: source.location.start.column,
              }
            : undefined,
          codeSnippet: this.getNodeText(source),
          kind: 'source',
        },
        sink: {
          nodeId: sink.id,
          location: sink.location
            ? {
                file: sink.location.file,
                line: sink.location.start.line,
                column: sink.location.start.column,
              }
            : undefined,
          codeSnippet: this.getNodeText(sink),
          kind: 'sink',
        },
        steps: path,
        pathLength: path.length,
      };
    }

    return finding;
  }

  /**
   * Generate finding description
   */
  private generateDescription(
    model: VulnerabilityModel,
    source: ASTNode,
    sink: ASTNode | null,
  ): string {
    const sourceText = this.getNodeText(source) ?? 'unknown source';

    if (sink) {
      const sinkText = this.getNodeText(sink) ?? 'unknown sink';
      return `${model.name}: User input from '${sourceText}' flows to '${sinkText}' without proper sanitization.`;
    }

    return `${model.name}: Potentially unsafe pattern detected at '${sourceText}'.`;
  }

  /**
   * Calculate finding confidence
   */
  private calculateConfidence(
    model: VulnerabilityModel,
    path?: FlowStep[],
  ): 'high' | 'medium' | 'low' {
    if (!path) {
      // Pattern-based detection
      return 'medium';
    }

    // Taint-based detection
    if (path.length <= 3) {
      return 'high'; // Short paths are more likely true positives
    }

    if (path.length <= 7) {
      return 'medium';
    }

    return 'low'; // Long paths may have more false positives
  }

  /**
   * Count total paths analyzed
   */
  private countPathsAnalyzed(): number {
    let count = 0;
    for (const states of this.taintStates.values()) {
      count += states.length;
    }
    return count;
  }
}

/**
 * Create vulnerability detector
 */
export function createDetector(
  modelManager?: VulnerabilityModelManager,
  options?: Partial<DetectorOptions>,
): VulnerabilityDetector {
  return new VulnerabilityDetector(modelManager, options);
}
