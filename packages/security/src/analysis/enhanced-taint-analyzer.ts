/**
 * @fileoverview Enhanced Taint Analyzer with interprocedural analysis
 * @module @nahisaho/musubix-security/analysis/enhanced-taint-analyzer
 * @trace REQ-SEC-001 (EARS: THE system SHALL provide interprocedural taint analysis)
 * @trace TSK-SEC-008
 */

import type {
  TaintPath,
  TaintResult,
  TaintAnalysisOptions,
  TaintSourceCategory,
  TaintSinkCategory,
  Severity,
} from '../types/index.js';
import type { DataFlowGraph } from '@nahisaho/musubix-dfg';

import { TaintAnalyzer, resetTaintCounters } from './taint-analyzer.js';
import { CallGraphBuilder, type CallGraph, type CallGraphStatistics } from './interprocedural/call-graph-builder.js';
import { TaintPropagator, type TaintFinding, type TaintLocation } from './interprocedural/taint-propagator.js';
import { DFGTaintAdapter, type DFGTaintResult, type DFGTaintStatistics } from './interprocedural/dfg-adapter.js';
import type { SourceDefinition } from './sources/types.js';
import type { SinkDefinition } from './sinks/types.js';

// Import aggregated built-ins
import { ALL_BUILTIN_SOURCES } from './sources/index.js';
import { ALL_BUILTIN_SINKS } from './sinks/index.js';
import { ALL_BUILTIN_SANITIZERS } from './sanitizers/index.js';

/**
 * Options for enhanced taint analysis
 */
export interface EnhancedTaintOptions extends TaintAnalysisOptions {
  /** Enable interprocedural analysis */
  interprocedural?: boolean;
  /** Enable DFG-based analysis */
  useDFG?: boolean;
  /** Include call graph building */
  buildCallGraph?: boolean;
  /** Maximum call depth for interprocedural analysis */
  maxCallDepth?: number;
  /** Track implicit flows (control dependencies) */
  trackImplicitFlows?: boolean;
  /** Custom source definitions */
  customSourceDefinitions?: SourceDefinition[];
  /** Custom sink definitions */
  customSinkDefinitions?: SinkDefinition[];
}

/**
 * Result from enhanced taint analysis
 */
export interface EnhancedTaintResult extends TaintResult {
  /** Call graph (if built) */
  callGraph?: CallGraph;
  /** Call graph statistics */
  callGraphStats?: CallGraphStatistics;
  /** Interprocedural findings */
  interproceduralFindings?: TaintFinding[];
  /** DFG-based results (if enabled) */
  dfgResults?: DFGTaintResult[];
  /** DFG statistics */
  dfgStats?: DFGTaintStatistics;
  /** Analysis mode used */
  analysisMode: 'intraprocedural' | 'interprocedural' | 'dfg' | 'combined';
}

/**
 * Enhanced Taint Analyzer with interprocedural capabilities
 * @trace REQ-SEC-001, TSK-SEC-008
 */
export class EnhancedTaintAnalyzer {
  private baseAnalyzer: TaintAnalyzer;
  private callGraphBuilder: CallGraphBuilder | null = null;
  private taintPropagator: TaintPropagator | null = null;
  private dfgAdapter: DFGTaintAdapter | null = null;
  private options: EnhancedTaintOptions;
  
  private sourceDefinitions: SourceDefinition[];
  private sinkDefinitions: SinkDefinition[];

  constructor(options: EnhancedTaintOptions = {}) {
    this.baseAnalyzer = new TaintAnalyzer(options);
    this.options = {
      // Base options
      customSources: options.customSources ?? [],
      customSinks: options.customSinks ?? [],
      additionalSanitizers: options.additionalSanitizers ?? [],
      excludePatterns: options.excludePatterns ?? ['node_modules', 'dist', '.git'],
      maxPathDepth: options.maxPathDepth ?? 10,
      trackAsync: options.trackAsync ?? true,
      
      // Enhanced options
      interprocedural: options.interprocedural ?? true,
      useDFG: options.useDFG ?? false,
      buildCallGraph: options.buildCallGraph ?? true,
      maxCallDepth: options.maxCallDepth ?? 5,
      trackImplicitFlows: options.trackImplicitFlows ?? false,
      customSourceDefinitions: options.customSourceDefinitions ?? [],
      customSinkDefinitions: options.customSinkDefinitions ?? [],
    };

    // Collect all source definitions
    this.sourceDefinitions = [
      ...ALL_BUILTIN_SOURCES,
      ...(this.options.customSourceDefinitions ?? []),
    ];

    // Collect all sink definitions
    this.sinkDefinitions = [
      ...ALL_BUILTIN_SINKS,
      ...(this.options.customSinkDefinitions ?? []),
    ];

    // Initialize interprocedural components if enabled
    if (this.options.interprocedural || this.options.buildCallGraph) {
      this.callGraphBuilder = new CallGraphBuilder({
        maxDepth: this.options.maxCallDepth,
        trackCallbacks: true,
        includeAnonymous: true,
      });

      this.taintPropagator = new TaintPropagator(
        this.sourceDefinitions,
        this.sinkDefinitions,
        [...ALL_BUILTIN_SANITIZERS],
        {
          maxDepth: this.options.maxCallDepth,
          trackImplicitFlows: this.options.trackImplicitFlows,
          minConfidence: 0.5,
        }
      );
    }

    // Initialize DFG adapter if enabled
    if (this.options.useDFG) {
      this.dfgAdapter = new DFGTaintAdapter(
        this.sourceDefinitions,
        this.sinkDefinitions,
        {
          trackAliasing: true,
          trackControlDependencies: this.options.trackImplicitFlows,
          maxDepth: (this.options.maxCallDepth ?? 5) * 4,
          minConfidence: 0.5,
        }
      );
    }
  }

  /**
   * Reset analysis state (for testing)
   */
  static resetState(): void {
    resetTaintCounters();
  }

  /**
   * Analyze a directory with enhanced taint analysis
   */
  async analyze(rootPath: string): Promise<EnhancedTaintResult> {
    const startTime = Date.now();
    
    // Step 1: Run base intraprocedural analysis
    const baseResult = await this.baseAnalyzer.analyze(rootPath);

    // Determine analysis mode
    let analysisMode: EnhancedTaintResult['analysisMode'] = 'intraprocedural';
    if (this.options.useDFG && this.options.interprocedural) {
      analysisMode = 'combined';
    } else if (this.options.useDFG) {
      analysisMode = 'dfg';
    } else if (this.options.interprocedural) {
      analysisMode = 'interprocedural';
    }

    // Initialize enhanced result
    const result: EnhancedTaintResult = {
      ...baseResult,
      analysisMode,
    };

    // Step 2: Build call graph if enabled
    if (this.options.buildCallGraph && this.callGraphBuilder) {
      try {
        const callGraph = await this.callGraphBuilder.buildFromDirectory(rootPath);
        result.callGraph = callGraph;
        result.callGraphStats = this.callGraphBuilder.getStatistics(result.callGraph);
      } catch (error) {
        console.warn(`Warning: Failed to build call graph: ${error}`);
      }
    }

    // Step 3: Run interprocedural analysis if enabled
    if (this.options.interprocedural && this.taintPropagator && result.callGraph) {
      try {
        const sourceLocations = this.extractSourceLocations(baseResult);
        const findings = this.taintPropagator.analyze(
          result.callGraph,
          sourceLocations
        );
        result.interproceduralFindings = findings;

        // Merge interprocedural findings into unsafe paths
        const mergedPaths = this.mergeFindings(
          result.unsafePaths,
          findings
        );
        result.unsafePaths = mergedPaths;
      } catch (error) {
        console.warn(`Warning: Interprocedural analysis failed: ${error}`);
      }
    }

    // Update duration
    result.duration = Date.now() - startTime;

    // Update summary
    result.summary = this.buildSummary(result);

    return result;
  }

  /**
   * Analyze with DFG
   */
  async analyzeWithDFG(rootPath: string, dfgs: DataFlowGraph[]): Promise<EnhancedTaintResult> {
    const startTime = Date.now();
    
    // Run base analysis
    const baseResult = await this.baseAnalyzer.analyze(rootPath);
    
    const result: EnhancedTaintResult = {
      ...baseResult,
      analysisMode: 'dfg',
      dfgResults: [],
    };

    // Analyze each DFG
    if (this.dfgAdapter && dfgs.length > 0) {
      let totalStats: DFGTaintStatistics = {
        totalNodes: 0,
        taintedNodes: 0,
        sources: 0,
        sinks: 0,
        vulnerablePaths: 0,
        sanitizedPaths: 0,
        avgConfidence: 0,
      };

      for (const dfg of dfgs) {
        const dfgResult = this.dfgAdapter.analyzeTaint(dfg);
        result.dfgResults!.push(dfgResult);

        // Accumulate statistics
        const stats = this.dfgAdapter.getStatistics(dfgResult);
        totalStats.totalNodes += stats.totalNodes;
        totalStats.taintedNodes += stats.taintedNodes;
        totalStats.sources += stats.sources;
        totalStats.sinks += stats.sinks;
        totalStats.vulnerablePaths += stats.vulnerablePaths;
        totalStats.sanitizedPaths += stats.sanitizedPaths;
      }

      // Calculate average confidence
      if (totalStats.vulnerablePaths > 0) {
        const totalConfidence = result.dfgResults!.reduce((sum, r) => {
          return sum + r.vulnerablePaths.reduce((s, p) => s + p.confidence, 0);
        }, 0);
        totalStats.avgConfidence = totalConfidence / totalStats.vulnerablePaths;
      }

      result.dfgStats = totalStats;

      // Convert DFG paths to TaintPath format
      const dfgPaths = this.convertDFGPaths(result.dfgResults!);
      result.unsafePaths = [...result.unsafePaths, ...dfgPaths];
    }

    result.duration = Date.now() - startTime;
    result.summary = this.buildSummary(result);

    return result;
  }

  /**
   * Extract source locations from base analysis
   */
  private extractSourceLocations(baseResult: TaintResult): TaintLocation[] {
    return baseResult.sources.map((source) => ({
      nodeId: source.id,
      identifier: source.variableName,
      line: source.location.startLine,
      column: source.location.startColumn,
      filePath: source.location.file,
    }));
  }

  /**
   * Merge intraprocedural and interprocedural findings
   */
  private mergeFindings(
    intraPaths: TaintPath[],
    interFindings: TaintFinding[]
  ): TaintPath[] {
    const merged = [...intraPaths];
    const existingKeys = new Set(
      intraPaths.map(p => `${p.source.location.file}:${p.source.location.startLine}:${p.sink.location.file}:${p.sink.location.startLine}`)
    );

    // Convert interprocedural findings to TaintPath format
    for (const finding of interFindings) {
      const key = `${finding.source.location.file}:${finding.source.location.line}:${finding.sink.location.file}:${finding.sink.location.line}`;
      
      // Skip if already covered by intraprocedural analysis
      if (existingKeys.has(key)) continue;

      merged.push(this.convertFindingToPath(finding));
    }

    return merged;
  }

  /**
   * Convert TaintFinding to TaintPath
   */
  private convertFindingToPath(finding: TaintFinding): TaintPath {
    const sourceCategory = (finding.source.type || 'user-input') as TaintSourceCategory;
    const sinkCategory = finding.sink.category;

    return {
      id: finding.id,
      source: {
        id: finding.source.id,
        category: sourceCategory,
        location: {
          file: finding.source.location.file,
          startLine: finding.source.location.line,
          startColumn: finding.source.location.column,
          endLine: finding.source.location.line,
          endColumn: finding.source.location.column + (finding.source.name?.length ?? 0),
        },
        variableName: finding.source.name ?? 'unknown',
        expression: finding.source.name ?? 'unknown',
        description: `Taint source: ${finding.source.name}`,
        confidence: finding.source.confidence,
      },
      sink: {
        id: finding.sink.id,
        category: sinkCategory,
        location: {
          file: finding.sink.location.file,
          startLine: finding.sink.location.line,
          startColumn: finding.sink.location.column,
          endLine: finding.sink.location.line,
          endColumn: finding.sink.location.column + (finding.sink.name?.length ?? 0),
        },
        functionName: finding.sink.name ?? 'unknown',
        argumentIndex: 0,
        expectedSanitizers: [],
        description: `Taint sink: ${finding.sink.name}`,
        severity: finding.severity,
      },
      steps: finding.flowPath.map((edge, idx) => ({
        index: idx,
        location: {
          file: edge.from.filePath,
          startLine: edge.from.line,
          startColumn: edge.from.column,
          endLine: edge.from.line,
          endColumn: edge.from.column,
        },
        expression: edge.from.identifier ?? '',
        operation: this.mapFlowTypeToOperation(edge.flowType),
        sanitized: edge.sanitizersApplied.length > 0,
      })),
      sanitized: finding.sanitizationComplete,
      confidence: finding.confidence,
      length: finding.flowPath.length,
    };
  }

  /**
   * Map TaintFlowType to TaintFlowStep operation
   */
  private mapFlowTypeToOperation(flowType: string): 'assignment' | 'parameter' | 'return' | 'property-access' | 'call' | 'array-access' {
    const mapping: Record<string, 'assignment' | 'parameter' | 'return' | 'property-access' | 'call' | 'array-access'> = {
      'assignment': 'assignment',
      'parameter': 'parameter',
      'return': 'return',
      'property-access': 'property-access',
      'method-call': 'call',
      'callback': 'call',
      'implicit': 'assignment',
    };
    return mapping[flowType] ?? 'assignment';
  }

  /**
   * Convert DFG results to TaintPath format
   */
  private convertDFGPaths(dfgResults: DFGTaintResult[]): TaintPath[] {
    const paths: TaintPath[] = [];
    let pathCounter = 0;

    for (const dfgResult of dfgResults) {
      for (const vulnPath of dfgResult.vulnerablePaths) {
        if (vulnPath.isSanitized) continue; // Skip sanitized paths

        pathCounter++;
        paths.push({
          id: `DFG-PATH-${String(pathCounter).padStart(4, '0')}`,
          source: {
            id: `DFG-SRC-${pathCounter}`,
            category: 'user-input' as TaintSourceCategory,
            location: {
              file: vulnPath.source.filePath,
              startLine: vulnPath.source.line,
              startColumn: vulnPath.source.column,
              endLine: vulnPath.source.line,
              endColumn: vulnPath.source.column,
            },
            variableName: vulnPath.source.identifier ?? '',
            expression: vulnPath.source.identifier ?? '',
            description: 'DFG-detected taint source',
            confidence: vulnPath.confidence,
          },
          sink: {
            id: `DFG-SNK-${pathCounter}`,
            category: 'sql-query' as TaintSinkCategory,
            location: {
              file: vulnPath.sink.filePath,
              startLine: vulnPath.sink.line,
              startColumn: vulnPath.sink.column,
              endLine: vulnPath.sink.line,
              endColumn: vulnPath.sink.column,
            },
            functionName: vulnPath.sink.identifier ?? '',
            argumentIndex: 0,
            expectedSanitizers: [],
            description: 'DFG-detected taint sink',
            severity: 'high',
          },
          steps: vulnPath.path.map((nodeId, index) => ({
            index,
            location: {
              file: vulnPath.source.filePath,
              startLine: 0,
              startColumn: 0,
              endLine: 0,
              endColumn: 0,
            },
            expression: nodeId,
            operation: 'assignment',
            sanitized: false,
          })),
          sanitized: vulnPath.isSanitized,
          confidence: vulnPath.confidence,
          length: vulnPath.path.length,
        });
      }
    }

    return paths;
  }

  /**
   * Build summary from results
   */
  private buildSummary(result: EnhancedTaintResult): TaintResult['summary'] {
    const bySeverity: Record<Severity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };

    const bySourceCategory: Record<TaintSourceCategory, number> = {
      'user-input': 0,
      'database': 0,
      'file-system': 0,
      'network': 0,
      'environment': 0,
      'config': 0,
      'cli-args': 0,
    };

    const bySinkCategory: Record<TaintSinkCategory, number> = {
      'sql-query': 0,
      'nosql-query': 0,
      'command-exec': 0,
      'file-write': 0,
      'file-read': 0,
      'html-output': 0,
      'redirect': 0,
      'eval': 0,
      'deserialization': 0,
      'ldap-query': 0,
      'xpath-query': 0,
      'http-request': 0,
    };

    for (const path of result.unsafePaths) {
      bySeverity[path.sink.severity]++;
      bySourceCategory[path.source.category]++;
      bySinkCategory[path.sink.category]++;
    }

    return {
      totalSources: result.sources.length,
      totalSinks: result.sinks.length,
      unsafePathCount: result.unsafePaths.length,
      bySeverity,
      bySourceCategory,
      bySinkCategory,
    };
  }

  /**
   * Get source definitions
   */
  getSourceDefinitions(): SourceDefinition[] {
    return [...this.sourceDefinitions];
  }

  /**
   * Get sink definitions
   */
  getSinkDefinitions(): SinkDefinition[] {
    return [...this.sinkDefinitions];
  }

  /**
   * Add custom source definition
   */
  addSourceDefinition(source: SourceDefinition): void {
    this.sourceDefinitions.push(source);
    // Reinitialize propagator with new definitions
    if (this.taintPropagator) {
      this.taintPropagator = new TaintPropagator(
        this.sourceDefinitions,
        this.sinkDefinitions,
        [...ALL_BUILTIN_SANITIZERS],
        {
          maxDepth: this.options.maxCallDepth,
          trackImplicitFlows: this.options.trackImplicitFlows,
          minConfidence: 0.5,
        }
      );
    }
  }

  /**
   * Add custom sink definition
   */
  addSinkDefinition(sink: SinkDefinition): void {
    this.sinkDefinitions.push(sink);
    // Reinitialize propagator with new definitions
    if (this.taintPropagator) {
      this.taintPropagator = new TaintPropagator(
        this.sourceDefinitions,
        this.sinkDefinitions,
        [...ALL_BUILTIN_SANITIZERS],
        {
          maxDepth: this.options.maxCallDepth,
          trackImplicitFlows: this.options.trackImplicitFlows,
          minConfidence: 0.5,
        }
      );
    }
  }
}

/**
 * Create enhanced taint analyzer
 */
export function createEnhancedTaintAnalyzer(
  options?: EnhancedTaintOptions
): EnhancedTaintAnalyzer {
  return new EnhancedTaintAnalyzer(options);
}
