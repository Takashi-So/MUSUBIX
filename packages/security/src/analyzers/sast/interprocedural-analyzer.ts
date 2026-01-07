/**
 * @fileoverview Interprocedural Analyzer for Cross-Function Data Flow Analysis
 * @module @nahisaho/musubix-security/analyzers/sast/interprocedural-analyzer
 * @trace DES-SEC2-SAST-004, REQ-SEC2-SAST-004
 */

import type { Vulnerability, Severity, SourceLocation, OWASPCategory } from '../../types/vulnerability.js';

/**
 * Interprocedural analysis result
 */
export interface InterproceduralResult {
  vulnerabilities: InterproceduralVulnerability[];
  callGraph: CallGraph;
  dataFlowPaths: DataFlowPath[];
  analysisMetrics: AnalysisMetrics;
}

/**
 * Interprocedural vulnerability
 */
export interface InterproceduralVulnerability {
  id: string;
  type: 'taint-propagation' | 'privilege-escalation' | 'data-leakage' | 'injection';
  severity: Severity;
  entryPoint: SourceLocation;
  sinkPoint: SourceLocation;
  dataFlowPath: DataFlowPath;
  description: string;
  recommendation: string;
  confidence: number;
}

/**
 * Call graph
 */
export interface CallGraph {
  nodes: CallGraphNode[];
  edges: CallGraphEdge[];
  entryPoints: string[];
  sinks: string[];
}

/**
 * Call graph node
 */
export interface CallGraphNode {
  id: string;
  name: string;
  file: string;
  line: number;
  type: 'function' | 'method' | 'constructor' | 'callback' | 'anonymous';
  isAsync: boolean;
  parameters: ParameterInfo[];
  returnType?: string;
  modifiers: string[];
}

/**
 * Call graph edge
 */
export interface CallGraphEdge {
  source: string;
  target: string;
  callSite: SourceLocation;
  callType: 'direct' | 'indirect' | 'virtual' | 'callback';
  arguments: ArgumentBinding[];
}

/**
 * Parameter information
 */
export interface ParameterInfo {
  name: string;
  index: number;
  type?: string;
  isTainted: boolean;
  taintSource?: string;
}

/**
 * Argument binding
 */
export interface ArgumentBinding {
  parameterIndex: number;
  expression: string;
  isTainted: boolean;
  taintSource?: string;
}

/**
 * Data flow path
 */
export interface DataFlowPath {
  id: string;
  source: DataFlowNode;
  sink: DataFlowNode;
  intermediateNodes: DataFlowNode[];
  taintType: string;
  confidence: number;
  isSanitized: boolean;
  sanitizationPoint?: DataFlowNode;
}

/**
 * Data flow node
 */
export interface DataFlowNode {
  id: string;
  expression: string;
  location: SourceLocation;
  nodeType: 'source' | 'sink' | 'transform' | 'sanitizer' | 'propagator';
  taintState: 'tainted' | 'sanitized' | 'unknown';
}

/**
 * Analysis metrics
 */
export interface AnalysisMetrics {
  totalFunctions: number;
  totalCallSites: number;
  analysisDepth: number;
  executionTime: number;
  nodesVisited: number;
  pathsAnalyzed: number;
}

/**
 * Analysis options
 */
export interface InterproceduralOptions {
  /** Maximum call depth to analyze */
  maxDepth?: number;
  /** Analysis timeout in milliseconds */
  timeout?: number;
  /** Maximum nodes to visit */
  maxNodes?: number;
  /** Enable context-sensitive analysis */
  contextSensitive?: boolean;
  /** Track implicit data flows */
  trackImplicitFlows?: boolean;
  /** Custom source definitions */
  customSources?: TaintSourceDef[];
  /** Custom sink definitions */
  customSinks?: TaintSinkDef[];
  /** Custom sanitizer definitions */
  customSanitizers?: SanitizerDef[];
}

/**
 * Taint source definition
 */
export interface TaintSourceDef {
  pattern: RegExp;
  type: string;
  description: string;
}

/**
 * Taint sink definition
 */
export interface TaintSinkDef {
  pattern: RegExp;
  type: string;
  vulnerabilityType: string;
  severity: Severity;
}

/**
 * Sanitizer definition
 */
export interface SanitizerDef {
  pattern: RegExp;
  sanitizes: string[];
}

/**
 * Built-in taint sources
 */
const DEFAULT_SOURCES: TaintSourceDef[] = [
  { pattern: /req\.(body|query|params|headers|cookies)/, type: 'user-input', description: 'HTTP request input' },
  { pattern: /request\.(json|form|args|values)/, type: 'user-input', description: 'HTTP request input (Python)' },
  { pattern: /process\.env\[/, type: 'environment', description: 'Environment variable' },
  { pattern: /fs\.read|readFile|readFileSync/, type: 'file', description: 'File read' },
  { pattern: /\.query\(|\.execute\(/, type: 'database', description: 'Database query result' },
  { pattern: /localStorage|sessionStorage/, type: 'storage', description: 'Browser storage' },
  { pattern: /window\.location|document\.URL/, type: 'url', description: 'URL parameter' },
  { pattern: /document\.cookie/, type: 'cookie', description: 'Cookie value' },
  { pattern: /\.innerHTML|\.outerHTML/, type: 'dom', description: 'DOM content' },
];

/**
 * Built-in taint sinks
 */
const DEFAULT_SINKS: TaintSinkDef[] = [
  { pattern: /eval\(|Function\(|setTimeout\(|setInterval\(/, type: 'code-execution', vulnerabilityType: 'injection', severity: 'critical' },
  { pattern: /\.innerHTML\s*=|\.outerHTML\s*=|document\.write/, type: 'xss', vulnerabilityType: 'injection', severity: 'high' },
  { pattern: /exec\(|spawn\(|execSync\(|spawnSync\(/, type: 'command-injection', vulnerabilityType: 'injection', severity: 'critical' },
  { pattern: /\.query\(|\.execute\(|\.raw\(/, type: 'sql-injection', vulnerabilityType: 'injection', severity: 'critical' },
  { pattern: /fs\.write|writeFile|writeFileSync/, type: 'file-write', vulnerabilityType: 'data-leakage', severity: 'high' },
  { pattern: /res\.send\(|res\.json\(|response\.write/, type: 'response', vulnerabilityType: 'data-leakage', severity: 'medium' },
  { pattern: /console\.log\(|print\(|logger\.\w+\(/, type: 'logging', vulnerabilityType: 'data-leakage', severity: 'low' },
  { pattern: /redirect\(|navigate\(|window\.location\s*=/, type: 'redirect', vulnerabilityType: 'injection', severity: 'medium' },
];

/**
 * Built-in sanitizers
 */
const DEFAULT_SANITIZERS: SanitizerDef[] = [
  { pattern: /escape|sanitize|encode|clean|filter/, sanitizes: ['xss', 'sql-injection', 'command-injection'] },
  { pattern: /parseInt|parseFloat|Number\(|String\(/, sanitizes: ['sql-injection', 'command-injection'] },
  { pattern: /validate|verify|check/, sanitizes: ['user-input'] },
  { pattern: /DOMPurify|xss|bleach/, sanitizes: ['xss'] },
  { pattern: /parameterized|prepared|placeholder/, sanitizes: ['sql-injection'] },
];

/**
 * Interprocedural Analyzer
 * @trace DES-SEC2-SAST-004
 */
export class InterproceduralAnalyzer {
  private options: InterproceduralOptions;
  private sources: TaintSourceDef[];
  private sinks: TaintSinkDef[];
  private sanitizers: SanitizerDef[];
  private callGraph: CallGraph;
  private visitedNodes: Set<string>;
  private analysisStartTime: number;

  constructor(options: InterproceduralOptions = {}) {
    this.options = {
      maxDepth: options.maxDepth ?? 20,
      timeout: options.timeout ?? 30000,
      maxNodes: options.maxNodes ?? 10000,
      contextSensitive: options.contextSensitive ?? true,
      trackImplicitFlows: options.trackImplicitFlows ?? false,
    };
    
    this.sources = [...DEFAULT_SOURCES, ...(options.customSources ?? [])];
    this.sinks = [...DEFAULT_SINKS, ...(options.customSinks ?? [])];
    this.sanitizers = [...DEFAULT_SANITIZERS, ...(options.customSanitizers ?? [])];
    
    this.callGraph = { nodes: [], edges: [], entryPoints: [], sinks: [] };
    this.visitedNodes = new Set();
    this.analysisStartTime = 0;
  }

  /**
   * Analyze code for interprocedural vulnerabilities
   * @trace REQ-SEC2-SAST-004
   */
  async analyze(code: string, filePath: string): Promise<InterproceduralResult> {
    this.analysisStartTime = Date.now();
    this.visitedNodes.clear();
    
    // Build call graph
    this.callGraph = this.buildCallGraph(code, filePath);
    
    // Track data flow across functions
    const dataFlowPaths = this.trackDataFlow(code, filePath);
    
    // Detect vulnerabilities
    const vulnerabilities = this.detectVulnerabilities(dataFlowPaths, filePath);
    
    const executionTime = Date.now() - this.analysisStartTime;
    
    return {
      vulnerabilities,
      callGraph: this.callGraph,
      dataFlowPaths,
      analysisMetrics: {
        totalFunctions: this.callGraph.nodes.length,
        totalCallSites: this.callGraph.edges.length,
        analysisDepth: this.options.maxDepth ?? 20,
        executionTime,
        nodesVisited: this.visitedNodes.size,
        pathsAnalyzed: dataFlowPaths.length,
      },
    };
  }

  /**
   * Build call graph from code
   */
  buildCallGraph(code: string, filePath: string): CallGraph {
    const nodes: CallGraphNode[] = [];
    const edges: CallGraphEdge[] = [];
    const entryPoints: string[] = [];
    const sinks: string[] = [];
    
    const lines = code.split('\n');
    
    // Extract function declarations
    const functionPatterns = [
      // Named function
      /(?:export\s+)?(?:async\s+)?function\s+(\w+)\s*\(([^)]*)\)/g,
      // Arrow function assigned to variable
      /(?:export\s+)?(?:const|let|var)\s+(\w+)\s*=\s*(?:async\s*)?\(([^)]*)\)\s*=>/g,
      // Method definition
      /(?:async\s+)?(\w+)\s*\(([^)]*)\)\s*{/g,
    ];
    
    for (const pattern of functionPatterns) {
      let match: RegExpExecArray | null;
      const globalPattern = new RegExp(pattern.source, 'gm');
      
      while ((match = globalPattern.exec(code)) !== null) {
        if (this.shouldStopAnalysis()) break;
        
        const name = match[1];
        const params = match[2];
        const line = code.substring(0, match.index).split('\n').length;
        const isAsync = match[0].includes('async');
        
        // Skip common keywords
        if (['if', 'while', 'for', 'switch', 'catch', 'function'].includes(name)) {
          continue;
        }
        
        const nodeId = `${filePath}:${name}:${line}`;
        
        const node: CallGraphNode = {
          id: nodeId,
          name,
          file: filePath,
          line,
          type: this.determineNodeType(code, match.index),
          isAsync,
          parameters: this.parseParameters(params),
          modifiers: this.extractModifiers(code, match.index),
        };
        
        nodes.push(node);
        this.visitedNodes.add(nodeId);
        
        // Check if this is an entry point
        if (this.isEntryPoint(name, code, match.index)) {
          entryPoints.push(nodeId);
        }
        
        // Check if this is a sink
        if (this.isSinkFunction(name)) {
          sinks.push(nodeId);
        }
      }
    }
    
    // Find call edges
    for (const node of nodes) {
      if (this.shouldStopAnalysis()) break;
      
      const functionBody = this.extractFunctionBody(code, node.line);
      const callMatches = functionBody.matchAll(/(\w+)\s*\(/g);
      
      for (const callMatch of callMatches) {
        const calledName = callMatch[0].replace(/\s*\($/, '');
        
        // Skip common keywords and built-ins
        if (['if', 'while', 'for', 'switch', 'catch', 'return', 'console', 'Math'].includes(calledName)) {
          continue;
        }
        
        // Find target node
        const targetNode = nodes.find(n => n.name === calledName);
        
        if (targetNode) {
          const callLine = node.line + functionBody.substring(0, callMatch.index).split('\n').length - 1;
          
          edges.push({
            source: node.id,
            target: targetNode.id,
            callSite: {
              file: filePath,
              startLine: callLine,
              endLine: callLine,
              startColumn: 0,
              endColumn: lines[callLine - 1]?.length ?? 0,
            },
            callType: this.determineCallType(functionBody, callMatch.index ?? 0),
            arguments: this.parseArguments(functionBody, callMatch.index ?? 0),
          });
        }
      }
    }
    
    return { nodes, edges, entryPoints, sinks };
  }

  /**
   * Track data flow across functions
   */
  trackDataFlow(code: string, filePath: string): DataFlowPath[] {
    const paths: DataFlowPath[] = [];
    const lines = code.split('\n');
    
    // Find all taint sources
    const sourceNodes = this.findTaintSources(code, filePath, lines);
    
    // Find all taint sinks
    const sinkNodes = this.findTaintSinks(code, filePath, lines);
    
    // For each source, trace flow to sinks
    for (const source of sourceNodes) {
      if (this.shouldStopAnalysis()) break;
      
      const reachableSinks = this.traceFlowToSinks(source, sinkNodes, code, filePath, lines);
      
      for (const sink of reachableSinks) {
        const intermediateNodes = this.findIntermediateNodes(source, sink, code, filePath, lines);
        const sanitizationPoint = this.findSanitizationPoint(intermediateNodes);
        
        paths.push({
          id: `flow-${source.id}-${sink.id}`,
          source,
          sink,
          intermediateNodes,
          taintType: source.taintState,
          confidence: this.calculatePathConfidence(source, sink, intermediateNodes, sanitizationPoint),
          isSanitized: sanitizationPoint !== undefined,
          sanitizationPoint,
        });
      }
    }
    
    return paths;
  }

  /**
   * Detect vulnerabilities from data flow paths
   */
  private detectVulnerabilities(
    paths: DataFlowPath[],
    _filePath: string
  ): InterproceduralVulnerability[] {
    const vulnerabilities: InterproceduralVulnerability[] = [];
    
    for (const path of paths) {
      // Skip sanitized paths
      if (path.isSanitized) continue;
      
      // Find matching sink definition
      const sinkDef = this.sinks.find(s => s.pattern.test(path.sink.expression));
      if (!sinkDef) continue;
      
      vulnerabilities.push({
        id: `IPA-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
        type: sinkDef.vulnerabilityType as InterproceduralVulnerability['type'],
        severity: sinkDef.severity,
        entryPoint: path.source.location,
        sinkPoint: path.sink.location,
        dataFlowPath: path,
        description: this.generateDescription(path, sinkDef),
        recommendation: this.generateRecommendation(path, sinkDef),
        confidence: path.confidence,
      });
    }
    
    return vulnerabilities;
  }

  /**
   * Find taint sources in code
   */
  private findTaintSources(code: string, filePath: string, lines: string[]): DataFlowNode[] {
    const nodes: DataFlowNode[] = [];
    
    for (const source of this.sources) {
      let match: RegExpExecArray | null;
      const globalPattern = new RegExp(source.pattern.source, 'gm');
      
      while ((match = globalPattern.exec(code)) !== null) {
        const line = code.substring(0, match.index).split('\n').length;
        
        nodes.push({
          id: `src-${line}-${nodes.length}`,
          expression: match[0],
          location: {
            file: filePath,
            startLine: line,
            endLine: line,
            startColumn: 0,
            endColumn: lines[line - 1]?.length ?? 0,
          },
          nodeType: 'source',
          taintState: 'tainted',
        });
      }
    }
    
    return nodes;
  }

  /**
   * Find taint sinks in code
   */
  private findTaintSinks(code: string, filePath: string, lines: string[]): DataFlowNode[] {
    const nodes: DataFlowNode[] = [];
    
    for (const sink of this.sinks) {
      let match: RegExpExecArray | null;
      const globalPattern = new RegExp(sink.pattern.source, 'gm');
      
      while ((match = globalPattern.exec(code)) !== null) {
        const line = code.substring(0, match.index).split('\n').length;
        
        nodes.push({
          id: `sink-${line}-${nodes.length}`,
          expression: match[0],
          location: {
            file: filePath,
            startLine: line,
            endLine: line,
            startColumn: 0,
            endColumn: lines[line - 1]?.length ?? 0,
          },
          nodeType: 'sink',
          taintState: 'unknown',
        });
      }
    }
    
    return nodes;
  }

  /**
   * Trace flow from source to sinks
   */
  private traceFlowToSinks(
    source: DataFlowNode,
    sinks: DataFlowNode[],
    _code: string,
    _filePath: string,
    lines: string[]
  ): DataFlowNode[] {
    const reachableSinks: DataFlowNode[] = [];
    
    // Extract variable name from source
    const sourceContext = lines[source.location.startLine - 1] ?? '';
    const varMatch = sourceContext.match(/(\w+)\s*=\s*.*$/);
    const sourceVar = varMatch?.[1];
    
    if (!sourceVar) return reachableSinks;
    
    // Check if source variable reaches any sink
    for (const sink of sinks) {
      const sinkLine = sink.location.startLine;
      
      // Simple reach analysis: check if variable is used between source and sink
      if (sinkLine >= source.location.startLine) {
        const codeBetween = lines.slice(source.location.startLine - 1, sinkLine).join('\n');
        
        // Check if the source variable (or derivatives) is used at the sink
        if (codeBetween.includes(sourceVar) && lines[sinkLine - 1]?.includes(sourceVar)) {
          reachableSinks.push(sink);
        }
      }
    }
    
    return reachableSinks;
  }

  /**
   * Find intermediate nodes between source and sink
   */
  private findIntermediateNodes(
    source: DataFlowNode,
    sink: DataFlowNode,
    _code: string,
    filePath: string,
    lines: string[]
  ): DataFlowNode[] {
    const nodes: DataFlowNode[] = [];
    const startLine = source.location.startLine;
    const endLine = sink.location.startLine;
    
    for (let i = startLine; i < endLine; i++) {
      const line = lines[i - 1];
      if (!line) continue;
      
      // Check for transformations
      if (line.match(/=.*\+|=.*\.|=.*\[/)) {
        nodes.push({
          id: `transform-${i}`,
          expression: line.trim(),
          location: {
            file: filePath,
            startLine: i,
            endLine: i,
            startColumn: 0,
            endColumn: line.length,
          },
          nodeType: 'transform',
          taintState: 'tainted',
        });
      }
      
      // Check for sanitizers
      for (const sanitizer of this.sanitizers) {
        if (sanitizer.pattern.test(line)) {
          nodes.push({
            id: `sanitizer-${i}`,
            expression: line.trim(),
            location: {
              file: filePath,
              startLine: i,
              endLine: i,
              startColumn: 0,
              endColumn: line.length,
            },
            nodeType: 'sanitizer',
            taintState: 'sanitized',
          });
        }
      }
    }
    
    return nodes;
  }

  /**
   * Find sanitization point in intermediate nodes
   */
  private findSanitizationPoint(nodes: DataFlowNode[]): DataFlowNode | undefined {
    return nodes.find(n => n.nodeType === 'sanitizer');
  }

  /**
   * Calculate path confidence
   */
  private calculatePathConfidence(
    source: DataFlowNode,
    sink: DataFlowNode,
    intermediate: DataFlowNode[],
    sanitizer?: DataFlowNode
  ): number {
    let confidence = 0.7;
    
    // Reduce confidence if there's a potential sanitizer
    if (sanitizer) {
      confidence -= 0.3;
    }
    
    // Increase confidence for direct paths (fewer intermediate nodes)
    if (intermediate.length <= 2) {
      confidence += 0.2;
    } else if (intermediate.length > 5) {
      confidence -= 0.1;
    }
    
    // Increase confidence for closer source and sink
    const distance = Math.abs(sink.location.startLine - source.location.startLine);
    if (distance <= 10) {
      confidence += 0.1;
    }
    
    return Math.min(Math.max(confidence, 0), 1);
  }

  /**
   * Check if analysis should stop
   */
  private shouldStopAnalysis(): boolean {
    const elapsed = Date.now() - this.analysisStartTime;
    const timeout = this.options.timeout ?? 30000;
    const maxNodes = this.options.maxNodes ?? 10000;
    
    return elapsed > timeout || this.visitedNodes.size > maxNodes;
  }

  /**
   * Determine node type
   */
  private determineNodeType(code: string, index: number): CallGraphNode['type'] {
    const beforeMatch = code.substring(Math.max(0, index - 50), index);
    
    if (beforeMatch.includes('constructor')) return 'constructor';
    if (beforeMatch.match(/\.\w+\s*=/)) return 'method';
    if (beforeMatch.match(/=>\s*$/)) return 'callback';
    return 'function';
  }

  /**
   * Parse function parameters
   */
  private parseParameters(params: string): ParameterInfo[] {
    if (!params.trim()) return [];
    
    return params.split(',').map((param, index) => {
      const trimmed = param.trim();
      const nameMatch = trimmed.match(/^(\w+)/);
      
      return {
        name: nameMatch?.[1] ?? `arg${index}`,
        index,
        isTainted: false,
      };
    });
  }

  /**
   * Extract function modifiers
   */
  private extractModifiers(code: string, index: number): string[] {
    const modifiers: string[] = [];
    const beforeMatch = code.substring(Math.max(0, index - 30), index);
    
    if (beforeMatch.includes('export')) modifiers.push('export');
    if (beforeMatch.includes('async')) modifiers.push('async');
    if (beforeMatch.includes('static')) modifiers.push('static');
    if (beforeMatch.includes('private')) modifiers.push('private');
    if (beforeMatch.includes('public')) modifiers.push('public');
    
    return modifiers;
  }

  /**
   * Check if function is an entry point
   */
  private isEntryPoint(_name: string, code: string, index: number): boolean {
    const entryPointPatterns = [
      /app\.(get|post|put|delete|patch)\s*\(/,
      /router\.(get|post|put|delete|patch)\s*\(/,
      /export\s+default/,
      /module\.exports/,
      /addEventListener/,
    ];
    
    const context = code.substring(Math.max(0, index - 100), index);
    return entryPointPatterns.some(p => p.test(context));
  }

  /**
   * Check if function is a sink
   */
  private isSinkFunction(name: string): boolean {
    const sinkFunctions = ['eval', 'exec', 'query', 'execute', 'write', 'send'];
    return sinkFunctions.includes(name.toLowerCase());
  }

  /**
   * Extract function body
   */
  private extractFunctionBody(code: string, startLine: number): string {
    const lines = code.split('\n');
    const startIndex = lines.slice(0, startLine - 1).join('\n').length + 1;
    
    let depth = 0;
    let inString = false;
    let stringChar = '';
    let bodyStart = -1;
    
    for (let i = startIndex; i < code.length; i++) {
      const char = code[i];
      const prevChar = code[i - 1];
      
      if (!inString) {
        if (char === '"' || char === "'" || char === '`') {
          inString = true;
          stringChar = char;
        } else if (char === '{') {
          if (depth === 0) bodyStart = i;
          depth++;
        } else if (char === '}') {
          depth--;
          if (depth === 0) {
            return code.substring(bodyStart, i + 1);
          }
        }
      } else {
        if (char === stringChar && prevChar !== '\\') {
          inString = false;
        }
      }
    }
    
    return code.substring(startIndex, Math.min(startIndex + 1000, code.length));
  }

  /**
   * Determine call type
   */
  private determineCallType(body: string, index: number): CallGraphEdge['callType'] {
    const before = body.substring(Math.max(0, index - 30), index);
    
    if (before.includes('.')) return 'virtual';
    if (before.includes('await') || before.includes('then')) return 'callback';
    return 'direct';
  }

  /**
   * Parse arguments at call site
   */
  private parseArguments(body: string, index: number): ArgumentBinding[] {
    const bindings: ArgumentBinding[] = [];
    
    // Find the opening parenthesis
    let parenStart = body.indexOf('(', index);
    if (parenStart === -1) return bindings;
    
    // Extract argument string
    let depth = 1;
    let argEnd = parenStart + 1;
    
    for (let i = parenStart + 1; i < body.length && depth > 0; i++) {
      if (body[i] === '(') depth++;
      if (body[i] === ')') depth--;
      argEnd = i;
    }
    
    const argsStr = body.substring(parenStart + 1, argEnd);
    const args = argsStr.split(',').map(a => a.trim()).filter(a => a);
    
    for (let i = 0; i < args.length; i++) {
      const isTainted = this.sources.some(s => s.pattern.test(args[i]));
      
      bindings.push({
        parameterIndex: i,
        expression: args[i],
        isTainted,
        taintSource: isTainted ? this.sources.find(s => s.pattern.test(args[i]))?.type : undefined,
      });
    }
    
    return bindings;
  }

  /**
   * Generate vulnerability description
   */
  private generateDescription(path: DataFlowPath, sinkDef: TaintSinkDef): string {
    const distance = path.sink.location.startLine - path.source.location.startLine;
    const hops = path.intermediateNodes.length;
    
    return `Untrusted data from ${path.source.expression} flows to ${sinkDef.type} sink ` +
      `(${path.sink.expression}) through ${hops} intermediate steps across ${distance} lines`;
  }

  /**
   * Generate recommendation
   */
  private generateRecommendation(_path: DataFlowPath, sinkDef: TaintSinkDef): string {
    const recommendations: Record<string, string> = {
      'code-execution': 'Never use eval() or Function() with untrusted input. Use safe alternatives.',
      'xss': 'Sanitize output using DOMPurify or escape HTML entities before rendering.',
      'command-injection': 'Use parameterized commands or exec with explicit argument arrays.',
      'sql-injection': 'Use parameterized queries or prepared statements.',
      'file-write': 'Validate file paths and restrict write locations.',
      'response': 'Filter sensitive data before sending responses.',
      'logging': 'Redact sensitive information before logging.',
      'redirect': 'Validate redirect URLs against a whitelist.',
    };
    
    return recommendations[sinkDef.type] ?? 'Validate and sanitize input before use.';
  }

  /**
   * Convert results to standard vulnerability format
   */
  toVulnerabilities(result: InterproceduralResult): Vulnerability[] {
    return result.vulnerabilities.map(vuln => ({
      id: vuln.id,
      type: vuln.type as Vulnerability['type'],
      severity: vuln.severity,
      cwes: this.getCWEsForType(vuln.type),
      owasp: this.getOWASPForType(vuln.type) as OWASPCategory[],
      location: vuln.sinkPoint,
      description: vuln.description,
      recommendation: vuln.recommendation,
      confidence: vuln.confidence,
      ruleId: 'IPA',
      codeSnippet: '',
      detectedAt: new Date(),
    }));
  }

  /**
   * Get CWE IDs for vulnerability type
   */
  private getCWEsForType(type: string): string[] {
    const cweMap: Record<string, string[]> = {
      'taint-propagation': ['CWE-20', 'CWE-79'],
      'privilege-escalation': ['CWE-269', 'CWE-250'],
      'data-leakage': ['CWE-200', 'CWE-532'],
      'injection': ['CWE-74', 'CWE-89', 'CWE-78'],
    };
    return cweMap[type] ?? ['CWE-Unknown'];
  }

  /**
   * Get OWASP IDs for vulnerability type
   */
  private getOWASPForType(type: string): OWASPCategory[] {
    const owaspMap: Record<string, OWASPCategory[]> = {
      'taint-propagation': ['A03:2021'],
      'privilege-escalation': ['A01:2021'],
      'data-leakage': ['A01:2021', 'A09:2021'],
      'injection': ['A03:2021'],
    };
    return owaspMap[type] ?? ['A00:Unknown'];
  }
}

/**
 * Create interprocedural analyzer instance
 */
export function createInterproceduralAnalyzer(
  options?: InterproceduralOptions
): InterproceduralAnalyzer {
  return new InterproceduralAnalyzer(options);
}
