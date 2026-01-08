/**
 * @fileoverview Taint Propagator - Track taint flow across function boundaries
 * @module @nahisaho/musubix-security/analysis/interprocedural/taint-propagator
 * @trace REQ-SEC-001 (EARS: WHEN tainted data flows through function calls, THE system SHALL track it)
 */

import type {
  CallGraph,
  CallGraphNode,
  CallGraphEdge,
} from './call-graph-builder.js';
import type { TaintSinkCategory } from '../../types/taint.js';
import type { SourceDefinition } from '../sources/types.js';
import type { SinkDefinition } from '../sinks/types.js';
import type { SanitizerDefinition } from '../sanitizers/types.js';

/**
 * Simplified source info for findings
 */
export interface TaintSourceInfo {
  id: string;
  name: string;
  location: {
    file: string;
    line: number;
    column: number;
  };
  type: string;
  confidence: number;
}

/**
 * Simplified sink info for findings
 */
export interface TaintSinkInfo {
  id: string;
  name: string;
  location: {
    file: string;
    line: number;
    column: number;
  };
  category: TaintSinkCategory;
  confidence: number;
}

/**
 * Taint state for a variable/parameter
 */
export interface TaintState {
  /** Whether the value is tainted */
  isTainted: boolean;
  /** Source of taint (if tainted) */
  source?: TaintSourceInfo;
  /** Confidence level (0-1) */
  confidence: number;
  /** Sanitizers applied */
  sanitizers: string[];
  /** Categories this taint affects */
  affectedCategories: TaintSinkCategory[];
}

/**
 * Taint context within a function
 */
export interface FunctionTaintContext {
  /** Node ID */
  nodeId: string;
  /** Parameter taint states (by index) */
  parameterTaints: Map<number, TaintState>;
  /** Local variable taint states */
  localTaints: Map<string, TaintState>;
  /** Return value taint state */
  returnTaint?: TaintState;
  /** Whether function has side effects */
  hasSideEffects: boolean;
}

/**
 * Taint flow edge - represents taint flowing from one location to another
 */
export interface TaintFlowEdge {
  /** Unique ID */
  id: string;
  /** Source location */
  from: TaintLocation;
  /** Destination location */
  to: TaintLocation;
  /** Type of flow */
  flowType: TaintFlowType;
  /** Associated call edge (if interprocedural) */
  callEdge?: CallGraphEdge;
  /** Sanitizers in path */
  sanitizersApplied: string[];
  /** Confidence (0-1) */
  confidence: number;
}

/**
 * Location of taint
 */
export interface TaintLocation {
  /** Function node ID */
  nodeId: string;
  /** Variable name or parameter index */
  identifier: string;
  /** Line number */
  line: number;
  /** Column number */
  column: number;
  /** File path */
  filePath: string;
}

/**
 * Type of taint flow
 */
export type TaintFlowType =
  | 'assignment'      // Direct assignment
  | 'parameter'       // Passed as function parameter
  | 'return'          // Returned from function
  | 'property-access' // Property access
  | 'method-call'     // Method call return
  | 'callback'        // Callback invocation
  | 'implicit';       // Implicit flow (control dependency)

/**
 * Taint finding - vulnerability detected
 */
export interface TaintFinding {
  /** Unique ID */
  id: string;
  /** Severity level */
  severity: 'critical' | 'high' | 'medium' | 'low' | 'info';
  /** Vulnerability title */
  title: string;
  /** Description */
  description: string;
  /** CWE ID */
  cwe?: string;
  /** Source of taint */
  source: TaintSourceInfo;
  /** Sink where taint flows */
  sink: TaintSinkInfo;
  /** Complete taint flow path */
  flowPath: TaintFlowEdge[];
  /** Sanitizers in path (may be incomplete) */
  sanitizersInPath: string[];
  /** Whether sanitization is complete */
  sanitizationComplete: boolean;
  /** Confidence (0-1) */
  confidence: number;
  /** Suggested remediation */
  remediation?: string;
}

/**
 * Summary of taint analysis results
 */
export interface TaintSummary {
  /** Node ID */
  nodeId: string;
  /** Parameters that propagate taint to return */
  taintPropagatingParams: number[];
  /** Whether function sanitizes input */
  isSanitizer: boolean;
  /** Categories sanitized */
  sanitizesCategories: TaintSinkCategory[];
  /** Whether function is a sink */
  isSink: boolean;
  /** Sink category if applicable */
  sinkCategory?: TaintSinkCategory;
  /** Whether function is a source */
  isSource: boolean;
  /** Source type if applicable */
  sourceType?: string;
}

/**
 * Options for taint propagation
 */
export interface TaintPropagatorOptions {
  /** Maximum call depth to analyze */
  maxDepth?: number;
  /** Track implicit flows (control dependencies) */
  trackImplicitFlows?: boolean;
  /** Minimum confidence threshold */
  minConfidence?: number;
  /** Custom sources */
  customSources?: SourceDefinition[];
  /** Custom sinks */
  customSinks?: SinkDefinition[];
  /** Custom sanitizers */
  customSanitizers?: SanitizerDefinition[];
}

/**
 * Taint Propagator - Performs interprocedural taint analysis
 * @trace REQ-SEC-001
 */
export class TaintPropagator {
  private options: Required<TaintPropagatorOptions>;
  private functionSummaries: Map<string, TaintSummary> = new Map();
  private sources: SourceDefinition[];
  private sinks: SinkDefinition[];
  private sanitizers: SanitizerDefinition[];

  constructor(
    sources: SourceDefinition[],
    sinks: SinkDefinition[],
    sanitizers: SanitizerDefinition[],
    options: TaintPropagatorOptions = {}
  ) {
    this.sources = sources;
    this.sinks = sinks;
    this.sanitizers = sanitizers;
    this.options = {
      maxDepth: options.maxDepth ?? 10,
      trackImplicitFlows: options.trackImplicitFlows ?? false,
      minConfidence: options.minConfidence ?? 0.5,
      customSources: options.customSources ?? [],
      customSinks: options.customSinks ?? [],
      customSanitizers: options.customSanitizers ?? [],
    };

    // Merge custom definitions
    this.sources = [...this.sources, ...this.options.customSources];
    this.sinks = [...this.sinks, ...this.options.customSinks];
    this.sanitizers = [...this.sanitizers, ...this.options.customSanitizers];
  }

  /**
   * Analyze a call graph for taint vulnerabilities
   */
  analyze(
    callGraph: CallGraph,
    sourceLocations: TaintLocation[],
    functionContexts?: Map<string, FunctionTaintContext>
  ): TaintFinding[] {
    const findings: TaintFinding[] = [];
    
    // Build function summaries
    this.buildFunctionSummaries(callGraph, functionContexts);

    // For each source, trace taint flow to potential sinks
    for (const sourceLocation of sourceLocations) {
      const taintFlows = this.traceTaintFlow(
        callGraph,
        sourceLocation,
        new Set<string>(),
        [],
        1.0,
        0
      );

      // Check each flow for sink vulnerabilities
      for (const flow of taintFlows) {
        const finding = this.checkForVulnerability(flow, sourceLocation);
        if (finding && finding.confidence >= this.options.minConfidence) {
          findings.push(finding);
        }
      }
    }

    return this.deduplicateFindings(findings);
  }

  /**
   * Build summaries of each function's taint behavior
   */
  private buildFunctionSummaries(
    callGraph: CallGraph,
    functionContexts?: Map<string, FunctionTaintContext>
  ): void {
    for (const [nodeId, node] of callGraph.nodes) {
      const summary = this.analyzeFunctionTaint(node, callGraph, functionContexts?.get(nodeId));
      this.functionSummaries.set(nodeId, summary);
    }
  }

  /**
   * Analyze a single function's taint behavior
   */
  private analyzeFunctionTaint(
    node: CallGraphNode,
    _callGraph: CallGraph,
    context?: FunctionTaintContext
  ): TaintSummary {
    const summary: TaintSummary = {
      nodeId: node.id,
      taintPropagatingParams: [],
      isSanitizer: false,
      sanitizesCategories: [],
      isSink: false,
      isSource: false,
    };

    // Check if function is a known source
    const matchedSource = this.sources.find((s) =>
      this.matchesFunctionName(node.name, s.name)
    );
    if (matchedSource) {
      summary.isSource = true;
      summary.sourceType = matchedSource.id;
    }

    // Check if function is a known sink
    for (const sink of this.sinks) {
      for (const pattern of sink.patterns) {
        const methods = pattern.method
          ? Array.isArray(pattern.method) ? pattern.method : [pattern.method]
          : [];
        const properties = pattern.property
          ? Array.isArray(pattern.property) ? pattern.property : [pattern.property]
          : [];
        
        const matchesMethod = methods.some((m) => this.matchesFunctionName(node.name, m));
        const matchesProperty = properties.some((p) => this.matchesFunctionName(node.name, p));
        
        if (matchesMethod || matchesProperty) {
          summary.isSink = true;
          summary.sinkCategory = sink.category;
          break;
        }
      }
    }

    // Check if function is a known sanitizer
    const matchedSanitizer = this.sanitizers.find((s) =>
      this.matchesFunctionName(node.name, s.name, s.aliases, s.namePattern)
    );
    if (matchedSanitizer) {
      summary.isSanitizer = true;
      summary.sanitizesCategories = matchedSanitizer.protects;
    }

    // If we have context, analyze parameter propagation
    if (context) {
      for (const [paramIdx, taintState] of context.parameterTaints) {
        if (context.returnTaint?.isTainted && taintState.isTainted) {
          summary.taintPropagatingParams.push(paramIdx);
        }
      }
    } else {
      // Without context, assume all parameters can propagate to return
      summary.taintPropagatingParams = node.parameters.map((_, i) => i);
    }

    return summary;
  }

  /**
   * Trace taint flow from a source location
   */
  private traceTaintFlow(
    callGraph: CallGraph,
    currentLocation: TaintLocation,
    visited: Set<string>,
    path: TaintFlowEdge[],
    confidence: number,
    depth: number
  ): TaintFlowEdge[][] {
    if (depth >= this.options.maxDepth) {
      return [path];
    }

    const visitKey = `${currentLocation.nodeId}:${currentLocation.identifier}`;
    if (visited.has(visitKey)) {
      return [path];
    }
    visited.add(visitKey);

    const results: TaintFlowEdge[][] = [];
    const summary = this.functionSummaries.get(currentLocation.nodeId);

    // If current location is a sink, record the path
    if (summary?.isSink) {
      results.push(path);
    }

    // Check outgoing calls from this function
    const outgoingEdges = callGraph.outgoingEdges.get(currentLocation.nodeId) ?? [];

    for (const edge of outgoingEdges) {
      // Check if tainted value is passed as argument
      const argIndex = this.findTaintedArgument(edge, currentLocation);
      if (argIndex === -1) continue;

      const calleeNode = callGraph.nodes.get(edge.calleeId);
      const calleeSummary = this.functionSummaries.get(edge.calleeId);
      if (!calleeNode || !calleeSummary) continue;

      // Create flow edge for parameter passing
      const paramFlowEdge: TaintFlowEdge = {
        id: `flow_${path.length}`,
        from: currentLocation,
        to: {
          nodeId: edge.calleeId,
          identifier: `param_${argIndex}`,
          line: edge.line,
          column: edge.column,
          filePath: edge.filePath,
        },
        flowType: 'parameter',
        callEdge: edge,
        sanitizersApplied: [],
        confidence: confidence * (edge.isConditional ? 0.8 : 1.0),
      };

      // Check for sanitization
      if (calleeSummary.isSanitizer) {
        paramFlowEdge.sanitizersApplied.push(calleeNode.name);
      }

      const newPath = [...path, paramFlowEdge];

      // If callee is a sink, record finding
      if (calleeSummary.isSink) {
        results.push(newPath);
      }

      // If callee propagates taint to return, continue tracing
      if (calleeSummary.taintPropagatingParams.includes(argIndex)) {
        const returnLocation: TaintLocation = {
          nodeId: edge.calleeId,
          identifier: 'return',
          line: edge.line,
          column: edge.column,
          filePath: edge.filePath,
        };

        const returnFlowEdge: TaintFlowEdge = {
          id: `flow_${newPath.length}`,
          from: paramFlowEdge.to,
          to: returnLocation,
          flowType: 'return',
          sanitizersApplied: calleeSummary.isSanitizer ? [calleeNode.name] : [],
          confidence: paramFlowEdge.confidence,
        };

        const recursiveFlows = this.traceTaintFlow(
          callGraph,
          returnLocation,
          new Set(visited),
          [...newPath, returnFlowEdge],
          returnFlowEdge.confidence,
          depth + 1
        );

        results.push(...recursiveFlows);
      }
    }

    // Also trace to callers if taint is in return value
    if (currentLocation.identifier === 'return') {
      const incomingEdges = callGraph.incomingEdges.get(currentLocation.nodeId) ?? [];
      
      for (const edge of incomingEdges) {
        const callerLocation: TaintLocation = {
          nodeId: edge.callerId,
          identifier: `call_result_${edge.line}`,
          line: edge.line,
          column: edge.column,
          filePath: edge.filePath,
        };

        const callResultEdge: TaintFlowEdge = {
          id: `flow_${path.length}`,
          from: currentLocation,
          to: callerLocation,
          flowType: 'method-call',
          callEdge: edge,
          sanitizersApplied: [],
          confidence: confidence * 0.9,
        };

        const recursiveFlows = this.traceTaintFlow(
          callGraph,
          callerLocation,
          new Set(visited),
          [...path, callResultEdge],
          callResultEdge.confidence,
          depth + 1
        );

        results.push(...recursiveFlows);
      }
    }

    if (results.length === 0) {
      results.push(path);
    }

    return results;
  }

  /**
   * Find if a tainted value is passed as an argument
   */
  private findTaintedArgument(
    edge: CallGraphEdge,
    taintedLocation: TaintLocation
  ): number {
    // Simple heuristic: check if any argument matches the tainted identifier
    for (let i = 0; i < edge.arguments.length; i++) {
      if (edge.arguments[i].includes(taintedLocation.identifier)) {
        return i;
      }
    }
    return -1;
  }

  /**
   * Check if a flow path represents a vulnerability
   */
  private checkForVulnerability(
    flowPath: TaintFlowEdge[],
    sourceLocation: TaintLocation
  ): TaintFinding | null {
    if (flowPath.length === 0) return null;

    const lastEdge = flowPath[flowPath.length - 1];
    const summary = this.functionSummaries.get(lastEdge.to.nodeId);
    
    if (!summary?.isSink) return null;

    // Collect all sanitizers in path
    const sanitizersInPath: string[] = [];
    for (const edge of flowPath) {
      sanitizersInPath.push(...edge.sanitizersApplied);
    }

    // Check if sanitization is complete for this sink category
    const sinkCategory = summary.sinkCategory!;
    const sanitizationComplete = this.checkSanitizationComplete(sanitizersInPath, sinkCategory);

    // Calculate overall confidence
    const confidence = flowPath.reduce((conf, edge) => conf * edge.confidence, 1.0);

    // Don't report if properly sanitized
    if (sanitizationComplete && confidence < 0.3) return null;

    const node = this.functionSummaries.get(lastEdge.to.nodeId);
    const sink = this.sinks.find((s) => s.category === sinkCategory);

    return {
      id: `finding_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      severity: this.calculateSeverity(sinkCategory, sanitizationComplete, confidence),
      title: `Potential ${sinkCategory} vulnerability`,
      description: this.generateDescription(sinkCategory, flowPath, sanitizersInPath),
      cwe: sink?.relatedCWE?.[0],
      source: {
        id: `src_${sourceLocation.nodeId}`,
        name: sourceLocation.identifier,
        location: {
          file: sourceLocation.filePath,
          line: sourceLocation.line,
          column: sourceLocation.column,
        },
        type: 'user-input',
        confidence: 1.0,
      },
      sink: {
        id: `sink_${lastEdge.to.nodeId}`,
        name: node?.nodeId ?? 'unknown',
        location: {
          file: lastEdge.to.filePath,
          line: lastEdge.to.line,
          column: lastEdge.to.column,
        },
        category: sinkCategory,
        confidence,
      },
      flowPath,
      sanitizersInPath,
      sanitizationComplete,
      confidence,
      remediation: this.generateRemediation(sinkCategory),
    };
  }

  /**
   * Check if sanitization is complete for a category
   */
  private checkSanitizationComplete(
    sanitizersApplied: string[],
    sinkCategory: TaintSinkCategory
  ): boolean {
    for (const sanitizerName of sanitizersApplied) {
      const sanitizer = this.sanitizers.find(
        (s) =>
          s.name === sanitizerName ||
          s.aliases?.includes(sanitizerName)
      );
      if (sanitizer?.protects.includes(sinkCategory) && sanitizer.completeness === 'complete') {
        return true;
      }
    }
    return false;
  }

  /**
   * Calculate severity based on sink category and sanitization
   */
  private calculateSeverity(
    category: TaintSinkCategory,
    sanitized: boolean,
    confidence: number
  ): 'critical' | 'high' | 'medium' | 'low' | 'info' {
    const baseSeverity: Record<TaintSinkCategory, number> = {
      'sql-query': 5,
      'nosql-query': 4,
      'command-exec': 5,
      'file-write': 4,
      'file-read': 3,
      'html-output': 3,
      'redirect': 2,
      'eval': 5,
      'deserialization': 4,
      'ldap-query': 4,
      'xpath-query': 3,
      'http-request': 3,
    };

    let score = baseSeverity[category] ?? 3;
    if (sanitized) score -= 2;
    score = score * confidence;

    if (score >= 4.5) return 'critical';
    if (score >= 3.5) return 'high';
    if (score >= 2.5) return 'medium';
    if (score >= 1.5) return 'low';
    return 'info';
  }

  /**
   * Generate vulnerability description
   */
  private generateDescription(
    category: TaintSinkCategory,
    flowPath: TaintFlowEdge[],
    sanitizers: string[]
  ): string {
    const descriptions: Record<TaintSinkCategory, string> = {
      'sql-query': 'User-controlled data flows to SQL query without proper sanitization',
      'nosql-query': 'User-controlled data flows to NoSQL query without proper sanitization',
      'command-exec': 'User-controlled data flows to OS command execution',
      'file-write': 'User-controlled data used in file path (potential path traversal)',
      'file-read': 'User-controlled data used in file path for reading (path traversal)',
      'html-output': 'User-controlled data rendered without escaping (XSS)',
      'redirect': 'User-controlled data used in redirect URL (open redirect)',
      'eval': 'User-controlled data flows to code evaluation (code injection)',
      'deserialization': 'User-controlled data passed to deserializer (RCE risk)',
      'ldap-query': 'User-controlled data flows to LDAP query (LDAP injection)',
      'xpath-query': 'User-controlled data flows to XPath query (XPath injection)',
      'http-request': 'User-controlled data used in outbound request URL (SSRF)',
    };

    let description = descriptions[category] ?? 'Potential security vulnerability detected';
    
    if (sanitizers.length > 0) {
      description += `. Partial sanitization applied: ${sanitizers.join(', ')}`;
    }

    description += `. Flow path length: ${flowPath.length} steps.`;

    return description;
  }

  /**
   * Generate remediation suggestion
   */
  private generateRemediation(category: TaintSinkCategory): string {
    const remediations: Record<TaintSinkCategory, string> = {
      'sql-query': 'Use parameterized queries or prepared statements instead of string concatenation',
      'nosql-query': 'Use parameterized queries and validate input types',
      'command-exec': 'Avoid shell commands with user input. If necessary, use allowlists and escape properly',
      'file-write': 'Validate and sanitize file paths. Use path.resolve() and check against allowed base directory',
      'file-read': 'Validate file paths against allowlist. Use path.basename() to prevent traversal',
      'html-output': 'Escape HTML entities or use framework auto-escaping. Consider DOMPurify for rich content',
      'redirect': 'Validate redirect URLs against allowlist of trusted domains',
      'eval': 'Avoid eval/Function with user input. Use safer alternatives like JSON.parse()',
      'deserialization': 'Avoid deserializing untrusted data. Use safe parsers and validate structure',
      'ldap-query': 'Escape LDAP special characters and use parameterized queries',
      'xpath-query': 'Escape XPath special characters or use parameterized queries',
      'http-request': 'Validate URLs against allowlist. Block internal IPs and private networks',
    };

    return remediations[category] ?? 'Review and sanitize user input before use';
  }

  /**
   * Deduplicate findings with same source and sink
   */
  private deduplicateFindings(findings: TaintFinding[]): TaintFinding[] {
    const seen = new Map<string, TaintFinding>();
    
    for (const finding of findings) {
      const key = `${finding.source.location.file}:${finding.source.location.line}:${finding.sink.location.file}:${finding.sink.location.line}`;
      const existing = seen.get(key);
      
      if (!existing || finding.confidence > existing.confidence) {
        seen.set(key, finding);
      }
    }
    
    return Array.from(seen.values());
  }

  /**
   * Match function name against pattern
   */
  private matchesFunctionName(
    actual: string,
    expected: string,
    aliases?: string[],
    pattern?: string
  ): boolean {
    if (actual === expected) return true;
    if (aliases?.includes(actual)) return true;
    if (pattern && new RegExp(pattern).test(actual)) return true;
    return false;
  }

  /**
   * Get function summary by node ID
   */
  getFunctionSummary(nodeId: string): TaintSummary | undefined {
    return this.functionSummaries.get(nodeId);
  }

  /**
   * Get all source functions
   */
  getSourceFunctions(): TaintSummary[] {
    return Array.from(this.functionSummaries.values()).filter((s) => s.isSource);
  }

  /**
   * Get all sink functions
   */
  getSinkFunctions(): TaintSummary[] {
    return Array.from(this.functionSummaries.values()).filter((s) => s.isSink);
  }

  /**
   * Get all sanitizer functions
   */
  getSanitizerFunctions(): TaintSummary[] {
    return Array.from(this.functionSummaries.values()).filter((s) => s.isSanitizer);
  }
}
