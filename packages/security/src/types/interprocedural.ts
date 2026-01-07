/**
 * @fileoverview Interprocedural analysis type definitions
 * @module @nahisaho/musubix-security/types/interprocedural
 * @trace DES-SEC2-SAST-004, REQ-SEC2-SAST-004
 */

import type { SourceLocation } from './vulnerability.js';

/**
 * Data flow operation type
 */
export type DataFlowOperation = 
  | 'define'    // Variable definition
  | 'use'       // Variable usage
  | 'call'      // Function call (parameter passing)
  | 'return';   // Return value

/**
 * Parameter information
 */
export interface ParameterInfo {
  /** Parameter name */
  name: string;
  
  /** Parameter type (if available) */
  type?: string;
  
  /** Whether parameter is tainted */
  isTainted?: boolean;
  
  /** Index in parameter list */
  index: number;
}

/**
 * Call graph node representing a function
 * @trace REQ-SEC2-SAST-004
 */
export interface CallGraphNode {
  /** Unique node identifier */
  id: string;
  
  /** Function name */
  name: string;
  
  /** Module/file path */
  module: string;
  
  /** Source code location */
  location: SourceLocation;
  
  /** Function parameters */
  parameters: ParameterInfo[];
  
  /** Return type (if available) */
  returnType?: string;
  
  /** Whether function is exported */
  isExported?: boolean;
  
  /** Whether function is async */
  isAsync?: boolean;
  
  /** Complexity score */
  complexity?: number;
}

/**
 * Argument mapping between caller and callee
 */
export interface ArgumentMapping {
  /** Expression passed by caller */
  callerExpression: string;
  
  /** Parameter name in callee */
  calleeParameter: string;
  
  /** Whether argument may be tainted */
  maybeTainted?: boolean;
}

/**
 * Call graph edge representing a function call
 */
export interface CallGraphEdge {
  /** Caller function ID */
  caller: string;
  
  /** Callee function ID */
  callee: string;
  
  /** Call site location */
  location: SourceLocation;
  
  /** Argument mappings */
  argumentMapping: ArgumentMapping[];
  
  /** Call type */
  callType?: 'direct' | 'indirect' | 'callback';
}

/**
 * Call graph structure
 * @trace REQ-SEC2-SAST-004
 */
export interface CallGraph {
  /** All function nodes */
  nodes: CallGraphNode[];
  
  /** All call edges */
  edges: CallGraphEdge[];
  
  /** Root nodes (entry points) */
  roots: string[];
  
  /** Leaf nodes (terminal functions) */
  leaves: string[];
}

/**
 * Cycle information for recursive calls
 */
export interface CycleInfo {
  /** Nodes involved in the cycle */
  nodes: string[];
  
  /** Entry point of the cycle */
  entryPoint: string;
  
  /** Cycle length */
  length: number;
}

/**
 * Data flow step across function boundaries
 */
export interface DataFlowStep {
  /** Source location */
  location: SourceLocation;
  
  /** Expression at this step */
  expression: string;
  
  /** Function containing this step */
  functionId: string;
  
  /** Operation type */
  operation: DataFlowOperation;
  
  /** Step index in path */
  index: number;
}

/**
 * Data flow path tracking variable across functions
 */
export interface DataFlowPath {
  /** Variable being tracked */
  variable: string;
  
  /** Steps in the data flow */
  steps: DataFlowStep[];
  
  /** Whether path crosses function boundaries */
  crossesBoundary: boolean;
  
  /** Functions involved in the path */
  functionsInvolved: string[];
  
  /** Whether path is tainted */
  isTainted?: boolean;
}

/**
 * Interprocedural analysis options
 */
export interface InterproceduralOptions {
  /** Maximum call depth to analyze */
  maxDepth?: number;
  
  /** Include external library calls */
  includeExternalCalls?: boolean;
  
  /** Detect cycles */
  detectCycles?: boolean;
  
  /** Track data flow */
  trackDataFlow?: boolean;
  
  /** Entry points (if not specified, auto-detect) */
  entryPoints?: string[];
  
  /** Timeout per file in milliseconds */
  timeout?: number;
}

/**
 * Interprocedural analysis result
 * @trace REQ-SEC2-SAST-004
 */
export interface InterproceduralResult {
  /** Generated call graph */
  callGraph: CallGraph;
  
  /** Detected data flow paths */
  dataFlows: DataFlowPath[];
  
  /** Detected recursive cycles */
  cycles: CycleInfo[];
  
  /** Whether max depth was reached */
  maxDepthReached: boolean;
  
  /** Analysis statistics */
  stats: {
    totalFunctions: number;
    totalCalls: number;
    taintedPaths: number;
    cyclesDetected: number;
  };
  
  /** Analysis duration in milliseconds */
  analysisTime: number;
}

/**
 * Interprocedural analyzer interface
 * @trace DES-SEC2-SAST-004
 */
export interface IInterproceduralAnalyzer {
  /**
   * Build call graph for given files
   */
  buildCallGraph(
    files: string[],
    options?: InterproceduralOptions
  ): Promise<CallGraph>;
  
  /**
   * Analyze data flow across function boundaries
   */
  analyzeDataFlow(
    callGraph: CallGraph,
    options?: InterproceduralOptions
  ): Promise<DataFlowPath[]>;
  
  /**
   * Detect cycles in call graph
   */
  detectCycles(callGraph: CallGraph): CycleInfo[];
  
  /**
   * Get callers of a function
   */
  getCallers(callGraph: CallGraph, functionId: string): CallGraphNode[];
  
  /**
   * Get callees of a function
   */
  getCallees(callGraph: CallGraph, functionId: string): CallGraphNode[];
  
  /**
   * Find path between two functions
   */
  findPath(
    callGraph: CallGraph,
    fromId: string,
    toId: string
  ): CallGraphNode[] | null;
  
  /**
   * Full interprocedural analysis
   */
  analyze(
    files: string[],
    options?: InterproceduralOptions
  ): Promise<InterproceduralResult>;
}
