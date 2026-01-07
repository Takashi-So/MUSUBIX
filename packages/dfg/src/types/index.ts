/**
 * Type definitions for DFG/CFG analysis
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-dfg/types
 */

// ============================================================================
// Base Node Types
// ============================================================================

/**
 * Unique identifier for graph nodes
 */
export type NodeId = string;

/**
 * Unique identifier for graph edges
 */
export type EdgeId = string;

/**
 * Source location in code
 */
export interface SourceLocation {
  /** File path */
  filePath: string;
  /** Start line (1-based) */
  startLine: number;
  /** Start column (0-based) */
  startColumn: number;
  /** End line (1-based) */
  endLine: number;
  /** End column (0-based) */
  endColumn: number;
}

// ============================================================================
// Data Flow Graph Types
// ============================================================================

/**
 * Node types in Data Flow Graph
 */
export type DFGNodeType =
  | 'variable'
  | 'parameter'
  | 'literal'
  | 'expression'
  | 'call'
  | 'return'
  | 'assignment'
  | 'property-access'
  | 'array-access'
  | 'binary-operation'
  | 'unary-operation'
  | 'conditional'
  | 'function'
  | 'class'
  | 'import'
  | 'export';

/**
 * Edge types in Data Flow Graph
 */
export type DFGEdgeType =
  | 'def-use'        // Definition to use
  | 'use-def'        // Use to definition
  | 'data-dep'       // Data dependency
  | 'call-arg'       // Function call argument
  | 'call-return'    // Function return value
  | 'property'       // Property access
  | 'alias'          // Variable aliasing
  | 'phi'            // SSA phi node
  | 'control-dep';   // Control dependency

/**
 * Data type information for nodes
 */
export interface TypeInfo {
  /** Type name */
  name: string;
  /** Full qualified type */
  fullType: string;
  /** Is nullable */
  nullable: boolean;
  /** Generic type arguments */
  typeArguments?: TypeInfo[];
  /** Is array type */
  isArray: boolean;
  /** Is promise type */
  isPromise: boolean;
}

/**
 * Node in Data Flow Graph
 */
export interface DFGNode {
  /** Unique node identifier */
  id: NodeId;
  /** Node type */
  type: DFGNodeType;
  /** Node name/label */
  name: string;
  /** Source code location */
  location: SourceLocation;
  /** Type information */
  typeInfo?: TypeInfo;
  /** Scope path (e.g., 'module.class.method') */
  scope: string;
  /** Additional metadata */
  metadata: Record<string, unknown>;
}

/**
 * Edge in Data Flow Graph
 */
export interface DFGEdge {
  /** Unique edge identifier */
  id: EdgeId;
  /** Edge type */
  type: DFGEdgeType;
  /** Source node ID */
  source: NodeId;
  /** Target node ID */
  target: NodeId;
  /** Edge label/description */
  label?: string;
  /** Edge weight (for analysis) */
  weight: number;
  /** Additional metadata */
  metadata: Record<string, unknown>;
}

/**
 * Complete Data Flow Graph
 */
export interface DataFlowGraph {
  /** Graph identifier */
  id: string;
  /** Source file path */
  filePath: string;
  /** All nodes */
  nodes: Map<NodeId, DFGNode>;
  /** All edges */
  edges: Map<EdgeId, DFGEdge>;
  /** Entry points (function/module entries) */
  entryPoints: NodeId[];
  /** Exit points */
  exitPoints: NodeId[];
  /** Analysis metadata */
  metadata: {
    /** Analysis timestamp */
    analyzedAt: Date;
    /** Language version */
    languageVersion: string;
    /** Number of nodes */
    nodeCount: number;
    /** Number of edges */
    edgeCount: number;
  };
}

// ============================================================================
// Control Flow Graph Types
// ============================================================================

/**
 * Basic block types in Control Flow Graph
 */
export type CFGBlockType =
  | 'entry'
  | 'exit'
  | 'basic'
  | 'conditional'
  | 'loop-header'
  | 'loop-body'
  | 'loop-exit'
  | 'switch'
  | 'case'
  | 'try'
  | 'catch'
  | 'finally'
  | 'throw';

/**
 * Edge types in Control Flow Graph
 */
export type CFGEdgeType =
  | 'sequential'     // Normal sequential flow
  | 'conditional-true'
  | 'conditional-false'
  | 'loop-back'
  | 'loop-exit'
  | 'switch-case'
  | 'switch-default'
  | 'exception'
  | 'return'
  | 'break'
  | 'continue';

/**
 * Statement in a basic block
 */
export interface CFGStatement {
  /** Statement index in block */
  index: number;
  /** Statement type */
  type: string;
  /** Source code text */
  text: string;
  /** Source location */
  location: SourceLocation;
}

/**
 * Basic block in Control Flow Graph
 */
export interface CFGBlock {
  /** Unique block identifier */
  id: NodeId;
  /** Block type */
  type: CFGBlockType;
  /** Block label */
  label: string;
  /** Statements in this block */
  statements: CFGStatement[];
  /** Predecessor block IDs */
  predecessors: NodeId[];
  /** Successor block IDs */
  successors: NodeId[];
  /** Dominator block ID */
  dominator?: NodeId;
  /** Post-dominator block ID */
  postDominator?: NodeId;
  /** Loop depth */
  loopDepth: number;
  /** Source location */
  location: SourceLocation;
}

/**
 * Edge in Control Flow Graph
 */
export interface CFGEdge {
  /** Unique edge identifier */
  id: EdgeId;
  /** Edge type */
  type: CFGEdgeType;
  /** Source block ID */
  source: NodeId;
  /** Target block ID */
  target: NodeId;
  /** Condition expression (for conditional edges) */
  condition?: string;
  /** Is back edge (loop) */
  isBackEdge: boolean;
}

/**
 * Complete Control Flow Graph
 */
export interface ControlFlowGraph {
  /** Graph identifier */
  id: string;
  /** Function/method name */
  functionName: string;
  /** Source file path */
  filePath: string;
  /** Entry block ID */
  entryBlock: NodeId;
  /** Exit block IDs */
  exitBlocks: NodeId[];
  /** All blocks */
  blocks: Map<NodeId, CFGBlock>;
  /** All edges */
  edges: Map<EdgeId, CFGEdge>;
  /** Analysis metadata */
  metadata: {
    /** Analysis timestamp */
    analyzedAt: Date;
    /** Cyclomatic complexity */
    cyclomaticComplexity: number;
    /** Maximum loop depth */
    maxLoopDepth: number;
    /** Number of blocks */
    blockCount: number;
    /** Number of edges */
    edgeCount: number;
  };
}

// ============================================================================
// Analysis Options
// ============================================================================

/**
 * Options for DFG analysis
 */
export interface DFGAnalysisOptions {
  /** Include inter-procedural analysis */
  interprocedural: boolean;
  /** Track aliasing */
  trackAliasing: boolean;
  /** Include type information */
  includeTypes: boolean;
  /** Maximum analysis depth */
  maxDepth: number;
  /** Timeout in milliseconds */
  timeout: number;
  /** Include library/external dependencies */
  includeExternal: boolean;
}

/**
 * Options for CFG analysis
 */
export interface CFGAnalysisOptions {
  /** Compute dominators */
  computeDominators: boolean;
  /** Compute post-dominators */
  computePostDominators: boolean;
  /** Identify loops */
  identifyLoops: boolean;
  /** Include exception flow */
  includeExceptions: boolean;
  /** Maximum analysis depth */
  maxDepth: number;
  /** Timeout in milliseconds */
  timeout: number;
}

/**
 * Default DFG analysis options
 */
export const DEFAULT_DFG_OPTIONS: DFGAnalysisOptions = {
  interprocedural: false,
  trackAliasing: true,
  includeTypes: true,
  maxDepth: 10,
  timeout: 30000,
  includeExternal: false,
};

/**
 * Default CFG analysis options
 */
export const DEFAULT_CFG_OPTIONS: CFGAnalysisOptions = {
  computeDominators: true,
  computePostDominators: true,
  identifyLoops: true,
  includeExceptions: true,
  maxDepth: 10,
  timeout: 30000,
};

// ============================================================================
// Analysis Results
// ============================================================================

/**
 * Data dependency chain
 */
export interface DataDependencyChain {
  /** Starting variable/expression */
  source: DFGNode;
  /** Dependency chain */
  chain: DFGEdge[];
  /** End variable/expression */
  target: DFGNode;
  /** Chain length */
  length: number;
}

/**
 * Execution path through CFG
 */
export interface ExecutionPath {
  /** Path identifier */
  id: string;
  /** Blocks in path order */
  blocks: CFGBlock[];
  /** Edges in path */
  edges: CFGEdge[];
  /** Path conditions */
  conditions: string[];
  /** Is feasible path */
  isFeasible: boolean;
}

/**
 * Variable definition-use information
 */
export interface DefUseInfo {
  /** Variable name */
  variable: string;
  /** Definition node */
  definition: DFGNode;
  /** Use nodes */
  uses: DFGNode[];
  /** Is dead code (no uses) */
  isDeadCode: boolean;
}

/**
 * Taint propagation result
 */
export interface TaintPropagation {
  /** Taint source */
  source: DFGNode;
  /** Taint sinks */
  sinks: DFGNode[];
  /** Propagation paths */
  paths: DataDependencyChain[];
  /** Sanitizers encountered */
  sanitizers: DFGNode[];
}
