/**
 * @fileoverview CodeDB Type Definitions
 * @module @nahisaho/musubix-security/types/codedb
 * @trace TSK-002, REQ-SEC-DB-001, REQ-SEC-DB-002, REQ-SEC-DB-003, REQ-SEC-DB-004
 */

import type {
  ASTNode,
  ASTEdge,
  DFGNode,
  DFGEdge,
  BasicBlock,
  CFGEdge,
  SymbolTable,
  SupportedLanguage,
} from '../extractors/base-extractor.js';

// Re-export SupportedLanguage for convenience
export type { SupportedLanguage } from '../extractors/base-extractor.js';

// ============================================================================
// CodeDB Core Types
// ============================================================================

/**
 * Code Database - Main structure containing all code information
 * @trace REQ-SEC-DB-001
 */
export interface CodeDatabase {
  /** Database version */
  version: string;
  /** Project path */
  projectPath: string;
  /** Languages in this database */
  languages: SupportedLanguage[];
  /** Creation timestamp */
  createdAt: Date;
  /** Last update timestamp */
  updatedAt: Date;
  /** Files in this database */
  files: Map<string, FileInfo>;
  /** AST storage */
  ast: ASTStore;
  /** Data Flow Graph storage */
  dfg: DFGStore;
  /** Control Flow Graph storage */
  cfg: CFGStore;
  /** Symbol table */
  symbols: GlobalSymbolTable;
  /** Call graph */
  callGraph: CallGraph;
  /** Type information */
  types: TypeStore;
  /** Database statistics */
  stats: DatabaseStats;
}

/**
 * File information
 */
export interface FileInfo {
  /** File path (relative to project) */
  path: string;
  /** Language */
  language: SupportedLanguage;
  /** File hash (for incremental updates) */
  hash: string;
  /** Last modified timestamp */
  lastModified: Date;
  /** Lines of code */
  linesOfCode: number;
  /** Root AST node ID */
  rootAstNodeId: string;
}

/**
 * Database statistics
 */
export interface DatabaseStats {
  /** Total files */
  totalFiles: number;
  /** Total lines of code */
  totalLinesOfCode: number;
  /** Total AST nodes */
  totalAstNodes: number;
  /** Total DFG nodes */
  totalDfgNodes: number;
  /** Total CFG blocks */
  totalCfgBlocks: number;
  /** Total symbols */
  totalSymbols: number;
  /** Database size in bytes (estimated) */
  estimatedSize: number;
}

// ============================================================================
// AST Store
// ============================================================================

/**
 * AST Store - Storage for all AST nodes
 * @trace REQ-SEC-DB-002
 */
export interface ASTStore {
  /** All AST nodes by ID */
  nodes: Map<string, ASTNode>;
  /** All AST edges */
  edges: ASTEdge[];
  /** Root nodes per file */
  rootNodes: Map<string, string>;
  /** Node index by type */
  nodesByType: Map<string, Set<string>>;
}

// ============================================================================
// DFG Store
// ============================================================================

/**
 * DFG Store - Storage for Data Flow Graph
 * @trace REQ-SEC-DB-003
 */
export interface DFGStore {
  /** All DFG nodes by ID */
  nodes: Map<string, DFGNode>;
  /** All DFG edges */
  edges: DFGEdge[];
  /** Source node IDs */
  sources: Set<string>;
  /** Sink node IDs */
  sinks: Set<string>;
  /** Sanitizer node IDs */
  sanitizers: Set<string>;
  /** Taint propagation paths (cached) */
  taintPaths: TaintPath[];
}

/**
 * Taint propagation path
 */
export interface TaintPath {
  /** Path ID */
  id: string;
  /** Source node ID */
  sourceId: string;
  /** Sink node ID */
  sinkId: string;
  /** Intermediate node IDs */
  intermediateNodes: string[];
  /** Is sanitized? */
  isSanitized: boolean;
  /** Sanitizer node ID (if sanitized) */
  sanitizerId?: string;
  /** Taint label */
  taintLabel: string;
  /** Confidence score */
  confidence: number;
}

// ============================================================================
// CFG Store
// ============================================================================

/**
 * CFG Store - Storage for Control Flow Graph
 * @trace REQ-SEC-DB-004
 */
export interface CFGStore {
  /** All basic blocks by ID */
  blocks: Map<string, BasicBlock>;
  /** All CFG edges */
  edges: CFGEdge[];
  /** Entry block IDs per function */
  entryBlocks: Map<string, string>;
  /** Exit block IDs per function */
  exitBlocks: Map<string, string>;
  /** Loop information */
  loops: LoopInfo[];
  /** Dominator tree */
  dominatorTree: Map<string, string[]>;
}

/**
 * Loop information
 */
export interface LoopInfo {
  /** Loop ID (optional for backwards compatibility) */
  id?: string;
  /** Loop header block ID */
  headerId: string;
  /** Back edge block IDs */
  backEdges: string[];
  /** All blocks in loop body */
  bodyBlocks: string[];
  /** Nested loop IDs */
  nestedLoops: string[];
  /** Loop bound (if determinable) */
  bound?: number | 'unknown';
}

// ============================================================================
// Symbol Table (Global)
// ============================================================================

/**
 * Global symbol table across all files
 */
export interface GlobalSymbolTable extends SymbolTable {
  /** Symbol index by name */
  symbolsByName: Map<string, Set<string>>;
  /** Exports by file */
  exportsByFile: Map<string, Set<string>>;
  /** Imports by file */
  importsByFile: Map<string, Set<string>>;
  /** Cross-file references */
  crossFileRefs: CrossFileReference[];
}

/**
 * Cross-file reference
 */
export interface CrossFileReference {
  /** Source file */
  sourceFile: string;
  /** Target file */
  targetFile: string;
  /** Source symbol ID */
  sourceSymbolId: string;
  /** Target symbol ID */
  targetSymbolId: string;
  /** Reference type */
  refType: 'import' | 'call' | 'extend' | 'implement';
}

// ============================================================================
// Call Graph
// ============================================================================

/**
 * Call graph
 */
export interface CallGraph {
  /** Call graph nodes (functions) */
  nodes: Map<string, CallGraphNode>;
  /** Call graph edges */
  edges: CallGraphEdge[];
  /** Entry point function IDs */
  entryPoints: Set<string>;
  /** Virtual/dynamic calls */
  virtualCalls: VirtualCall[];
}

/**
 * Call graph node
 */
export interface CallGraphNode {
  /** Node ID (same as symbol ID) */
  id: string;
  /** Function name */
  name: string;
  /** File path */
  file: string;
  /** Function type */
  type: 'function' | 'method' | 'constructor' | 'callback' | 'anonymous';
  /** Is async? */
  isAsync: boolean;
  /** Is exported? */
  isExported: boolean;
  /** Callees (called by this function) */
  callees: string[];
  /** Callers (functions that call this) */
  callers: string[];
}

/**
 * Call graph edge
 */
export interface CallGraphEdge {
  /** Caller function ID */
  callerId: string;
  /** Callee function ID */
  calleeId: string;
  /** Call site location */
  callSite: {
    file: string;
    line: number;
    column: number;
  };
  /** Call type */
  callType: 'direct' | 'indirect' | 'virtual' | 'callback';
  /** Arguments passed */
  arguments: ArgumentInfo[];
}

/**
 * Argument information
 */
export interface ArgumentInfo {
  /** Parameter index */
  index: number;
  /** Argument expression */
  expression: string;
  /** Is tainted? */
  isTainted: boolean;
  /** Taint source (if tainted) */
  taintSource?: string;
}

/**
 * Virtual/dynamic call
 */
export interface VirtualCall {
  /** Call site ID */
  callSiteId: string;
  /** Possible target function IDs */
  possibleTargets: string[];
  /** Call expression */
  expression: string;
  /** Resolution confidence */
  confidence: number;
}

// ============================================================================
// Type Store
// ============================================================================

/**
 * Type store
 */
export interface TypeStore {
  /** Type definitions */
  types: Map<string, TypeDefinition>;
  /** Type aliases */
  aliases: Map<string, string>;
  /** Interface definitions */
  interfaces: Map<string, InterfaceDefinition>;
  /** Class hierarchy */
  classHierarchy: Map<string, ClassHierarchy>;
  /** Type hierarchy (for backwards compatibility) */
  typeHierarchy?: Map<string, TypeHierarchyInfo>;
}

/**
 * Type hierarchy info (legacy)
 */
export interface TypeHierarchyInfo {
  /** Super types */
  superTypes?: string[];
  /** Sub types */
  subTypes?: string[];
}

/**
 * Type definition
 */
export interface TypeDefinition {
  /** Type ID */
  id: string;
  /** Type name */
  name: string;
  /** Type kind */
  kind: 'primitive' | 'object' | 'array' | 'function' | 'union' | 'intersection' | 'generic';
  /** Type parameters (for generics) */
  typeParameters?: string[];
  /** Properties (for objects) */
  properties?: Map<string, string>;
  /** Element type (for arrays) */
  elementType?: string;
  /** Return type (for functions) */
  returnType?: string;
  /** Parameter types (for functions) */
  parameterTypes?: string[];
  /** File where defined (optional) */
  file?: string;
  /** Members (for classes) */
  members?: Array<{ name: string; type: string }>;
  /** Supertypes (optional) */
  supertypes?: string[];
}

/**
 * Interface definition
 */
export interface InterfaceDefinition {
  /** Interface ID */
  id: string;
  /** Interface name */
  name: string;
  /** Extended interfaces */
  extends: string[];
  /** Properties */
  properties: Map<string, TypedProperty>;
  /** Methods */
  methods: Map<string, MethodSignature>;
}

/**
 * Typed property
 */
export interface TypedProperty {
  /** Property name */
  name: string;
  /** Property type */
  type: string;
  /** Is optional? */
  optional: boolean;
  /** Is readonly? */
  readonly: boolean;
}

/**
 * Method signature
 */
export interface MethodSignature {
  /** Method name */
  name: string;
  /** Parameters */
  parameters: { name: string; type: string }[];
  /** Return type */
  returnType: string;
}

/**
 * Class hierarchy information
 */
export interface ClassHierarchy {
  /** Class ID */
  classId: string;
  /** Super class ID */
  superClassId?: string;
  /** Implemented interface IDs */
  implementedInterfaces: string[];
  /** Subclass IDs */
  subClasses: string[];
}

// ============================================================================
// Builder Types
// ============================================================================

/**
 * Options for creating code database
 */
export interface CreateDBOptions {
  /** Project root path */
  projectPath: string;
  /** Languages to extract (default: auto-detect) */
  languages?: SupportedLanguage[];
  /** File patterns to include */
  includePatterns?: string[];
  /** File patterns to exclude */
  excludePatterns?: string[];
  /** Maximum file size in bytes */
  maxFileSize?: number;
  /** Enable parallel extraction */
  parallel?: boolean;
  /** Number of parallel workers */
  parallelWorkers?: number;
  /** Progress callback */
  onProgress?: (progress: BuildProgress) => void;
}

/**
 * Build progress information
 */
export interface BuildProgress {
  /** Current phase */
  phase: 'scanning' | 'extracting' | 'building' | 'indexing';
  /** Files processed */
  filesProcessed: number;
  /** Total files */
  totalFiles: number;
  /** Current file */
  currentFile?: string;
  /** Percentage complete */
  percentage: number;
}

/**
 * File change for incremental updates
 */
export interface FileChange {
  /** File path */
  path: string;
  /** Change type */
  changeType: 'added' | 'modified' | 'deleted';
  /** New content (for added/modified) */
  content?: string;
}

// ============================================================================
// Query Types
// ============================================================================

/**
 * AST query selector
 */
export interface ASTSelector {
  /** Node type to match */
  type?: string | string[];
  /** Node properties to match */
  properties?: Record<string, unknown>;
  /** Parent node type */
  parentType?: string;
  /** Ancestor node types (in order) */
  ancestors?: string[];
  /** Descendant node types (must contain) */
  descendants?: string[];
  /** File path pattern */
  filePattern?: string;
}

/**
 * Data flow query
 */
export interface DataFlowQuery {
  /** Source node selector */
  source?: DFGNodeSelector;
  /** Sink node selector */
  sink?: DFGNodeSelector;
  /** Path constraints */
  pathConstraints?: PathConstraint[];
  /** Include sanitized paths? */
  includeSanitized?: boolean;
  /** Maximum path length */
  maxPathLength?: number;
}

/**
 * DFG node selector
 */
export interface DFGNodeSelector {
  /** Node type */
  nodeType?: 'source' | 'sink' | 'transform' | 'sanitizer' | 'propagator';
  /** Taint label pattern */
  taintLabel?: string | RegExp;
  /** Expression pattern */
  expression?: string | RegExp;
}

/**
 * Path constraint
 */
export interface PathConstraint {
  /** Constraint type */
  type: 'must-pass' | 'must-not-pass' | 'before' | 'after';
  /** Node selector */
  nodeSelector: DFGNodeSelector;
}

/**
 * Control flow query
 */
export interface ControlFlowQuery {
  /** From block selector */
  from: CFGBlockSelector;
  /** To block selector */
  to: CFGBlockSelector;
  /** Path constraints */
  constraints?: CFGPathConstraint[];
}

/**
 * CFG block selector
 */
export interface CFGBlockSelector {
  /** Block ID */
  blockId?: string;
  /** Contains statement type */
  containsType?: string;
  /** Is loop header? */
  isLoopHeader?: boolean;
  /** Is entry? */
  isEntry?: boolean;
  /** Is exit? */
  isExit?: boolean;
}

/**
 * CFG path constraint
 */
export interface CFGPathConstraint {
  /** Constraint type */
  type: 'must-pass' | 'must-not-pass' | 'avoid-loop';
  /** Block selector */
  blockSelector?: CFGBlockSelector;
}

/**
 * Symbol query
 */
export interface SymbolQuery {
  /** Symbol name pattern */
  name?: string | RegExp;
  /** Symbol kind */
  kind?: string | string[];
  /** Is exported? */
  isExported?: boolean;
  /** File pattern */
  filePattern?: string;
  /** Type pattern */
  type?: string | RegExp;
}

export type { ASTNode, ASTEdge, DFGNode, DFGEdge, BasicBlock, CFGEdge, SymbolTable };
