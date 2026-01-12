/**
 * @fileoverview Base Extractor - Abstract base class for language-specific code extractors
 * @module @nahisaho/musubix-security/extractors/base-extractor
 * @trace TSK-001, REQ-SEC-LANG-001, REQ-SEC-LANG-002, REQ-SEC-LANG-003, REQ-SEC-LANG-004
 */

import type { SourceLocation } from '../types/vulnerability.js';

// ============================================================================
// Supported Languages
// ============================================================================

/**
 * Supported programming languages
 * @trace REQ-SEC-LANG-001, REQ-SEC-LANG-002, REQ-SEC-LANG-003, REQ-SEC-LANG-004
 */
export type SupportedLanguage =
  | 'typescript'
  | 'javascript'
  | 'python'
  | 'php'
  | 'go'      // Phase 1
  | 'java'    // Phase 1
  | 'ruby'    // Phase 1
  | 'rust'    // Phase 1
  | 'kotlin'  // Phase 2
  | 'swift';  // Phase 2

/**
 * File extension to language mapping
 */
export const EXTENSION_TO_LANGUAGE: Record<string, SupportedLanguage> = {
  // TypeScript
  '.ts': 'typescript',
  '.tsx': 'typescript',
  '.mts': 'typescript',
  '.cts': 'typescript',
  // JavaScript
  '.js': 'javascript',
  '.jsx': 'javascript',
  '.mjs': 'javascript',
  '.cjs': 'javascript',
  // Python
  '.py': 'python',
  '.pyw': 'python',
  // PHP
  '.php': 'php',
  '.phtml': 'php',
  '.php5': 'php',
  '.php7': 'php',
  // Go
  '.go': 'go',
  // Java
  '.java': 'java',
  // Ruby
  '.rb': 'ruby',
  '.erb': 'ruby',
  '.rake': 'ruby',
  // Rust
  '.rs': 'rust',
  // Kotlin
  '.kt': 'kotlin',
  '.kts': 'kotlin',
  // Swift
  '.swift': 'swift',
};

// ============================================================================
// AST Types
// ============================================================================

/**
 * AST Node type
 */
export interface ASTNode {
  /** Unique node ID */
  id: string;
  /** Node type (e.g., 'FunctionDeclaration', 'CallExpression') */
  type: string;
  /** Source location */
  location: SourceLocation;
  /** Node-specific properties */
  properties: Record<string, unknown>;
  /** Child node IDs */
  children: string[];
  /** Parent node ID */
  parent?: string;
  /** Raw text content */
  text?: string;
  /** Additional metadata */
  metadata?: Record<string, unknown>;
}

/**
 * AST Edge type
 */
export interface ASTEdge {
  /** Source node ID */
  from: string;
  /** Target node ID */
  to: string;
  /** Edge label (e.g., 'body', 'arguments', 'condition') */
  label: string;
}

// ============================================================================
// Data Flow Graph Types
// ============================================================================

/**
 * Data Flow Graph Node
 */
export interface DFGNode {
  /** Unique node ID */
  id: string;
  /** Corresponding AST node ID */
  astNodeId: string;
  /** Node type */
  nodeType: 'source' | 'sink' | 'transform' | 'sanitizer' | 'propagator';
  /** Taint label (if tainted) */
  taintLabel?: string;
  /** Expression text */
  expression: string;
  /** Source location */
  location: SourceLocation;
  /** Additional properties */
  properties: Record<string, unknown>;
  /** Variable name (optional) */
  variable?: string;
  /** Operation type (optional) */
  operation?: 'read' | 'write' | 'call' | 'param' | 'return';
  /** Predecessor node IDs */
  predecessors?: string[];
  /** Successor node IDs */
  successors?: string[];
}

/**
 * Data Flow Graph Edge
 */
export interface DFGEdge {
  /** Source node ID */
  from: string;
  /** Target node ID */
  to: string;
  /** Edge type */
  edgeType: 'data' | 'control' | 'implicit';
  /** Edge properties */
  properties: Record<string, unknown>;
  /** Legacy type field (alias for edgeType) */
  type?: 'data' | 'control' | 'call' | 'return';
  /** Variable name */
  variable?: string;
  /** Condition expression */
  condition?: string;
}

/**
 * Data Flow Graph
 */
export interface DataFlowGraph {
  /** All DFG nodes */
  nodes: Map<string, DFGNode>;
  /** All DFG edges */
  edges: DFGEdge[];
  /** Source node IDs */
  sources: string[];
  /** Sink node IDs */
  sinks: string[];
}

// ============================================================================
// Control Flow Graph Types
// ============================================================================

/**
 * Basic Block in CFG
 */
export interface BasicBlock {
  /** Unique block ID */
  id: string;
  /** AST node IDs in this block */
  statements: string[];
  /** Predecessor block IDs */
  predecessors: string[];
  /** Successor block IDs */
  successors: string[];
  /** Dominator block IDs (optional) */
  dominators?: string[];
  /** Is this a loop header? */
  loopHeader?: boolean;
  /** Is this an entry block? */
  isEntry?: boolean;
  /** Is this an exit block? */
  isExit?: boolean;
}

/**
 * CFG Edge
 */
export interface CFGEdge {
  /** Source block ID */
  from: string;
  /** Target block ID */
  to: string;
  /** Edge type */
  edgeType: 'normal' | 'true' | 'false' | 'exception' | 'finally' | 'break' | 'continue';
  /** Condition expression (for conditional edges) */
  condition?: string;
  /** Legacy type field (alias for edgeType) */
  type?: 'sequential' | 'conditional' | 'back' | 'exception';
}

/**
 * Control Flow Graph
 */
export interface ControlFlowGraph {
  /** All basic blocks */
  blocks: Map<string, BasicBlock>;
  /** All CFG edges */
  edges: CFGEdge[];
  /** Entry block IDs */
  entryBlocks: string[];
  /** Exit block IDs */
  exitBlocks: string[];
  /** Entry block ID (singular, for legacy compatibility) */
  entry?: string;
  /** Exit block ID (singular, for legacy compatibility) */
  exit?: string;
}

// ============================================================================
// Symbol Table Types
// ============================================================================

/**
 * Symbol kind
 */
export type SymbolKind =
  | 'function'
  | 'method'
  | 'class'
  | 'interface'
  | 'variable'
  | 'constant'
  | 'parameter'
  | 'property'
  | 'import'
  | 'export'
  | 'type'
  | 'enum';

/**
 * Symbol definition
 */
export interface Symbol {
  /** Symbol name */
  name: string;
  /** Symbol kind */
  kind: SymbolKind;
  /** Definition location */
  location: SourceLocation;
  /** Type (if known) */
  type?: string;
  /** Scope ID */
  scopeId: string;
  /** Is exported? */
  isExported?: boolean;
  /** Additional properties */
  properties: Record<string, unknown>;
}

/**
 * Function symbol with additional info
 */
export interface FunctionSymbol extends Symbol {
  kind: 'function' | 'method';
  /** Parameters */
  parameters: ParameterInfo[];
  /** Return type */
  returnType?: string;
  /** Is async? */
  isAsync?: boolean;
  /** Is generator? */
  isGenerator?: boolean;
}

/**
 * Parameter info
 */
export interface ParameterInfo {
  /** Parameter name */
  name: string;
  /** Parameter index */
  index: number;
  /** Parameter type */
  type?: string;
  /** Has default value? */
  hasDefault?: boolean;
  /** Is rest parameter? */
  isRest?: boolean;
}

/**
 * Class symbol with additional info
 */
export interface ClassSymbol extends Omit<Symbol, 'properties'> {
  kind: 'class';
  /** Super class name */
  superClass?: string;
  /** Implemented interfaces */
  implements?: string[];
  /** Methods */
  methods: string[];
  /** Class properties (method names) */
  properties: string[];
  /** Additional metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Symbol Table
 */
export interface SymbolTable {
  /** All symbols by ID */
  symbols: Map<string, Symbol>;
  /** Function symbols */
  functions: Map<string, FunctionSymbol>;
  /** Class symbols */
  classes: Map<string, ClassSymbol>;
  /** Scopes */
  scopes: Map<string, ScopeInfo>;
  /** Global symbols (for legacy compatibility) */
  global?: Map<string, Symbol>;
  /** Package name (optional) */
  packageName?: string;
}

/**
 * Scope info
 */
export interface ScopeInfo {
  /** Scope ID */
  id: string;
  /** Parent scope ID */
  parentId?: string;
  /** Symbol IDs in this scope */
  symbols: string[];
  /** Scope kind */
  kind: 'global' | 'function' | 'block' | 'class' | 'module';
}

// ============================================================================
// Extraction Result
// ============================================================================

/**
 * Extraction error
 */
export interface ExtractionError {
  /** Error message */
  message: string;
  /** Error location */
  location?: SourceLocation;
  /** Error severity */
  severity: 'error' | 'warning' | 'info';
}

/**
 * Extraction metrics
 */
export interface ExtractionMetrics {
  /** Total lines of code */
  linesOfCode: number;
  /** Number of functions */
  functionCount: number;
  /** Number of classes */
  classCount: number;
  /** Number of AST nodes */
  astNodeCount: number;
  /** Extraction time in milliseconds */
  extractionTime: number;
}

/**
 * Extraction result
 * @trace REQ-SEC-DB-002, REQ-SEC-DB-003, REQ-SEC-DB-004
 */
export interface ExtractionResult {
  /** Language */
  language: SupportedLanguage;
  /** File path */
  filePath: string;
  /** AST root node */
  ast: ASTNode;
  /** All AST nodes */
  astNodes: Map<string, ASTNode>;
  /** AST edges */
  astEdges: ASTEdge[];
  /** Data flow graph */
  dfg: DataFlowGraph;
  /** Control flow graph */
  cfg: ControlFlowGraph;
  /** Symbol table */
  symbols: SymbolTable;
  /** Extraction errors */
  errors: ExtractionError[];
  /** Extraction metrics */
  metrics: ExtractionMetrics;
  /** Taint paths (optional) */
  taintPaths?: TaintPathInfo[];
}

/**
 * Taint path info (from extraction)
 */
export interface TaintPathInfo {
  /** Source node ID */
  sourceId: string;
  /** Sink node ID */
  sinkId: string;
  /** Intermediate node IDs */
  path: string[];
  /** Taint label */
  label: string;
}

// ============================================================================
// Extraction Options
// ============================================================================

/**
 * Extraction progress
 */
export interface ExtractionProgress {
  /** Current phase */
  phase: 'parsing' | 'ast' | 'dfg' | 'cfg' | 'symbols' | 'done';
  /** Progress percentage (0-100) */
  percentage: number;
  /** Current file */
  file?: string;
}

// ============================================================================
// Framework Model Types
// ============================================================================

/**
 * Framework source definition
 */
export interface FrameworkSource {
  /** Pattern to match */
  pattern: RegExp;
  /** Source type */
  type: string;
  /** Description */
  description: string;
  /** Taint label */
  taintLabel: string;
}

/**
 * Framework sink definition
 */
export interface FrameworkSink {
  /** Pattern to match */
  pattern: RegExp;
  /** Sink type */
  type: string;
  /** Vulnerability type this leads to */
  vulnerabilityType: string;
  /** Severity */
  severity: 'critical' | 'high' | 'medium' | 'low';
}

/**
 * Framework sanitizer definition
 */
export interface FrameworkSanitizer {
  /** Pattern to match */
  pattern: RegExp;
  /** What this sanitizer sanitizes */
  sanitizes: string[];
}

/**
 * Framework model
 */
export interface FrameworkModel {
  /** Framework name */
  name: string;
  /** Supported languages */
  languages: SupportedLanguage[];
  /** Sources */
  sources: FrameworkSource[];
  /** Sinks */
  sinks: FrameworkSink[];
  /** Sanitizers */
  sanitizers: FrameworkSanitizer[];
}

// ============================================================================
// Base Extractor
// ============================================================================

/**
 * Extraction options
 */
export interface ExtractionOptions {
  /** Include AST in result */
  includeAST?: boolean;
  /** Include DFG in result */
  includeDFG?: boolean;
  /** Include CFG in result */
  includeCFG?: boolean;
  /** Include symbols in result */
  includeSymbols?: boolean;
  /** Framework models to apply */
  frameworkModels?: FrameworkModel[];
  /** Maximum AST depth */
  maxDepth?: number;
  /** Timeout in milliseconds */
  timeout?: number;
}

/**
 * Default extraction options
 */
export const DEFAULT_EXTRACTION_OPTIONS: Required<ExtractionOptions> = {
  includeAST: true,
  includeDFG: true,
  includeCFG: true,
  includeSymbols: true,
  frameworkModels: [],
  maxDepth: 100,
  timeout: 30000,
};

/**
 * Abstract base class for language-specific code extractors
 * @trace TSK-001
 */
export abstract class BaseExtractor {
  /**
   * Get the supported language
   */
  abstract readonly language: SupportedLanguage;

  /**
   * Get supported file extensions
   */
  abstract readonly extensions: string[];

  /**
   * Check if a file is supported by this extractor
   */
  supports(filePath: string): boolean {
    const ext = filePath.substring(filePath.lastIndexOf('.'));
    return this.extensions.includes(ext.toLowerCase());
  }

  /**
   * Extract code information from source
   * @param source - Source code content
   * @param filePath - File path
   * @param options - Extraction options
   * @returns Extraction result
   */
  async extract(
    source: string,
    filePath: string,
    options: ExtractionOptions = {}
  ): Promise<ExtractionResult> {
    const opts = { ...DEFAULT_EXTRACTION_OPTIONS, ...options };
    const startTime = Date.now();
    const errors: ExtractionError[] = [];

    // Build AST
    const { ast, astNodes, astEdges } = await this.buildAST(source, filePath);

    // Build DFG (if requested)
    let dfg: DataFlowGraph = {
      nodes: new Map(),
      edges: [],
      sources: [],
      sinks: [],
    };
    if (opts.includeDFG) {
      dfg = await this.buildDFG(astNodes, astEdges, opts.frameworkModels);
    }

    // Build CFG (if requested)
    let cfg: ControlFlowGraph = {
      blocks: new Map(),
      edges: [],
      entryBlocks: [],
      exitBlocks: [],
    };
    if (opts.includeCFG) {
      cfg = await this.buildCFG(astNodes, astEdges);
    }

    // Extract symbols (if requested)
    let symbols: SymbolTable = {
      symbols: new Map(),
      functions: new Map(),
      classes: new Map(),
      scopes: new Map(),
    };
    if (opts.includeSymbols) {
      symbols = await this.extractSymbols(astNodes);
    }

    const extractionTime = Date.now() - startTime;

    return {
      language: this.language,
      filePath,
      ast,
      astNodes,
      astEdges,
      dfg,
      cfg,
      symbols,
      errors,
      metrics: {
        linesOfCode: source.split('\n').length,
        functionCount: symbols.functions.size,
        classCount: symbols.classes.size,
        astNodeCount: astNodes.size,
        extractionTime,
      },
    };
  }

  /**
   * Build AST from source code
   * @param source - Source code
   * @param filePath - File path
   * @returns AST root node and all nodes
   */
  protected abstract buildAST(
    source: string,
    filePath: string
  ): Promise<{
    ast: ASTNode;
    astNodes: Map<string, ASTNode>;
    astEdges: ASTEdge[];
  }>;

  /**
   * Build Data Flow Graph from AST
   * @param astNodes - All AST nodes
   * @param astEdges - AST edges
   * @param frameworkModels - Framework models to apply
   * @returns Data Flow Graph
   */
  protected abstract buildDFG(
    astNodes: Map<string, ASTNode>,
    astEdges: ASTEdge[],
    frameworkModels: FrameworkModel[]
  ): Promise<DataFlowGraph>;

  /**
   * Build Control Flow Graph from AST
   * @param astNodes - All AST nodes
   * @param astEdges - AST edges
   * @returns Control Flow Graph
   */
  protected abstract buildCFG(
    astNodes: Map<string, ASTNode>,
    astEdges: ASTEdge[]
  ): Promise<ControlFlowGraph>;

  /**
   * Extract symbols from AST
   * @param astNodes - All AST nodes
   * @returns Symbol table
   */
  protected abstract extractSymbols(
    astNodes: Map<string, ASTNode>
  ): Promise<SymbolTable>;

  /**
   * Get framework models supported by this extractor
   */
  abstract getFrameworkModels(): FrameworkModel[];

  /**
   * Generate unique node ID
   */
  protected generateNodeId(prefix: string = 'node'): string {
    return `${prefix}_${Date.now()}_${Math.random().toString(36).substring(2, 9)}`;
  }

  /**
   * Create source location from line/column info
   */
  protected createLocation(
    file: string,
    startLine: number,
    startColumn: number,
    endLine: number,
    endColumn: number
  ): SourceLocation {
    return {
      file,
      startLine,
      startColumn,
      endLine,
      endColumn,
    };
  }
}

/**
 * Factory function to create extractor
 */
export function createExtractor(_language: SupportedLanguage): BaseExtractor {
  // This will be implemented when specific extractors are available
  throw new Error(`Extractor for language '${_language}' not yet implemented`);
}

/**
 * Detect language from file path
 */
export function detectLanguage(filePath: string): SupportedLanguage | null {
  const ext = filePath.substring(filePath.lastIndexOf('.')).toLowerCase();
  return EXTENSION_TO_LANGUAGE[ext] ?? null;
}
