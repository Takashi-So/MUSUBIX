/**
 * @fileoverview CodeDB Serializer - Save/Load CodeDB to/from JSON
 * @module @nahisaho/musubix-security/codedb/serializer
 * @trace TSK-016, REQ-SEC-CODEDB-005
 */

import { CodeDB, type CodeDBOptions } from './database.js';
import type {
  ASTNode,
  DataFlowGraph,
  ControlFlowGraph,
  SymbolTable,
  SymbolEntry,
  DFGNode,
  DFGEdge,
  BasicBlock,
  CFGEdge,
} from '../extractors/base-extractor.js';

/**
 * Serialized database format
 */
export interface SerializedCodeDB {
  /** Format version */
  version: '1.0';
  /** Database metadata */
  metadata: {
    id: string;
    name: string;
    createdAt: string;
    files: string[];
    languages: string[];
    custom: Record<string, unknown>;
  };
  /** AST data */
  ast: Record<string, SerializedAST>;
  /** DFG data */
  dfg: Record<string, SerializedDFG>;
  /** CFG data */
  cfg: Record<string, SerializedCFG>;
  /** Symbol tables */
  symbols: Record<string, SerializedSymbolTable>;
  /** Call graph */
  callGraph: SerializedCallGraph;
  /** Type store */
  types: SerializedTypeStore;
  /** Taint paths */
  taintPaths: SerializedTaintPath[];
  /** Loop info */
  loopInfo: SerializedLoopInfo[];
}

/**
 * Serialized AST node
 */
export interface SerializedAST {
  id: string;
  type: string;
  text: string;
  location: {
    file: string;
    startLine: number;
    endLine: number;
    startColumn: number;
    endColumn: number;
  };
  children: SerializedAST[];
  metadata: Record<string, unknown>;
}

/**
 * Serialized DFG
 */
export interface SerializedDFG {
  nodes: Array<{
    id: string;
    astNodeId: string;
    variable: string;
    operation: string;
    location: {
      file: string;
      startLine: number;
      endLine: number;
      startColumn: number;
      endColumn: number;
    };
    predecessors: string[];
    successors: string[];
    taintLabel?: string;
  }>;
  edges: Array<{
    from: string;
    to: string;
    type: string;
    variable?: string;
    condition?: string;
  }>;
}

/**
 * Serialized CFG
 */
export interface SerializedCFG {
  entry: string;
  exit: string;
  blocks: Array<{
    id: string;
    statements: string[];
    predecessors: string[];
    successors: string[];
    loopHeader?: boolean;
  }>;
  edges: Array<{
    from: string;
    to: string;
    type: string;
    condition?: string;
  }>;
}

/**
 * Serialized symbol table
 */
export interface SerializedSymbolTable {
  global: Array<[string, SerializedSymbolEntry]>;
  scopes: Array<{
    scopeId: string;
    symbols: Array<[string, SerializedSymbolEntry]>;
  }>;
  packageName?: string;
}

/**
 * Serialized symbol entry
 */
export interface SerializedSymbolEntry {
  name: string;
  kind: string;
  type?: string;
  location: {
    file: string;
    startLine: number;
    endLine: number;
    startColumn: number;
    endColumn: number;
  };
  scope: string;
  exported?: boolean;
  modifiers?: string[];
}

/**
 * Serialized call graph
 */
export interface SerializedCallGraph {
  nodes: Array<{
    id: string;
    file: string;
    callers: string[];
    callees: string[];
  }>;
  edges: Array<{
    caller: string;
    callee: string;
    location: { line: number; column: number };
  }>;
}

/**
 * Serialized type store
 */
export interface SerializedTypeStore {
  types: Array<[string, {
    file: string;
    kind: string;
    members?: Array<{ name: string; type: string }>;
    supertypes?: string[];
  }]>;
  typeHierarchy: Array<[string, string[]]>;
}

/**
 * Serialized taint path
 */
export interface SerializedTaintPath {
  id: string;
  source: string;
  sink: string;
  path: string[];
  labels: string[];
}

/**
 * Serialized loop info
 */
export interface SerializedLoopInfo {
  id: string;
  file: string;
  headerId: string;
  bodyBlockIds: string[];
  backEdge: { from: string; to: string };
}

/**
 * Serialization options
 */
export interface SerializeOptions {
  /** Pretty print JSON */
  pretty?: boolean;
  /** Include source text (can be large) */
  includeSourceText?: boolean;
  /** Compress output */
  compress?: boolean;
}

/**
 * Deserialization options
 */
export interface DeserializeOptions {
  /** Validate structure */
  validate?: boolean;
}

/**
 * CodeDB Serializer
 */
export class CodeDBSerializer {
  /**
   * Serialize CodeDB to JSON
   */
  serialize(database: CodeDB, options: SerializeOptions = {}): string {
    const serialized = this.toSerializedFormat(database, options);
    
    if (options.pretty) {
      return JSON.stringify(serialized, null, 2);
    }
    
    return JSON.stringify(serialized);
  }

  /**
   * Deserialize JSON to CodeDB
   */
  deserialize(json: string, options: DeserializeOptions = {}): CodeDB {
    const data = JSON.parse(json) as SerializedCodeDB;
    
    if (options.validate) {
      this.validate(data);
    }
    
    return this.fromSerializedFormat(data);
  }

  /**
   * Convert CodeDB to serialized format
   */
  private toSerializedFormat(
    database: CodeDB,
    options: SerializeOptions,
  ): SerializedCodeDB {
    const serialized: SerializedCodeDB = {
      version: '1.0',
      metadata: {
        id: database.id,
        name: database.name,
        createdAt: database.createdAt.toISOString(),
        files: database.files,
        languages: database.languages,
        custom: database.metadata,
      },
      ast: {},
      dfg: {},
      cfg: {},
      symbols: {},
      callGraph: { nodes: [], edges: [] },
      types: { types: [], typeHierarchy: [] },
      taintPaths: [],
      loopInfo: [],
    };

    // Serialize AST for each file
    for (const filePath of database.files) {
      const ast = database.getAST(filePath);
      if (ast) {
        serialized.ast[filePath] = this.serializeAST(ast, options);
      }

      const dfg = database.getDFG(filePath);
      if (dfg) {
        serialized.dfg[filePath] = this.serializeDFG(dfg);
      }

      const cfg = database.getCFG(filePath);
      if (cfg) {
        serialized.cfg[filePath] = this.serializeCFG(cfg);
      }

      const symbols = database.getSymbolTable(filePath);
      if (symbols) {
        serialized.symbols[filePath] = this.serializeSymbolTable(symbols);
      }
    }

    // Serialize call graph
    const callGraph = database.getCallGraph();
    serialized.callGraph = this.serializeCallGraph(callGraph);

    // Serialize type store
    const typeStore = database.getTypeStore();
    serialized.types = this.serializeTypeStore(typeStore);

    // Serialize taint paths
    for (const path of database.getTaintPaths()) {
      serialized.taintPaths.push(this.serializeTaintPath(path));
    }

    // Serialize loop info
    for (const loop of database.getLoopInfo()) {
      serialized.loopInfo.push(this.serializeLoopInfo(loop));
    }

    return serialized;
  }

  /**
   * Convert serialized format to CodeDB
   */
  private fromSerializedFormat(data: SerializedCodeDB): CodeDB {
    const database = new CodeDB({
      name: data.metadata.name,
    });

    // Restore metadata
    (database as any).id = data.metadata.id;
    (database as any).createdAt = new Date(data.metadata.createdAt);
    (database as any).files = data.metadata.files;
    (database as any).languages = data.metadata.languages;
    (database as any).metadata = data.metadata.custom;

    // Restore AST for each file
    for (const [filePath, serializedAst] of Object.entries(data.ast)) {
      const ast = this.deserializeAST(serializedAst);
      database.addAST(filePath, ast);
    }

    // Restore DFG for each file
    for (const [filePath, serializedDfg] of Object.entries(data.dfg)) {
      const dfg = this.deserializeDFG(serializedDfg);
      database.addDFG(filePath, dfg);
    }

    // Restore CFG for each file
    for (const [filePath, serializedCfg] of Object.entries(data.cfg)) {
      const cfg = this.deserializeCFG(serializedCfg);
      database.addCFG(filePath, cfg);
    }

    // Restore symbol tables
    for (const [filePath, serializedSymbols] of Object.entries(data.symbols)) {
      const symbols = this.deserializeSymbolTable(serializedSymbols);
      database.addSymbolTable(filePath, symbols);
    }

    // Restore call graph
    this.deserializeCallGraph(data.callGraph, database);

    // Restore type store
    this.deserializeTypeStore(data.types, database);

    // Restore taint paths
    for (const serializedPath of data.taintPaths) {
      database.addTaintPath(this.deserializeTaintPath(serializedPath));
    }

    return database;
  }

  /**
   * Serialize AST
   */
  private serializeAST(ast: ASTNode, options: SerializeOptions): SerializedAST {
    return {
      id: ast.id,
      type: ast.type,
      text: options.includeSourceText ? ast.text : '',
      location: ast.location,
      children: ast.children.map((child) => this.serializeAST(child, options)),
      metadata: ast.metadata,
    };
  }

  /**
   * Deserialize AST
   */
  private deserializeAST(data: SerializedAST): ASTNode {
    const node: ASTNode = {
      id: data.id,
      type: data.type,
      text: data.text,
      location: data.location,
      children: data.children.map((child) => this.deserializeAST(child)),
      metadata: data.metadata,
    };

    // Restore parent references
    for (const child of node.children) {
      child.parent = node;
    }

    return node;
  }

  /**
   * Serialize DFG
   */
  private serializeDFG(dfg: DataFlowGraph): SerializedDFG {
    return {
      nodes: dfg.nodes.map((node) => ({
        id: node.id,
        astNodeId: node.astNodeId,
        variable: node.variable,
        operation: node.operation,
        location: node.location,
        predecessors: node.predecessors,
        successors: node.successors,
        taintLabel: node.taintLabel,
      })),
      edges: dfg.edges.map((edge) => ({
        from: edge.from,
        to: edge.to,
        type: edge.type,
        variable: edge.variable,
        condition: edge.condition,
      })),
    };
  }

  /**
   * Deserialize DFG
   */
  private deserializeDFG(data: SerializedDFG): DataFlowGraph {
    return {
      nodes: data.nodes.map((node) => ({
        id: node.id,
        astNodeId: node.astNodeId,
        variable: node.variable,
        operation: node.operation as 'read' | 'write' | 'call' | 'param' | 'return',
        location: node.location,
        predecessors: node.predecessors,
        successors: node.successors,
        taintLabel: node.taintLabel,
      })),
      edges: data.edges.map((edge) => ({
        from: edge.from,
        to: edge.to,
        type: edge.type as 'data' | 'control' | 'call' | 'return',
        variable: edge.variable,
        condition: edge.condition,
      })),
    };
  }

  /**
   * Serialize CFG
   */
  private serializeCFG(cfg: ControlFlowGraph): SerializedCFG {
    return {
      entry: cfg.entry,
      exit: cfg.exit,
      blocks: cfg.blocks.map((block) => ({
        id: block.id,
        statements: block.statements,
        predecessors: block.predecessors,
        successors: block.successors,
        loopHeader: block.loopHeader,
      })),
      edges: cfg.edges.map((edge) => ({
        from: edge.from,
        to: edge.to,
        type: edge.type,
        condition: edge.condition,
      })),
    };
  }

  /**
   * Deserialize CFG
   */
  private deserializeCFG(data: SerializedCFG): ControlFlowGraph {
    return {
      entry: data.entry,
      exit: data.exit,
      blocks: data.blocks.map((block) => ({
        id: block.id,
        statements: block.statements,
        predecessors: block.predecessors,
        successors: block.successors,
        loopHeader: block.loopHeader,
      })),
      edges: data.edges.map((edge) => ({
        from: edge.from,
        to: edge.to,
        type: edge.type as 'sequential' | 'conditional' | 'back' | 'exception',
        condition: edge.condition,
      })),
    };
  }

  /**
   * Serialize symbol table
   */
  private serializeSymbolTable(symbols: SymbolTable): SerializedSymbolTable {
    return {
      global: Array.from(symbols.global.entries()).map(([name, entry]) => [
        name,
        this.serializeSymbolEntry(entry),
      ]),
      scopes: symbols.scopes.map((scope) => ({
        scopeId: scope.scopeId,
        symbols: Array.from(scope.symbols.entries()).map(([name, entry]) => [
          name,
          this.serializeSymbolEntry(entry),
        ]),
      })),
      packageName: symbols.packageName,
    };
  }

  /**
   * Serialize symbol entry
   */
  private serializeSymbolEntry(entry: SymbolEntry): SerializedSymbolEntry {
    return {
      name: entry.name,
      kind: entry.kind,
      type: entry.type,
      location: entry.location,
      scope: entry.scope,
      exported: entry.exported,
      modifiers: entry.modifiers,
    };
  }

  /**
   * Deserialize symbol table
   */
  private deserializeSymbolTable(data: SerializedSymbolTable): SymbolTable {
    return {
      global: new Map(
        data.global.map(([name, entry]) => [name, this.deserializeSymbolEntry(entry)]),
      ),
      scopes: data.scopes.map((scope) => ({
        scopeId: scope.scopeId,
        symbols: new Map(
          scope.symbols.map(([name, entry]) => [name, this.deserializeSymbolEntry(entry)]),
        ),
      })),
      packageName: data.packageName,
    };
  }

  /**
   * Deserialize symbol entry
   */
  private deserializeSymbolEntry(data: SerializedSymbolEntry): SymbolEntry {
    return {
      name: data.name,
      kind: data.kind,
      type: data.type,
      location: data.location,
      scope: data.scope,
      exported: data.exported,
      modifiers: data.modifiers,
    };
  }

  /**
   * Serialize call graph
   */
  private serializeCallGraph(callGraph: any): SerializedCallGraph {
    return {
      nodes: Array.from(callGraph.nodes.values()).map((node: any) => ({
        id: node.id,
        file: node.file,
        callers: node.callers,
        callees: node.callees,
      })),
      edges: callGraph.edges.map((edge: any) => ({
        caller: edge.caller,
        callee: edge.callee,
        location: edge.location,
      })),
    };
  }

  /**
   * Deserialize call graph
   */
  private deserializeCallGraph(data: SerializedCallGraph, database: CodeDB): void {
    for (const edge of data.edges) {
      const callerNode = data.nodes.find((n) => n.id === edge.caller);
      const calleeNode = data.nodes.find((n) => n.id === edge.callee);
      
      if (callerNode && calleeNode) {
        database.addCallEdge(
          edge.caller,
          callerNode.file,
          edge.callee,
          calleeNode.file,
          edge.location,
        );
      }
    }
  }

  /**
   * Serialize type store
   */
  private serializeTypeStore(typeStore: any): SerializedTypeStore {
    return {
      types: Array.from(typeStore.types.entries()),
      typeHierarchy: Array.from(typeStore.typeHierarchy.entries()),
    };
  }

  /**
   * Deserialize type store
   */
  private deserializeTypeStore(data: SerializedTypeStore, database: CodeDB): void {
    for (const [name, info] of data.types) {
      database.addType(name, info);
    }
  }

  /**
   * Serialize taint path
   */
  private serializeTaintPath(path: any): SerializedTaintPath {
    return {
      id: path.id,
      source: path.source,
      sink: path.sink,
      path: path.path,
      labels: path.labels,
    };
  }

  /**
   * Deserialize taint path
   */
  private deserializeTaintPath(data: SerializedTaintPath): any {
    return {
      id: data.id,
      source: data.source,
      sink: data.sink,
      path: data.path,
      labels: data.labels,
    };
  }

  /**
   * Serialize loop info
   */
  private serializeLoopInfo(loop: any): SerializedLoopInfo {
    return {
      id: loop.id,
      file: loop.file,
      headerId: loop.headerId,
      bodyBlockIds: loop.bodyBlockIds,
      backEdge: loop.backEdge,
    };
  }

  /**
   * Validate serialized data structure
   */
  private validate(data: SerializedCodeDB): void {
    if (data.version !== '1.0') {
      throw new Error(`Unsupported CodeDB version: ${data.version}`);
    }

    if (!data.metadata?.id) {
      throw new Error('Missing metadata.id');
    }

    if (!Array.isArray(data.metadata.files)) {
      throw new Error('metadata.files must be an array');
    }
  }
}

/**
 * Create a new serializer
 */
export function createSerializer(): CodeDBSerializer {
  return new CodeDBSerializer();
}

/**
 * Serialize CodeDB to JSON (convenience function)
 */
export function serializeCodeDB(database: CodeDB, options?: SerializeOptions): string {
  const serializer = new CodeDBSerializer();
  return serializer.serialize(database, options);
}

/**
 * Deserialize JSON to CodeDB (convenience function)
 */
export function deserializeCodeDB(json: string, options?: DeserializeOptions): CodeDB {
  const serializer = new CodeDBSerializer();
  return serializer.deserialize(json, options);
}
