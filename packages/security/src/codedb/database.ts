/**
 * @fileoverview CodeDB Database Implementation
 * @module @nahisaho/musubix-security/codedb/database
 * @trace TSK-013, REQ-SEC-CODEDB-001, REQ-SEC-CODEDB-002
 */

import type {
  CodeDatabase,
  ASTStore,
  DFGStore,
  CFGStore,
  GlobalSymbolTable,
  CallGraph,
  TypeStore,
  TaintPath,
  LoopInfo,
  ASTSelector,
  DataFlowQuery,
  ControlFlowQuery,
} from '../types/codedb.js';
import type {
  ASTNode,
  DataFlowGraph,
  ControlFlowGraph,
  SymbolTable,
  DFGNode,
  BasicBlock,
} from '../extractors/base-extractor.js';

/**
 * CodeDB options
 */
export interface CodeDBOptions {
  /** Database name */
  name?: string;
  /** Maximum cache size */
  maxCacheSize?: number;
  /** Enable index building */
  enableIndexes?: boolean;
  /** Storage path (for persistence) */
  storagePath?: string;
}

/**
 * In-memory CodeDB implementation
 */
export class CodeDB implements CodeDatabase {
  id: string;
  name: string;
  createdAt: Date;
  files: string[];
  languages: string[];
  metadata: Record<string, unknown>;

  private astStore: Map<string, ASTNode> = new Map();
  private dfgStore: Map<string, DataFlowGraph> = new Map();
  private cfgStore: Map<string, ControlFlowGraph> = new Map();
  private symbolTables: Map<string, SymbolTable> = new Map();
  private callGraph: CallGraph;
  private typeStore: TypeStore;
  private taintPaths: TaintPath[] = [];
  private loopInfo: LoopInfo[] = [];

  // Indexes for fast lookup
  private astIndex: Map<string, Set<string>> = new Map(); // type -> nodeIds
  private symbolIndex: Map<string, Set<string>> = new Map(); // name -> fileIds
  private callIndex: Map<string, Set<string>> = new Map(); // callee -> callerIds

  /**
   * Create a new CodeDB
   */
  constructor(options: CodeDBOptions = {}) {
    this.id = `codedb_${Date.now()}_${Math.random().toString(36).slice(2, 9)}`;
    this.name = options.name ?? 'default';
    this.createdAt = new Date();
    this.files = [];
    this.languages = [];
    this.metadata = {};

    this.callGraph = { nodes: new Map(), edges: [] };
    this.typeStore = { types: new Map(), typeHierarchy: new Map() };
  }

  /**
   * Add AST to database
   */
  addAST(filePath: string, ast: ASTNode): void {
    this.astStore.set(filePath, ast);

    if (!this.files.includes(filePath)) {
      this.files.push(filePath);
    }

    // Build AST index
    this.indexAST(filePath, ast);
  }

  /**
   * Get AST for file
   */
  getAST(filePath: string): ASTNode | undefined {
    return this.astStore.get(filePath);
  }

  /**
   * Add DFG to database
   */
  addDFG(filePath: string, dfg: DataFlowGraph): void {
    this.dfgStore.set(filePath, dfg);
  }

  /**
   * Get DFG for file
   */
  getDFG(filePath: string): DataFlowGraph | undefined {
    return this.dfgStore.get(filePath);
  }

  /**
   * Add CFG to database
   */
  addCFG(filePath: string, cfg: ControlFlowGraph): void {
    this.cfgStore.set(filePath, cfg);

    // Extract loop information
    this.extractLoopInfo(filePath, cfg);
  }

  /**
   * Get CFG for file
   */
  getCFG(filePath: string): ControlFlowGraph | undefined {
    return this.cfgStore.get(filePath);
  }

  /**
   * Add symbol table
   */
  addSymbolTable(filePath: string, symbols: SymbolTable): void {
    this.symbolTables.set(filePath, symbols);

    // Build symbol index
    for (const [name] of symbols.global) {
      if (!this.symbolIndex.has(name)) {
        this.symbolIndex.set(name, new Set());
      }
      this.symbolIndex.get(name)!.add(filePath);
    }
  }

  /**
   * Get symbol table for file
   */
  getSymbolTable(filePath: string): SymbolTable | undefined {
    return this.symbolTables.get(filePath);
  }

  /**
   * Get global symbol table (merged from all files)
   */
  getGlobalSymbolTable(): GlobalSymbolTable {
    const symbols = new Map<string, {
      name: string;
      file: string;
      kind: string;
      type?: string;
      exported?: boolean;
    }>();

    for (const [filePath, table] of this.symbolTables) {
      for (const [name, entry] of table.global) {
        symbols.set(`${filePath}#${name}`, {
          name,
          file: filePath,
          kind: entry.kind,
          type: entry.type,
          exported: entry.exported,
        });
      }
    }

    return {
      symbols,
      files: this.files,
    };
  }

  /**
   * Add call edge
   */
  addCallEdge(
    callerId: string,
    callerFile: string,
    calleeId: string,
    calleeFile: string,
    location: { line: number; column: number },
  ): void {
    // Ensure nodes exist
    if (!this.callGraph.nodes.has(callerId)) {
      this.callGraph.nodes.set(callerId, {
        id: callerId,
        file: callerFile,
        callers: [],
        callees: [],
      });
    }

    if (!this.callGraph.nodes.has(calleeId)) {
      this.callGraph.nodes.set(calleeId, {
        id: calleeId,
        file: calleeFile,
        callers: [],
        callees: [],
      });
    }

    // Add edge
    this.callGraph.edges.push({
      caller: callerId,
      callee: calleeId,
      location,
    });

    // Update node references
    const callerNode = this.callGraph.nodes.get(callerId)!;
    const calleeNode = this.callGraph.nodes.get(calleeId)!;
    callerNode.callees.push(calleeId);
    calleeNode.callers.push(callerId);

    // Build call index
    if (!this.callIndex.has(calleeId)) {
      this.callIndex.set(calleeId, new Set());
    }
    this.callIndex.get(calleeId)!.add(callerId);
  }

  /**
   * Get call graph
   */
  getCallGraph(): CallGraph {
    return this.callGraph;
  }

  /**
   * Add type information
   */
  addType(
    name: string,
    info: {
      file: string;
      kind: string;
      members?: Array<{ name: string; type: string }>;
      supertypes?: string[];
    },
  ): void {
    this.typeStore.types.set(name, info);

    if (info.supertypes) {
      this.typeStore.typeHierarchy.set(name, info.supertypes);
    }
  }

  /**
   * Get type store
   */
  getTypeStore(): TypeStore {
    return this.typeStore;
  }

  /**
   * Add taint path
   */
  addTaintPath(path: TaintPath): void {
    this.taintPaths.push(path);
  }

  /**
   * Get all taint paths
   */
  getTaintPaths(): TaintPath[] {
    return this.taintPaths;
  }

  /**
   * Get loop information
   */
  getLoopInfo(): LoopInfo[] {
    return this.loopInfo;
  }

  /**
   * Query AST nodes
   */
  queryAST(selector: ASTSelector): ASTNode[] {
    const results: ASTNode[] = [];

    // Use index if querying by type
    if (selector.type && this.astIndex.has(selector.type)) {
      const nodeIds = this.astIndex.get(selector.type)!;
      for (const nodeId of nodeIds) {
        const [filePath] = nodeId.split('#');
        const ast = this.astStore.get(filePath);
        if (ast) {
          const node = this.findNodeById(ast, nodeId);
          if (node && this.matchesSelector(node, selector)) {
            results.push(node);
          }
        }
      }
    } else {
      // Full scan
      for (const [filePath, ast] of this.astStore) {
        if (selector.file && filePath !== selector.file) continue;
        this.collectMatchingNodes(ast, selector, results);
      }
    }

    return results;
  }

  /**
   * Query data flow
   */
  queryDataFlow(query: DataFlowQuery): DFGNode[] {
    const results: DFGNode[] = [];

    for (const [filePath, dfg] of this.dfgStore) {
      if (query.file && filePath !== query.file) continue;

      for (const node of dfg.nodes) {
        if (this.matchesDataFlowQuery(node, query)) {
          results.push(node);
        }
      }
    }

    return results;
  }

  /**
   * Query control flow
   */
  queryControlFlow(query: ControlFlowQuery): BasicBlock[] {
    const results: BasicBlock[] = [];

    for (const [filePath, cfg] of this.cfgStore) {
      if (query.file && filePath !== query.file) continue;

      for (const block of cfg.blocks) {
        if (this.matchesControlFlowQuery(block, query, cfg)) {
          results.push(block);
        }
      }
    }

    return results;
  }

  /**
   * Find files by symbol
   */
  findFilesBySymbol(symbolName: string): string[] {
    return Array.from(this.symbolIndex.get(symbolName) ?? []);
  }

  /**
   * Find callers of a function
   */
  findCallers(functionId: string): string[] {
    return Array.from(this.callIndex.get(functionId) ?? []);
  }

  /**
   * Find reachable functions from a starting point
   */
  findReachableFunctions(startId: string, maxDepth = 10): string[] {
    const visited = new Set<string>();
    const queue: Array<{ id: string; depth: number }> = [{ id: startId, depth: 0 }];

    while (queue.length > 0) {
      const { id, depth } = queue.shift()!;

      if (visited.has(id) || depth > maxDepth) continue;
      visited.add(id);

      const node = this.callGraph.nodes.get(id);
      if (node) {
        for (const calleeId of node.callees) {
          if (!visited.has(calleeId)) {
            queue.push({ id: calleeId, depth: depth + 1 });
          }
        }
      }
    }

    return Array.from(visited);
  }

  /**
   * Check subtype relationship
   */
  isSubtypeOf(subtype: string, supertype: string): boolean {
    if (subtype === supertype) return true;

    const visited = new Set<string>();
    const queue = [subtype];

    while (queue.length > 0) {
      const current = queue.shift()!;
      if (visited.has(current)) continue;
      visited.add(current);

      const supertypes = this.typeStore.typeHierarchy.get(current);
      if (supertypes) {
        if (supertypes.includes(supertype)) return true;
        queue.push(...supertypes);
      }
    }

    return false;
  }

  /**
   * Get database statistics
   */
  getStatistics(): {
    files: number;
    astNodes: number;
    dfgNodes: number;
    cfgBlocks: number;
    symbols: number;
    callEdges: number;
    types: number;
    taintPaths: number;
  } {
    let astNodes = 0;
    let dfgNodes = 0;
    let cfgBlocks = 0;
    let symbols = 0;

    for (const ast of this.astStore.values()) {
      astNodes += this.countNodes(ast);
    }

    for (const dfg of this.dfgStore.values()) {
      dfgNodes += dfg.nodes.length;
    }

    for (const cfg of this.cfgStore.values()) {
      cfgBlocks += cfg.blocks.length;
    }

    for (const table of this.symbolTables.values()) {
      symbols += table.global.size;
      for (const scope of table.scopes) {
        symbols += scope.symbols.size;
      }
    }

    return {
      files: this.files.length,
      astNodes,
      dfgNodes,
      cfgBlocks,
      symbols,
      callEdges: this.callGraph.edges.length,
      types: this.typeStore.types.size,
      taintPaths: this.taintPaths.length,
    };
  }

  /**
   * Export to JSON
   */
  toJSON(): object {
    return {
      id: this.id,
      name: this.name,
      createdAt: this.createdAt.toISOString(),
      files: this.files,
      languages: this.languages,
      metadata: this.metadata,
      statistics: this.getStatistics(),
    };
  }

  // Private helper methods

  private indexAST(filePath: string, ast: ASTNode): void {
    const visit = (node: ASTNode) => {
      if (!this.astIndex.has(node.type)) {
        this.astIndex.set(node.type, new Set());
      }
      this.astIndex.get(node.type)!.add(node.id);

      for (const child of node.children) {
        visit(child);
      }
    };

    visit(ast);
  }

  private extractLoopInfo(filePath: string, cfg: ControlFlowGraph): void {
    // Find back edges to identify loops
    for (const edge of cfg.edges) {
      if (edge.type === 'back') {
        const headerBlock = cfg.blocks.find((b) => b.id === edge.to);
        if (headerBlock) {
          // Find all blocks in the loop body
          const loopBlocks = this.findLoopBlocks(cfg, headerBlock.id, edge.from);
          this.loopInfo.push({
            id: `loop_${this.loopInfo.length}`,
            file: filePath,
            headerId: headerBlock.id,
            bodyBlockIds: loopBlocks,
            backEdge: { from: edge.from, to: edge.to },
          });
        }
      }
    }
  }

  private findLoopBlocks(cfg: ControlFlowGraph, headerId: string, tailId: string): string[] {
    const loopBlocks = new Set<string>([headerId]);
    const workList = [tailId];

    while (workList.length > 0) {
      const blockId = workList.pop()!;
      if (loopBlocks.has(blockId)) continue;

      loopBlocks.add(blockId);
      const block = cfg.blocks.find((b) => b.id === blockId);
      if (block) {
        for (const predId of block.predecessors) {
          if (!loopBlocks.has(predId)) {
            workList.push(predId);
          }
        }
      }
    }

    return Array.from(loopBlocks);
  }

  private findNodeById(ast: ASTNode, nodeId: string): ASTNode | undefined {
    if (ast.id === nodeId) return ast;

    for (const child of ast.children) {
      const found = this.findNodeById(child, nodeId);
      if (found) return found;
    }

    return undefined;
  }

  private matchesSelector(node: ASTNode, selector: ASTSelector): boolean {
    if (selector.type && node.type !== selector.type) return false;
    if (selector.name && node.metadata?.name !== selector.name) return false;
    if (selector.text && !node.text.includes(selector.text)) return false;
    if (selector.lineRange) {
      const { start, end } = selector.lineRange;
      if (node.location.startLine < start || node.location.endLine > end) {
        return false;
      }
    }
    return true;
  }

  private collectMatchingNodes(
    node: ASTNode,
    selector: ASTSelector,
    results: ASTNode[],
  ): void {
    if (this.matchesSelector(node, selector)) {
      results.push(node);
    }

    for (const child of node.children) {
      this.collectMatchingNodes(child, selector, results);
    }
  }

  private matchesDataFlowQuery(node: DFGNode, query: DataFlowQuery): boolean {
    if (query.variable && node.variable !== query.variable) return false;
    if (query.operation && node.operation !== query.operation) return false;
    if (query.taintLabel && node.taintLabel !== query.taintLabel) return false;
    return true;
  }

  private matchesControlFlowQuery(
    block: BasicBlock,
    query: ControlFlowQuery,
    cfg: ControlFlowGraph,
  ): boolean {
    if (query.isEntry && block.id !== cfg.entry) return false;
    if (query.isExit && block.id !== cfg.exit) return false;
    if (query.hasBackEdge) {
      const hasBack = cfg.edges.some(
        (e) => e.type === 'back' && (e.from === block.id || e.to === block.id),
      );
      if (!hasBack) return false;
    }
    return true;
  }

  private countNodes(ast: ASTNode): number {
    let count = 1;
    for (const child of ast.children) {
      count += this.countNodes(child);
    }
    return count;
  }
}

/**
 * Create a new CodeDB instance
 */
export function createCodeDB(options?: CodeDBOptions): CodeDB {
  return new CodeDB(options);
}
