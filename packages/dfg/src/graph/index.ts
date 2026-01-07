/**
 * Graph data structures for DFG/CFG
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-dfg/graph
 */

import type {
  NodeId,
  EdgeId,
  DFGNode,
  DFGEdge,
  DataFlowGraph,
  CFGBlock,
  CFGEdge,
  ControlFlowGraph,
  DataDependencyChain,
  ExecutionPath,
  DefUseInfo,
} from '../types/index.js';

// ============================================================================
// Data Flow Graph Implementation
// ============================================================================

/**
 * Data Flow Graph builder and analyzer
 *
 * @example
 * ```typescript
 * const dfg = new DFGBuilder('module.ts');
 * dfg.addNode({ id: 'n1', type: 'variable', name: 'x', ... });
 * dfg.addEdge({ id: 'e1', type: 'def-use', source: 'n1', target: 'n2', ... });
 * const graph = dfg.build();
 * ```
 */
export class DFGBuilder {
  private nodes: Map<NodeId, DFGNode> = new Map();
  private edges: Map<EdgeId, DFGEdge> = new Map();
  private entryPoints: NodeId[] = [];
  private exitPoints: NodeId[] = [];
  private nodeCounter = 0;
  private edgeCounter = 0;

  constructor(
    private readonly filePath: string,
    private readonly id: string = `dfg-${Date.now()}`
  ) {}

  /**
   * Generate unique node ID
   */
  generateNodeId(prefix: string = 'n'): NodeId {
    return `${prefix}_${++this.nodeCounter}`;
  }

  /**
   * Generate unique edge ID
   */
  generateEdgeId(prefix: string = 'e'): EdgeId {
    return `${prefix}_${++this.edgeCounter}`;
  }

  /**
   * Add a node to the graph
   */
  addNode(node: DFGNode): this {
    this.nodes.set(node.id, node);
    return this;
  }

  /**
   * Add an edge to the graph
   */
  addEdge(edge: DFGEdge): this {
    this.edges.set(edge.id, edge);
    return this;
  }

  /**
   * Add entry point
   */
  addEntryPoint(nodeId: NodeId): this {
    if (!this.entryPoints.includes(nodeId)) {
      this.entryPoints.push(nodeId);
    }
    return this;
  }

  /**
   * Add exit point
   */
  addExitPoint(nodeId: NodeId): this {
    if (!this.exitPoints.includes(nodeId)) {
      this.exitPoints.push(nodeId);
    }
    return this;
  }

  /**
   * Get node by ID
   */
  getNode(id: NodeId): DFGNode | undefined {
    return this.nodes.get(id);
  }

  /**
   * Get edge by ID
   */
  getEdge(id: EdgeId): DFGEdge | undefined {
    return this.edges.get(id);
  }

  /**
   * Get outgoing edges from a node
   */
  getOutgoingEdges(nodeId: NodeId): DFGEdge[] {
    return Array.from(this.edges.values()).filter((e) => e.source === nodeId);
  }

  /**
   * Get incoming edges to a node
   */
  getIncomingEdges(nodeId: NodeId): DFGEdge[] {
    return Array.from(this.edges.values()).filter((e) => e.target === nodeId);
  }

  /**
   * Build the final DataFlowGraph
   */
  build(): DataFlowGraph {
    return {
      id: this.id,
      filePath: this.filePath,
      nodes: new Map(this.nodes),
      edges: new Map(this.edges),
      entryPoints: [...this.entryPoints],
      exitPoints: [...this.exitPoints],
      metadata: {
        analyzedAt: new Date(),
        languageVersion: 'TypeScript 5.x',
        nodeCount: this.nodes.size,
        edgeCount: this.edges.size,
      },
    };
  }
}

/**
 * Data Flow Graph query and analysis utilities
 */
export class DFGAnalyzer {
  constructor(private readonly graph: DataFlowGraph) {}

  /**
   * Find all paths from source to target
   */
  findPaths(
    sourceId: NodeId,
    targetId: NodeId,
    maxPaths: number = 100
  ): DataDependencyChain[] {
    const paths: DataDependencyChain[] = [];
    const visited = new Set<NodeId>();

    const dfs = (current: NodeId, path: DFGEdge[]): void => {
      if (paths.length >= maxPaths) return;

      if (current === targetId) {
        const sourceNode = this.graph.nodes.get(sourceId);
        const targetNode = this.graph.nodes.get(targetId);
        if (sourceNode && targetNode) {
          paths.push({
            source: sourceNode,
            chain: [...path],
            target: targetNode,
            length: path.length,
          });
        }
        return;
      }

      if (visited.has(current)) return;
      visited.add(current);

      const outEdges = this.getOutgoingEdges(current);
      for (const edge of outEdges) {
        dfs(edge.target, [...path, edge]);
      }

      visited.delete(current);
    };

    dfs(sourceId, []);
    return paths;
  }

  /**
   * Get outgoing edges from a node
   */
  getOutgoingEdges(nodeId: NodeId): DFGEdge[] {
    return Array.from(this.graph.edges.values()).filter(
      (e) => e.source === nodeId
    );
  }

  /**
   * Get incoming edges to a node
   */
  getIncomingEdges(nodeId: NodeId): DFGEdge[] {
    return Array.from(this.graph.edges.values()).filter(
      (e) => e.target === nodeId
    );
  }

  /**
   * Get all data dependencies for a variable
   */
  getDataDependencies(variableName: string): DefUseInfo[] {
    const results: DefUseInfo[] = [];
    const definitions = new Map<NodeId, DFGNode>();
    const uses = new Map<NodeId, DFGNode[]>();

    // Find all definitions
    for (const node of this.graph.nodes.values()) {
      if (node.name === variableName) {
        if (
          node.type === 'variable' ||
          node.type === 'parameter' ||
          node.type === 'assignment'
        ) {
          definitions.set(node.id, node);
          uses.set(node.id, []);
        }
      }
    }

    // Find all uses via def-use edges
    for (const edge of this.graph.edges.values()) {
      if (edge.type === 'def-use' && definitions.has(edge.source)) {
        const useNode = this.graph.nodes.get(edge.target);
        if (useNode) {
          uses.get(edge.source)?.push(useNode);
        }
      }
    }

    // Build results
    for (const [defId, defNode] of definitions) {
      const nodeUses = uses.get(defId) || [];
      results.push({
        variable: variableName,
        definition: defNode,
        uses: nodeUses,
        isDeadCode: nodeUses.length === 0,
      });
    }

    return results;
  }

  /**
   * Find taint propagation from source
   */
  findTaintPropagation(sourceId: NodeId): DFGNode[] {
    const tainted = new Set<NodeId>();
    const queue: NodeId[] = [sourceId];

    while (queue.length > 0) {
      const current = queue.shift()!;
      if (tainted.has(current)) continue;
      tainted.add(current);

      const outEdges = this.getOutgoingEdges(current);
      for (const edge of outEdges) {
        if (
          edge.type === 'def-use' ||
          edge.type === 'data-dep' ||
          edge.type === 'alias'
        ) {
          queue.push(edge.target);
        }
      }
    }

    return Array.from(tainted)
      .map((id) => this.graph.nodes.get(id))
      .filter((n): n is DFGNode => n !== undefined);
  }

  /**
   * Find dead code (definitions without uses)
   */
  findDeadCode(): DFGNode[] {
    const dead: DFGNode[] = [];

    for (const node of this.graph.nodes.values()) {
      if (
        node.type === 'variable' ||
        node.type === 'assignment'
      ) {
        const outEdges = this.getOutgoingEdges(node.id);
        const hasUse = outEdges.some((e) => e.type === 'def-use');
        if (!hasUse) {
          dead.push(node);
        }
      }
    }

    return dead;
  }

  /**
   * Export graph to DOT format for visualization
   */
  toDot(): string {
    const lines: string[] = ['digraph DFG {', '  rankdir=TB;'];

    // Nodes
    for (const node of this.graph.nodes.values()) {
      const label = `${node.name}\\n(${node.type})`;
      const shape = this.getNodeShape(node.type);
      lines.push(`  "${node.id}" [label="${label}" shape=${shape}];`);
    }

    // Edges
    for (const edge of this.graph.edges.values()) {
      const label = edge.label || edge.type;
      const style = edge.type === 'control-dep' ? 'dashed' : 'solid';
      lines.push(
        `  "${edge.source}" -> "${edge.target}" [label="${label}" style=${style}];`
      );
    }

    lines.push('}');
    return lines.join('\n');
  }

  private getNodeShape(
    type: string
  ): 'box' | 'ellipse' | 'diamond' | 'parallelogram' {
    switch (type) {
      case 'function':
      case 'class':
        return 'box';
      case 'conditional':
        return 'diamond';
      case 'call':
        return 'parallelogram';
      default:
        return 'ellipse';
    }
  }
}

// ============================================================================
// Control Flow Graph Implementation
// ============================================================================

/**
 * Control Flow Graph builder
 */
export class CFGBuilder {
  private blocks: Map<NodeId, CFGBlock> = new Map();
  private edges: Map<EdgeId, CFGEdge> = new Map();
  private entryBlock: NodeId = '';
  private exitBlocks: NodeId[] = [];
  private blockCounter = 0;
  private edgeCounter = 0;

  constructor(
    private readonly functionName: string,
    private readonly filePath: string,
    private readonly id: string = `cfg-${Date.now()}`
  ) {}

  /**
   * Generate unique block ID
   */
  generateBlockId(prefix: string = 'b'): NodeId {
    return `${prefix}_${++this.blockCounter}`;
  }

  /**
   * Generate unique edge ID
   */
  generateEdgeId(prefix: string = 'e'): EdgeId {
    return `${prefix}_${++this.edgeCounter}`;
  }

  /**
   * Add a basic block
   */
  addBlock(block: CFGBlock): this {
    this.blocks.set(block.id, block);
    return this;
  }

  /**
   * Add an edge
   */
  addEdge(edge: CFGEdge): this {
    this.edges.set(edge.id, edge);

    // Update predecessor/successor
    const sourceBlock = this.blocks.get(edge.source);
    const targetBlock = this.blocks.get(edge.target);

    if (sourceBlock && !sourceBlock.successors.includes(edge.target)) {
      sourceBlock.successors.push(edge.target);
    }
    if (targetBlock && !targetBlock.predecessors.includes(edge.source)) {
      targetBlock.predecessors.push(edge.source);
    }

    return this;
  }

  /**
   * Set entry block
   */
  setEntryBlock(blockId: NodeId): this {
    this.entryBlock = blockId;
    return this;
  }

  /**
   * Add exit block
   */
  addExitBlock(blockId: NodeId): this {
    if (!this.exitBlocks.includes(blockId)) {
      this.exitBlocks.push(blockId);
    }
    return this;
  }

  /**
   * Build the final ControlFlowGraph
   */
  build(): ControlFlowGraph {
    const cyclomaticComplexity = this.computeCyclomaticComplexity();
    const maxLoopDepth = this.computeMaxLoopDepth();

    return {
      id: this.id,
      functionName: this.functionName,
      filePath: this.filePath,
      entryBlock: this.entryBlock,
      exitBlocks: [...this.exitBlocks],
      blocks: new Map(this.blocks),
      edges: new Map(this.edges),
      metadata: {
        analyzedAt: new Date(),
        cyclomaticComplexity,
        maxLoopDepth,
        blockCount: this.blocks.size,
        edgeCount: this.edges.size,
      },
    };
  }

  private computeCyclomaticComplexity(): number {
    // M = E - N + 2P (for single connected component, P=1)
    return this.edges.size - this.blocks.size + 2;
  }

  private computeMaxLoopDepth(): number {
    let maxDepth = 0;
    for (const block of this.blocks.values()) {
      if (block.loopDepth > maxDepth) {
        maxDepth = block.loopDepth;
      }
    }
    return maxDepth;
  }
}

/**
 * Control Flow Graph analyzer
 */
export class CFGAnalyzer {
  constructor(private readonly graph: ControlFlowGraph) {}

  /**
   * Find all execution paths from entry to exit
   */
  findAllPaths(maxPaths: number = 100): ExecutionPath[] {
    const paths: ExecutionPath[] = [];
    const visited = new Set<string>();

    const dfs = (
      current: NodeId,
      path: { blocks: CFGBlock[]; edges: CFGEdge[] }
    ): void => {
      if (paths.length >= maxPaths) return;

      const block = this.graph.blocks.get(current);
      if (!block) return;

      path.blocks.push(block);

      if (this.graph.exitBlocks.includes(current)) {
        const conditions = path.edges
          .filter((e) => e.condition)
          .map((e) => e.condition!);

        paths.push({
          id: `path_${paths.length + 1}`,
          blocks: [...path.blocks],
          edges: [...path.edges],
          conditions,
          isFeasible: true, // Would need SMT solver for actual feasibility
        });
        path.blocks.pop();
        return;
      }

      const pathKey = path.blocks.map((b) => b.id).join(',');
      if (visited.has(pathKey)) {
        path.blocks.pop();
        return;
      }
      visited.add(pathKey);

      const outEdges = this.getOutgoingEdges(current);
      for (const edge of outEdges) {
        if (!edge.isBackEdge) {
          // Skip back edges to avoid infinite loops
          path.edges.push(edge);
          dfs(edge.target, path);
          path.edges.pop();
        }
      }

      visited.delete(pathKey);
      path.blocks.pop();
    };

    dfs(this.graph.entryBlock, { blocks: [], edges: [] });
    return paths;
  }

  /**
   * Get outgoing edges from a block
   */
  getOutgoingEdges(blockId: NodeId): CFGEdge[] {
    return Array.from(this.graph.edges.values()).filter(
      (e) => e.source === blockId
    );
  }

  /**
   * Get incoming edges to a block
   */
  getIncomingEdges(blockId: NodeId): CFGEdge[] {
    return Array.from(this.graph.edges.values()).filter(
      (e) => e.target === blockId
    );
  }

  /**
   * Find all loops (natural loops)
   */
  findLoops(): Array<{ header: CFGBlock; body: CFGBlock[] }> {
    const loops: Array<{ header: CFGBlock; body: CFGBlock[] }> = [];

    // Find back edges
    const backEdges = Array.from(this.graph.edges.values()).filter(
      (e) => e.isBackEdge
    );

    for (const backEdge of backEdges) {
      const header = this.graph.blocks.get(backEdge.target);
      if (!header) continue;

      // Find loop body via reverse DFS from back edge source
      const body = new Set<CFGBlock>();
      const stack: NodeId[] = [backEdge.source];

      while (stack.length > 0) {
        const current = stack.pop()!;
        if (current === backEdge.target) continue;

        const block = this.graph.blocks.get(current);
        if (!block || body.has(block)) continue;

        body.add(block);
        for (const predId of block.predecessors) {
          stack.push(predId);
        }
      }

      loops.push({
        header,
        body: Array.from(body),
      });
    }

    return loops;
  }

  /**
   * Compute cyclomatic complexity
   */
  getCyclomaticComplexity(): number {
    return this.graph.metadata.cyclomaticComplexity;
  }

  /**
   * Export graph to DOT format
   */
  toDot(): string {
    const lines: string[] = [
      `digraph CFG_${this.graph.functionName} {`,
      '  rankdir=TB;',
    ];

    // Blocks
    for (const block of this.graph.blocks.values()) {
      const label =
        block.statements.length > 0
          ? block.statements
              .map((s) => s.text.replace(/"/g, '\\"'))
              .join('\\n')
          : block.label;
      const shape = this.getBlockShape(block.type);
      const color = block.loopDepth > 0 ? 'lightblue' : 'white';
      lines.push(
        `  "${block.id}" [label="${label}" shape=${shape} style=filled fillcolor=${color}];`
      );
    }

    // Edges
    for (const edge of this.graph.edges.values()) {
      const label = edge.condition || edge.type;
      const style = edge.isBackEdge ? 'dashed' : 'solid';
      const color = edge.isBackEdge ? 'red' : 'black';
      lines.push(
        `  "${edge.source}" -> "${edge.target}" [label="${label}" style=${style} color=${color}];`
      );
    }

    lines.push('}');
    return lines.join('\n');
  }

  private getBlockShape(type: string): string {
    switch (type) {
      case 'entry':
      case 'exit':
        return 'ellipse';
      case 'conditional':
        return 'diamond';
      case 'loop-header':
        return 'hexagon';
      default:
        return 'box';
    }
  }
}

// Re-export
export { DFGBuilder as DataFlowGraphBuilder };
export { CFGBuilder as ControlFlowGraphBuilder };
