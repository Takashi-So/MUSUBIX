/**
 * @fileoverview Call Graph Builder - Build function call relationships for interprocedural analysis
 * @module @nahisaho/musubix-security/analysis/interprocedural/call-graph-builder
 * @trace REQ-SEC-001 (EARS: WHEN analyzing code, THE system SHALL perform interprocedural analysis)
 */

import { Project, SourceFile, SyntaxKind, CallExpression, Node } from 'ts-morph';

/**
 * Node in call graph representing a function/method
 */
export interface CallGraphNode {
  /** Unique ID for this node */
  id: string;
  /** Function/method name */
  name: string;
  /** Fully qualified name (including class/namespace) */
  qualifiedName: string;
  /** Source file path */
  filePath: string;
  /** Line number of definition */
  line: number;
  /** Column number of definition */
  column: number;
  /** Whether this is a method (vs standalone function) */
  isMethod: boolean;
  /** Class name if method */
  className?: string;
  /** Parameter names */
  parameters: string[];
  /** Whether function is async */
  isAsync: boolean;
  /** Whether function is a generator */
  isGenerator: boolean;
  /** Whether function is exported */
  isExported: boolean;
}

/**
 * Edge in call graph representing a function call
 */
export interface CallGraphEdge {
  /** ID of the edge */
  id: string;
  /** Caller node ID */
  callerId: string;
  /** Callee node ID */
  calleeId: string;
  /** Call site file path */
  filePath: string;
  /** Call site line number */
  line: number;
  /** Call site column number */
  column: number;
  /** Arguments passed at call site (expressions as strings) */
  arguments: string[];
  /** Whether call is conditional (inside if/ternary) */
  isConditional: boolean;
  /** Whether call is in a loop */
  isInLoop: boolean;
  /** Whether call is in a try block */
  isInTry: boolean;
  /** Whether this is a callback/async call */
  isCallback: boolean;
}

/**
 * Complete call graph structure
 */
export interface CallGraph {
  /** All function/method nodes */
  nodes: Map<string, CallGraphNode>;
  /** All call edges */
  edges: CallGraphEdge[];
  /** Mapping from node ID to outgoing edges */
  outgoingEdges: Map<string, CallGraphEdge[]>;
  /** Mapping from node ID to incoming edges */
  incomingEdges: Map<string, CallGraphEdge[]>;
  /** Entry points (functions called from outside) */
  entryPoints: string[];
  /** External calls (to unknown functions) */
  externalCalls: ExternalCall[];
}

/**
 * External call to unknown function
 */
export interface ExternalCall {
  /** Caller node ID */
  callerId: string;
  /** Name of external function */
  name: string;
  /** Module/package if known */
  module?: string;
  /** Call site location */
  filePath: string;
  line: number;
  column: number;
  arguments: string[];
}

/**
 * Options for call graph building
 */
export interface CallGraphBuilderOptions {
  /** Include node_modules */
  includeNodeModules?: boolean;
  /** Include type definitions */
  includeTypeDefs?: boolean;
  /** Maximum depth for recursive analysis */
  maxDepth?: number;
  /** Track callback/async calls */
  trackCallbacks?: boolean;
  /** Include anonymous functions */
  includeAnonymous?: boolean;
}

/**
 * Call Graph Builder - Builds interprocedural call graph from TypeScript/JavaScript source
 * @trace REQ-SEC-001
 */
export class CallGraphBuilder {
  private project: Project;
  private options: Required<CallGraphBuilderOptions>;
  private nodeCounter = 0;
  private edgeCounter = 0;
  private nodeMap: Map<string, CallGraphNode> = new Map();
  private signatureToNodeId: Map<string, string> = new Map();

  constructor(options: CallGraphBuilderOptions = {}) {
    this.options = {
      includeNodeModules: options.includeNodeModules ?? false,
      includeTypeDefs: options.includeTypeDefs ?? false,
      maxDepth: options.maxDepth ?? 10,
      trackCallbacks: options.trackCallbacks ?? true,
      includeAnonymous: options.includeAnonymous ?? false,
    };
    this.project = new Project({
      skipFileDependencyResolution: true,
      compilerOptions: {
        allowJs: true,
        noEmit: true,
      },
    });
  }

  /**
   * Build call graph from source files
   */
  buildFromFiles(filePaths: string[]): CallGraph {
    // Add files to project
    for (const filePath of filePaths) {
      if (this.shouldIncludeFile(filePath)) {
        this.project.addSourceFileAtPath(filePath);
      }
    }

    return this.buildGraph();
  }

  /**
   * Build call graph from source code strings
   */
  buildFromSources(sources: Array<{ filePath: string; content: string }>): CallGraph {
    for (const source of sources) {
      if (this.shouldIncludeFile(source.filePath)) {
        this.project.createSourceFile(source.filePath, source.content, { overwrite: true });
      }
    }

    return this.buildGraph();
  }

  /**
   * Build call graph from project directory
   */
  buildFromDirectory(dirPath: string, pattern = '**/*.{ts,tsx,js,jsx}'): CallGraph {
    this.project.addSourceFilesAtPaths(`${dirPath}/${pattern}`);
    return this.buildGraph();
  }

  private buildGraph(): CallGraph {
    const edges: CallGraphEdge[] = [];
    const externalCalls: ExternalCall[] = [];

    // First pass: collect all function declarations
    for (const sourceFile of this.project.getSourceFiles()) {
      if (!this.shouldIncludeFile(sourceFile.getFilePath())) continue;
      this.collectFunctionDeclarations(sourceFile);
    }

    // Second pass: analyze call sites
    for (const sourceFile of this.project.getSourceFiles()) {
      if (!this.shouldIncludeFile(sourceFile.getFilePath())) continue;
      this.collectCallEdges(sourceFile, edges, externalCalls);
    }

    // Build adjacency maps
    const outgoingEdges = new Map<string, CallGraphEdge[]>();
    const incomingEdges = new Map<string, CallGraphEdge[]>();

    for (const edge of edges) {
      if (!outgoingEdges.has(edge.callerId)) {
        outgoingEdges.set(edge.callerId, []);
      }
      outgoingEdges.get(edge.callerId)!.push(edge);

      if (!incomingEdges.has(edge.calleeId)) {
        incomingEdges.set(edge.calleeId, []);
      }
      incomingEdges.get(edge.calleeId)!.push(edge);
    }

    // Find entry points (nodes with no incoming edges from within the project)
    const entryPoints: string[] = [];
    for (const [nodeId, node] of this.nodeMap) {
      if (!incomingEdges.has(nodeId) || incomingEdges.get(nodeId)!.length === 0) {
        if (node.isExported) {
          entryPoints.push(nodeId);
        }
      }
    }

    return {
      nodes: this.nodeMap,
      edges,
      outgoingEdges,
      incomingEdges,
      entryPoints,
      externalCalls,
    };
  }

  private shouldIncludeFile(filePath: string): boolean {
    if (!this.options.includeNodeModules && filePath.includes('node_modules')) {
      return false;
    }
    if (!this.options.includeTypeDefs && filePath.endsWith('.d.ts')) {
      return false;
    }
    return true;
  }

  private collectFunctionDeclarations(sourceFile: SourceFile): void {
    const filePath = sourceFile.getFilePath();

    // Function declarations
    for (const func of sourceFile.getFunctions()) {
      const name = func.getName();
      if (!name && !this.options.includeAnonymous) continue;

      const node = this.createFunctionNode(
        name ?? `<anonymous_${this.nodeCounter}>`,
        name ?? `<anonymous_${this.nodeCounter}>`,
        filePath,
        func.getStartLineNumber(),
        func.getStart(),
        false,
        undefined,
        func.getParameters().map((p) => p.getName()),
        func.isAsync(),
        func.isGenerator(),
        func.isExported()
      );
      this.registerNode(node);
    }

    // Class methods
    for (const cls of sourceFile.getClasses()) {
      const className = cls.getName();
      if (!className) continue;

      for (const method of cls.getMethods()) {
        const methodName = method.getName();
        const qualifiedName = `${className}.${methodName}`;

        const node = this.createFunctionNode(
          methodName,
          qualifiedName,
          filePath,
          method.getStartLineNumber(),
          method.getStart(),
          true,
          className,
          method.getParameters().map((p) => p.getName()),
          method.isAsync(),
          false,
          cls.isExported()
        );
        this.registerNode(node);
      }

      // Constructor
      const ctor = cls.getConstructors()[0];
      if (ctor) {
        const qualifiedName = `${className}.constructor`;
        const node = this.createFunctionNode(
          'constructor',
          qualifiedName,
          filePath,
          ctor.getStartLineNumber(),
          ctor.getStart(),
          true,
          className,
          ctor.getParameters().map((p) => p.getName()),
          false,
          false,
          cls.isExported()
        );
        this.registerNode(node);
      }
    }

    // Arrow functions and function expressions assigned to variables
    for (const varDecl of sourceFile.getVariableDeclarations()) {
      const init = varDecl.getInitializer();
      if (!init) continue;

      if (
        init.getKind() === SyntaxKind.ArrowFunction ||
        init.getKind() === SyntaxKind.FunctionExpression
      ) {
        const name = varDecl.getName();
        const funcExpr = init.asKind(SyntaxKind.ArrowFunction) ?? init.asKind(SyntaxKind.FunctionExpression);
        if (!funcExpr) continue;

        const params = funcExpr.getParameters().map((p) => p.getName());
        const isAsync = funcExpr.isAsync();

        const varStmt = varDecl.getVariableStatement();
        const isExported = varStmt?.isExported() ?? false;

        const node = this.createFunctionNode(
          name,
          name,
          filePath,
          varDecl.getStartLineNumber(),
          varDecl.getStart(),
          false,
          undefined,
          params,
          isAsync,
          false,
          isExported
        );
        this.registerNode(node);
      }
    }
  }

  private collectCallEdges(
    sourceFile: SourceFile,
    edges: CallGraphEdge[],
    externalCalls: ExternalCall[]
  ): void {
    const filePath = sourceFile.getFilePath();

    // Find all call expressions
    sourceFile.forEachDescendant((node) => {
      if (node.getKind() === SyntaxKind.CallExpression) {
        const callExpr = node as CallExpression;
        this.processCallExpression(callExpr, filePath, edges, externalCalls);
      }
    });
  }

  private processCallExpression(
    callExpr: CallExpression,
    filePath: string,
    edges: CallGraphEdge[],
    externalCalls: ExternalCall[]
  ): void {
    // Get enclosing function
    const enclosingFunc = this.findEnclosingFunction(callExpr);
    const callerId = enclosingFunc
      ? this.signatureToNodeId.get(this.getNodeSignature(enclosingFunc.name, filePath, enclosingFunc.line))
      : undefined;

    if (!callerId) return;

    // Get callee information
    const expression = callExpr.getExpression();
    const calleeName = this.getCalleeName(expression);
    const calleeSignature = this.resolveCalleeSignature(expression);

    const args = callExpr.getArguments().map((arg) => arg.getText());
    const line = callExpr.getStartLineNumber();
    const column = callExpr.getStart();

    // Check call context
    const isConditional = this.isInConditional(callExpr);
    const isInLoop = this.isInLoop(callExpr);
    const isInTry = this.isInTry(callExpr);
    const isCallback = this.isCallbackCall(callExpr);

    // Try to resolve callee
    const calleeId = calleeSignature
      ? this.signatureToNodeId.get(calleeSignature)
      : undefined;

    if (calleeId) {
      // Internal call
      const edge: CallGraphEdge = {
        id: `edge_${++this.edgeCounter}`,
        callerId,
        calleeId,
        filePath,
        line,
        column,
        arguments: args,
        isConditional,
        isInLoop,
        isInTry,
        isCallback,
      };
      edges.push(edge);
    } else {
      // External call
      const external: ExternalCall = {
        callerId,
        name: calleeName,
        module: this.getModuleFromExpression(expression),
        filePath,
        line,
        column,
        arguments: args,
      };
      externalCalls.push(external);
    }
  }

  private findEnclosingFunction(node: Node): { name: string; line: number } | undefined {
    let current: Node | undefined = node.getParent();
    while (current) {
      if (current.getKind() === SyntaxKind.FunctionDeclaration) {
        const func = current.asKind(SyntaxKind.FunctionDeclaration);
        if (func) {
          return {
            name: func.getName() ?? '<anonymous>',
            line: func.getStartLineNumber(),
          };
        }
      }
      if (current.getKind() === SyntaxKind.MethodDeclaration) {
        const method = current.asKind(SyntaxKind.MethodDeclaration);
        if (method) {
          const cls = method.getParent()?.asKind(SyntaxKind.ClassDeclaration);
          const className = cls?.getName() ?? '';
          return {
            name: `${className}.${method.getName()}`,
            line: method.getStartLineNumber(),
          };
        }
      }
      if (current.getKind() === SyntaxKind.ArrowFunction || current.getKind() === SyntaxKind.FunctionExpression) {
        // Check if assigned to a variable
        const parent = current.getParent();
        if (parent?.getKind() === SyntaxKind.VariableDeclaration) {
          const varDecl = parent.asKind(SyntaxKind.VariableDeclaration);
          if (varDecl) {
            return {
              name: varDecl.getName(),
              line: varDecl.getStartLineNumber(),
            };
          }
        }
      }
      current = current.getParent();
    }
    return undefined;
  }

  private getCalleeName(expression: Node): string {
    if (expression.getKind() === SyntaxKind.Identifier) {
      return expression.getText();
    }
    if (expression.getKind() === SyntaxKind.PropertyAccessExpression) {
      const propAccess = expression.asKind(SyntaxKind.PropertyAccessExpression);
      return propAccess?.getName() ?? expression.getText();
    }
    return expression.getText();
  }

  private resolveCalleeSignature(expression: Node): string | undefined {
    // Try to resolve using type information
    const type = expression.getType();
    const symbol = type.getSymbol();
    
    if (symbol) {
      const declarations = symbol.getDeclarations();
      if (declarations.length > 0) {
        const decl = declarations[0];
        const filePath = decl.getSourceFile().getFilePath();
        const line = decl.getStartLineNumber();
        const name = symbol.getName();
        return this.getNodeSignature(name, filePath, line);
      }
    }
    return undefined;
  }

  private getModuleFromExpression(expression: Node): string | undefined {
    if (expression.getKind() === SyntaxKind.PropertyAccessExpression) {
      const propAccess = expression.asKind(SyntaxKind.PropertyAccessExpression);
      if (propAccess) {
        const expr = propAccess.getExpression();
        if (expr.getKind() === SyntaxKind.Identifier) {
          return expr.getText();
        }
      }
    }
    return undefined;
  }

  private isInConditional(node: Node): boolean {
    let current: Node | undefined = node.getParent();
    while (current) {
      const kind = current.getKind();
      if (
        kind === SyntaxKind.IfStatement ||
        kind === SyntaxKind.ConditionalExpression ||
        kind === SyntaxKind.SwitchStatement
      ) {
        return true;
      }
      if (
        kind === SyntaxKind.FunctionDeclaration ||
        kind === SyntaxKind.MethodDeclaration ||
        kind === SyntaxKind.ArrowFunction
      ) {
        break;
      }
      current = current.getParent();
    }
    return false;
  }

  private isInLoop(node: Node): boolean {
    let current: Node | undefined = node.getParent();
    while (current) {
      const kind = current.getKind();
      if (
        kind === SyntaxKind.ForStatement ||
        kind === SyntaxKind.ForInStatement ||
        kind === SyntaxKind.ForOfStatement ||
        kind === SyntaxKind.WhileStatement ||
        kind === SyntaxKind.DoStatement
      ) {
        return true;
      }
      if (
        kind === SyntaxKind.FunctionDeclaration ||
        kind === SyntaxKind.MethodDeclaration ||
        kind === SyntaxKind.ArrowFunction
      ) {
        break;
      }
      current = current.getParent();
    }
    return false;
  }

  private isInTry(node: Node): boolean {
    let current: Node | undefined = node.getParent();
    while (current) {
      const kind = current.getKind();
      if (kind === SyntaxKind.TryStatement) {
        return true;
      }
      if (
        kind === SyntaxKind.FunctionDeclaration ||
        kind === SyntaxKind.MethodDeclaration ||
        kind === SyntaxKind.ArrowFunction
      ) {
        break;
      }
      current = current.getParent();
    }
    return false;
  }

  private isCallbackCall(callExpr: CallExpression): boolean {
    // Check if any argument is a function expression
    for (const arg of callExpr.getArguments()) {
      const kind = arg.getKind();
      if (
        kind === SyntaxKind.ArrowFunction ||
        kind === SyntaxKind.FunctionExpression
      ) {
        return true;
      }
    }
    return false;
  }

  private createFunctionNode(
    name: string,
    qualifiedName: string,
    filePath: string,
    line: number,
    column: number,
    isMethod: boolean,
    className: string | undefined,
    parameters: string[],
    isAsync: boolean,
    isGenerator: boolean,
    isExported: boolean
  ): CallGraphNode {
    return {
      id: `node_${++this.nodeCounter}`,
      name,
      qualifiedName,
      filePath,
      line,
      column,
      isMethod,
      className,
      parameters,
      isAsync,
      isGenerator,
      isExported,
    };
  }

  private getNodeSignature(name: string, filePath: string, line: number): string {
    return `${filePath}:${name}:${line}`;
  }

  private registerNode(node: CallGraphNode): void {
    const signature = this.getNodeSignature(node.qualifiedName, node.filePath, node.line);
    this.nodeMap.set(node.id, node);
    this.signatureToNodeId.set(signature, node.id);
  }

  /**
   * Get all functions that can reach a given function
   */
  getCallers(graph: CallGraph, nodeId: string, depth = 1): string[] {
    if (depth <= 0) return [];
    
    const callers = new Set<string>();
    const incoming = graph.incomingEdges.get(nodeId) ?? [];
    
    for (const edge of incoming) {
      callers.add(edge.callerId);
      if (depth > 1) {
        const transitive = this.getCallers(graph, edge.callerId, depth - 1);
        for (const caller of transitive) {
          callers.add(caller);
        }
      }
    }
    
    return Array.from(callers);
  }

  /**
   * Get all functions called by a given function
   */
  getCallees(graph: CallGraph, nodeId: string, depth = 1): string[] {
    if (depth <= 0) return [];
    
    const callees = new Set<string>();
    const outgoing = graph.outgoingEdges.get(nodeId) ?? [];
    
    for (const edge of outgoing) {
      callees.add(edge.calleeId);
      if (depth > 1) {
        const transitive = this.getCallees(graph, edge.calleeId, depth - 1);
        for (const callee of transitive) {
          callees.add(callee);
        }
      }
    }
    
    return Array.from(callees);
  }

  /**
   * Find all paths between two functions
   */
  findPaths(
    graph: CallGraph,
    sourceId: string,
    targetId: string,
    maxLength = 10
  ): string[][] {
    const paths: string[][] = [];
    const visited = new Set<string>();
    
    const dfs = (current: string, path: string[]) => {
      if (path.length > maxLength) return;
      if (current === targetId) {
        paths.push([...path]);
        return;
      }
      if (visited.has(current)) return;
      
      visited.add(current);
      const outgoing = graph.outgoingEdges.get(current) ?? [];
      
      for (const edge of outgoing) {
        dfs(edge.calleeId, [...path, edge.calleeId]);
      }
      
      visited.delete(current);
    };
    
    dfs(sourceId, [sourceId]);
    return paths;
  }

  /**
   * Get call graph statistics
   */
  getStatistics(graph: CallGraph): CallGraphStatistics {
    const nodeCounts = {
      total: graph.nodes.size,
      functions: 0,
      methods: 0,
      async: 0,
      exported: 0,
    };

    for (const node of graph.nodes.values()) {
      if (node.isMethod) nodeCounts.methods++;
      else nodeCounts.functions++;
      if (node.isAsync) nodeCounts.async++;
      if (node.isExported) nodeCounts.exported++;
    }

    const edgeStats = {
      total: graph.edges.length,
      conditional: 0,
      inLoop: 0,
      inTry: 0,
      callback: 0,
    };

    for (const edge of graph.edges) {
      if (edge.isConditional) edgeStats.conditional++;
      if (edge.isInLoop) edgeStats.inLoop++;
      if (edge.isInTry) edgeStats.inTry++;
      if (edge.isCallback) edgeStats.callback++;
    }

    return {
      nodes: nodeCounts,
      edges: edgeStats,
      entryPoints: graph.entryPoints.length,
      externalCalls: graph.externalCalls.length,
      avgOutDegree: graph.edges.length / Math.max(graph.nodes.size, 1),
    };
  }
}

/**
 * Call graph statistics
 */
export interface CallGraphStatistics {
  nodes: {
    total: number;
    functions: number;
    methods: number;
    async: number;
    exported: number;
  };
  edges: {
    total: number;
    conditional: number;
    inLoop: number;
    inTry: number;
    callback: number;
  };
  entryPoints: number;
  externalCalls: number;
  avgOutDegree: number;
}
