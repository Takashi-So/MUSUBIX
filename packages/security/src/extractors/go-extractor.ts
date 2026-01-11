/**
 * @fileoverview Go Language Extractor
 * @module @nahisaho/musubix-security/extractors/go-extractor
 * @trace TSK-005, TSK-006, TSK-007, TSK-008
 * @trace REQ-SEC-LANG-002, REQ-SEC-CFG-001, REQ-SEC-DFG-001
 */

import {
  BaseExtractor,
  type ASTNode,
  type DFGNode,
  type DFGEdge,
  type DataFlowGraph,
  type BasicBlock,
  type CFGEdge,
  type ControlFlowGraph,
  type SymbolEntry,
  type SymbolTable,
  type FrameworkModel,
  type ExtractionResult,
  type ExtractorOptions,
} from './base-extractor.js';

// Tree-sitter types (will be properly typed when tree-sitter is installed)
interface TreeSitterNode {
  type: string;
  text: string;
  startPosition: { row: number; column: number };
  endPosition: { row: number; column: number };
  children: TreeSitterNode[];
  childCount: number;
  parent: TreeSitterNode | null;
  namedChildren: TreeSitterNode[];
  namedChildCount: number;
  firstChild: TreeSitterNode | null;
  lastChild: TreeSitterNode | null;
  nextSibling: TreeSitterNode | null;
  previousSibling: TreeSitterNode | null;
  childForFieldName(name: string): TreeSitterNode | null;
  childrenForFieldName(name: string): TreeSitterNode[];
}

interface TreeSitterTree {
  rootNode: TreeSitterNode;
}

interface TreeSitterParser {
  parse(input: string): TreeSitterTree;
  setLanguage(language: unknown): void;
}

/**
 * Go-specific AST node types
 */
type GoNodeType =
  | 'source_file'
  | 'package_clause'
  | 'import_declaration'
  | 'function_declaration'
  | 'method_declaration'
  | 'type_declaration'
  | 'const_declaration'
  | 'var_declaration'
  | 'short_var_declaration'
  | 'assignment_statement'
  | 'if_statement'
  | 'for_statement'
  | 'switch_statement'
  | 'select_statement'
  | 'return_statement'
  | 'go_statement'
  | 'defer_statement'
  | 'call_expression'
  | 'selector_expression'
  | 'index_expression'
  | 'slice_expression'
  | 'type_assertion'
  | 'binary_expression'
  | 'unary_expression'
  | 'identifier'
  | 'field_identifier'
  | 'package_identifier'
  | 'type_identifier'
  | 'composite_literal'
  | 'func_literal'
  | 'interpreted_string_literal'
  | 'raw_string_literal'
  | 'int_literal'
  | 'float_literal'
  | 'block'
  | 'parameter_list'
  | 'result'
  | 'struct_type'
  | 'interface_type'
  | 'map_type'
  | 'channel_type'
  | 'pointer_type'
  | 'slice_type'
  | 'array_type';

/**
 * Go framework patterns
 */
const GO_FRAMEWORK_PATTERNS: FrameworkModel[] = [
  // net/http
  {
    id: 'go-net-http',
    name: 'net/http',
    language: 'go',
    sourcePatterns: [
      { pattern: 'r.URL.Query', type: 'user_input' },
      { pattern: 'r.FormValue', type: 'user_input' },
      { pattern: 'r.PostFormValue', type: 'user_input' },
      { pattern: 'r.Header.Get', type: 'user_input' },
      { pattern: 'r.Body', type: 'user_input' },
      { pattern: 'r.Cookie', type: 'user_input' },
    ],
    sinkPatterns: [
      { pattern: 'w.Write', type: 'xss' },
      { pattern: 'fmt.Fprintf(w,', type: 'xss' },
      { pattern: 'template.Execute', type: 'xss' },
      { pattern: 'http.Redirect', type: 'open_redirect' },
    ],
    sanitizerPatterns: [
      { pattern: 'html.EscapeString', type: 'xss' },
      { pattern: 'template.HTMLEscapeString', type: 'xss' },
      { pattern: 'url.PathEscape', type: 'path_traversal' },
    ],
  },
  // Gin framework
  {
    id: 'go-gin',
    name: 'Gin',
    language: 'go',
    sourcePatterns: [
      { pattern: 'c.Query', type: 'user_input' },
      { pattern: 'c.Param', type: 'user_input' },
      { pattern: 'c.PostForm', type: 'user_input' },
      { pattern: 'c.GetHeader', type: 'user_input' },
      { pattern: 'c.ShouldBind', type: 'user_input' },
      { pattern: 'c.BindJSON', type: 'user_input' },
    ],
    sinkPatterns: [
      { pattern: 'c.String', type: 'xss' },
      { pattern: 'c.HTML', type: 'xss' },
      { pattern: 'c.Redirect', type: 'open_redirect' },
    ],
    sanitizerPatterns: [],
  },
  // database/sql
  {
    id: 'go-database-sql',
    name: 'database/sql',
    language: 'go',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'db.Query', type: 'sql_injection' },
      { pattern: 'db.Exec', type: 'sql_injection' },
      { pattern: 'db.QueryRow', type: 'sql_injection' },
      { pattern: 'tx.Query', type: 'sql_injection' },
      { pattern: 'tx.Exec', type: 'sql_injection' },
    ],
    sanitizerPatterns: [
      { pattern: 'db.Prepare', type: 'sql_injection' },
    ],
  },
  // os/exec
  {
    id: 'go-os-exec',
    name: 'os/exec',
    language: 'go',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'exec.Command', type: 'command_injection' },
      { pattern: 'exec.CommandContext', type: 'command_injection' },
    ],
    sanitizerPatterns: [],
  },
  // io/ioutil & os
  {
    id: 'go-file-io',
    name: 'file-io',
    language: 'go',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'os.Open', type: 'path_traversal' },
      { pattern: 'os.Create', type: 'path_traversal' },
      { pattern: 'os.ReadFile', type: 'path_traversal' },
      { pattern: 'os.WriteFile', type: 'path_traversal' },
      { pattern: 'ioutil.ReadFile', type: 'path_traversal' },
      { pattern: 'ioutil.WriteFile', type: 'path_traversal' },
    ],
    sanitizerPatterns: [
      { pattern: 'filepath.Clean', type: 'path_traversal' },
      { pattern: 'filepath.Abs', type: 'path_traversal' },
    ],
  },
];

/**
 * Go language extractor implementation
 */
export class GoExtractor extends BaseExtractor {
  private parser: TreeSitterParser | null = null;
  private tree: TreeSitterTree | null = null;
  private nodeIdCounter = 0;
  private blockIdCounter = 0;

  /**
   * Create a new Go extractor
   */
  constructor(options?: ExtractorOptions) {
    super('go', options);
    this.frameworkModels = GO_FRAMEWORK_PATTERNS;
  }

  /**
   * Initialize tree-sitter parser
   */
  protected async initParser(): Promise<void> {
    if (this.parser) return;

    try {
      // Dynamic import for tree-sitter
      const Parser = (await import('tree-sitter')).default;
      const Go = (await import('tree-sitter-go')).default;

      this.parser = new Parser();
      this.parser.setLanguage(Go);
    } catch {
      // Tree-sitter not available, will use fallback parsing
      this.parser = null;
    }
  }

  /**
   * Parse Go source code into AST
   */
  async parseAST(code: string, filePath: string): Promise<ASTNode> {
    await this.initParser();

    if (this.parser) {
      this.tree = this.parser.parse(code);
      return this.convertTreeSitterNode(this.tree.rootNode, filePath);
    }

    // Fallback: minimal AST structure
    return this.createFallbackAST(code, filePath);
  }

  /**
   * Convert tree-sitter node to our AST format
   */
  private convertTreeSitterNode(node: TreeSitterNode, filePath: string): ASTNode {
    const id = `${filePath}#${this.nodeIdCounter++}`;
    const children = node.namedChildren.map((child) =>
      this.convertTreeSitterNode(child, filePath),
    );

    const astNode: ASTNode = {
      id,
      type: node.type as GoNodeType,
      text: node.text,
      location: {
        file: filePath,
        startLine: node.startPosition.row + 1,
        endLine: node.endPosition.row + 1,
        startColumn: node.startPosition.column,
        endColumn: node.endPosition.column,
      },
      children,
      metadata: this.extractNodeMetadata(node),
    };

    // Set parent references
    for (const child of children) {
      child.parent = astNode;
    }

    return astNode;
  }

  /**
   * Extract metadata from tree-sitter node
   */
  private extractNodeMetadata(node: TreeSitterNode): Record<string, unknown> {
    const metadata: Record<string, unknown> = {};

    switch (node.type) {
      case 'function_declaration':
      case 'method_declaration': {
        const nameNode = node.childForFieldName('name');
        const paramsNode = node.childForFieldName('parameters');
        const resultNode = node.childForFieldName('result');

        metadata.name = nameNode?.text;
        metadata.parameters = this.extractParameters(paramsNode);
        metadata.returnType = resultNode?.text;

        if (node.type === 'method_declaration') {
          const receiverNode = node.childForFieldName('receiver');
          metadata.receiver = receiverNode?.text;
        }
        break;
      }

      case 'type_declaration': {
        const specs = node.namedChildren.filter((c) => c.type === 'type_spec');
        metadata.types = specs.map((spec) => ({
          name: spec.childForFieldName('name')?.text,
          kind: spec.childForFieldName('type')?.type,
        }));
        break;
      }

      case 'import_declaration': {
        const specs = node.namedChildren.filter(
          (c) => c.type === 'import_spec' || c.type === 'import_spec_list',
        );
        metadata.imports = this.extractImports(specs);
        break;
      }

      case 'call_expression': {
        const funcNode = node.childForFieldName('function');
        const argsNode = node.childForFieldName('arguments');
        metadata.callee = funcNode?.text;
        metadata.argumentCount = argsNode?.namedChildCount ?? 0;
        break;
      }

      case 'if_statement':
      case 'for_statement':
      case 'switch_statement':
        metadata.isControlFlow = true;
        break;

      case 'go_statement':
        metadata.isConcurrent = true;
        break;

      case 'defer_statement':
        metadata.isDeferred = true;
        break;
    }

    return metadata;
  }

  /**
   * Extract function parameters
   */
  private extractParameters(
    paramsNode: TreeSitterNode | null,
  ): Array<{ name: string; type: string }> {
    if (!paramsNode) return [];

    const params: Array<{ name: string; type: string }> = [];
    const paramDecls = paramsNode.namedChildren.filter(
      (c) => c.type === 'parameter_declaration',
    );

    for (const decl of paramDecls) {
      const names = decl.childrenForFieldName('name');
      const typeNode = decl.childForFieldName('type');
      const typeName = typeNode?.text ?? 'unknown';

      for (const nameNode of names) {
        params.push({ name: nameNode.text, type: typeName });
      }
    }

    return params;
  }

  /**
   * Extract import specifications
   */
  private extractImports(
    specs: TreeSitterNode[],
  ): Array<{ path: string; alias?: string }> {
    const imports: Array<{ path: string; alias?: string }> = [];

    for (const spec of specs) {
      if (spec.type === 'import_spec') {
        const pathNode = spec.childForFieldName('path');
        const aliasNode = spec.childForFieldName('name');
        imports.push({
          path: pathNode?.text?.replace(/"/g, '') ?? '',
          alias: aliasNode?.text,
        });
      } else if (spec.type === 'import_spec_list') {
        imports.push(...this.extractImports(spec.namedChildren));
      }
    }

    return imports;
  }

  /**
   * Build control flow graph
   */
  async buildCFG(ast: ASTNode): Promise<ControlFlowGraph> {
    const blocks: BasicBlock[] = [];
    const edges: CFGEdge[] = [];
    
    // Find all functions
    const functions = this.findNodesByType(ast, [
      'function_declaration',
      'method_declaration',
      'func_literal',
    ]);

    for (const func of functions) {
      const funcCFG = this.buildFunctionCFG(func);
      blocks.push(...funcCFG.blocks);
      edges.push(...funcCFG.edges);
    }

    // Create entry and exit blocks
    const entry: BasicBlock = {
      id: `${ast.location.file}#entry`,
      statements: [],
      predecessors: [],
      successors: blocks.filter((b) => b.predecessors.length === 0).map((b) => b.id),
    };

    const exit: BasicBlock = {
      id: `${ast.location.file}#exit`,
      statements: [],
      predecessors: blocks.filter((b) => b.successors.length === 0).map((b) => b.id),
      successors: [],
    };

    return {
      entry: entry.id,
      exit: exit.id,
      blocks: [entry, ...blocks, exit],
      edges,
    };
  }

  /**
   * Build CFG for a single function
   */
  private buildFunctionCFG(func: ASTNode): { blocks: BasicBlock[]; edges: CFGEdge[] } {
    const blocks: BasicBlock[] = [];
    const edges: CFGEdge[] = [];
    const bodyNode = func.children.find((c) => c.type === 'block');

    if (!bodyNode) {
      return { blocks, edges };
    }

    // Process function body
    const { blocks: bodyBlocks, edges: bodyEdges } = this.processBlock(bodyNode);
    blocks.push(...bodyBlocks);
    edges.push(...bodyEdges);

    return { blocks, edges };
  }

  /**
   * Process a block of statements
   */
  private processBlock(block: ASTNode): { blocks: BasicBlock[]; edges: CFGEdge[] } {
    const blocks: BasicBlock[] = [];
    const edges: CFGEdge[] = [];
    let currentBlock: BasicBlock | null = null;

    for (const stmt of block.children) {
      if (this.isControlFlowStatement(stmt)) {
        // End current block
        if (currentBlock && currentBlock.statements.length > 0) {
          blocks.push(currentBlock);
        }

        // Process control flow statement
        const cfResult = this.processControlFlow(stmt);
        blocks.push(...cfResult.blocks);
        edges.push(...cfResult.edges);

        // Start new block
        currentBlock = null;
      } else {
        // Add to current block
        if (!currentBlock) {
          currentBlock = {
            id: `${block.location.file}#block_${this.blockIdCounter++}`,
            statements: [],
            predecessors: [],
            successors: [],
          };
        }
        currentBlock.statements.push(stmt.id);
      }
    }

    // Add final block
    if (currentBlock && currentBlock.statements.length > 0) {
      blocks.push(currentBlock);
    }

    // Connect sequential blocks
    for (let i = 0; i < blocks.length - 1; i++) {
      if (blocks[i].successors.length === 0) {
        blocks[i].successors.push(blocks[i + 1].id);
        blocks[i + 1].predecessors.push(blocks[i].id);
        edges.push({
          from: blocks[i].id,
          to: blocks[i + 1].id,
          type: 'sequential',
        });
      }
    }

    return { blocks, edges };
  }

  /**
   * Check if statement is control flow
   */
  private isControlFlowStatement(stmt: ASTNode): boolean {
    return [
      'if_statement',
      'for_statement',
      'switch_statement',
      'select_statement',
      'return_statement',
      'go_statement',
      'defer_statement',
    ].includes(stmt.type);
  }

  /**
   * Process control flow statement
   */
  private processControlFlow(stmt: ASTNode): { blocks: BasicBlock[]; edges: CFGEdge[] } {
    const blocks: BasicBlock[] = [];
    const edges: CFGEdge[] = [];

    switch (stmt.type) {
      case 'if_statement': {
        // Create condition block
        const condBlock: BasicBlock = {
          id: `${stmt.location.file}#if_cond_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [],
        };
        blocks.push(condBlock);

        // Process then branch
        const thenBlock = stmt.children.find((c) => c.type === 'block');
        if (thenBlock) {
          const { blocks: thenBlocks, edges: thenEdges } = this.processBlock(thenBlock);
          blocks.push(...thenBlocks);
          edges.push(...thenEdges);

          if (thenBlocks.length > 0) {
            condBlock.successors.push(thenBlocks[0].id);
            thenBlocks[0].predecessors.push(condBlock.id);
            edges.push({
              from: condBlock.id,
              to: thenBlocks[0].id,
              type: 'conditional',
              condition: 'true',
            });
          }
        }

        // Process else branch
        const elseClause = stmt.children.find(
          (c) => c.type === 'block' && c !== thenBlock,
        );
        if (elseClause) {
          const { blocks: elseBlocks, edges: elseEdges } = this.processBlock(elseClause);
          blocks.push(...elseBlocks);
          edges.push(...elseEdges);

          if (elseBlocks.length > 0) {
            condBlock.successors.push(elseBlocks[0].id);
            elseBlocks[0].predecessors.push(condBlock.id);
            edges.push({
              from: condBlock.id,
              to: elseBlocks[0].id,
              type: 'conditional',
              condition: 'false',
            });
          }
        }
        break;
      }

      case 'for_statement': {
        // Create loop header block
        const headerBlock: BasicBlock = {
          id: `${stmt.location.file}#for_header_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [],
        };
        blocks.push(headerBlock);

        // Process loop body
        const bodyBlock = stmt.children.find((c) => c.type === 'block');
        if (bodyBlock) {
          const { blocks: bodyBlocks, edges: bodyEdges } = this.processBlock(bodyBlock);
          blocks.push(...bodyBlocks);
          edges.push(...bodyEdges);

          if (bodyBlocks.length > 0) {
            // Entry to body
            headerBlock.successors.push(bodyBlocks[0].id);
            bodyBlocks[0].predecessors.push(headerBlock.id);
            edges.push({
              from: headerBlock.id,
              to: bodyBlocks[0].id,
              type: 'conditional',
              condition: 'true',
            });

            // Back edge
            const lastBody = bodyBlocks[bodyBlocks.length - 1];
            lastBody.successors.push(headerBlock.id);
            headerBlock.predecessors.push(lastBody.id);
            edges.push({
              from: lastBody.id,
              to: headerBlock.id,
              type: 'back',
            });
          }
        }
        break;
      }

      case 'return_statement': {
        const returnBlock: BasicBlock = {
          id: `${stmt.location.file}#return_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [], // Will connect to exit
        };
        blocks.push(returnBlock);
        break;
      }

      default: {
        const block: BasicBlock = {
          id: `${stmt.location.file}#stmt_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [],
        };
        blocks.push(block);
      }
    }

    return { blocks, edges };
  }

  /**
   * Build data flow graph
   */
  async buildDFG(ast: ASTNode, cfg: ControlFlowGraph): Promise<DataFlowGraph> {
    const nodes: DFGNode[] = [];
    const edges: DFGEdge[] = [];
    const nodeMap = new Map<string, DFGNode>();

    // Process all assignments and declarations
    const assignments = this.findNodesByType(ast, [
      'short_var_declaration',
      'var_declaration',
      'const_declaration',
      'assignment_statement',
    ]);

    for (const assign of assignments) {
      const dfgNodes = this.createDFGNodesForAssignment(assign, nodeMap);
      nodes.push(...dfgNodes);
    }

    // Process function parameters as sources
    const functions = this.findNodesByType(ast, [
      'function_declaration',
      'method_declaration',
    ]);

    for (const func of functions) {
      const paramNodes = this.createDFGNodesForParameters(func, nodeMap);
      nodes.push(...paramNodes);
    }

    // Build edges based on data dependencies
    edges.push(...this.buildDFGEdges(nodes, nodeMap));

    return {
      nodes,
      edges,
    };
  }

  /**
   * Create DFG nodes for assignment
   */
  private createDFGNodesForAssignment(
    assign: ASTNode,
    nodeMap: Map<string, DFGNode>,
  ): DFGNode[] {
    const nodes: DFGNode[] = [];

    // Get left-hand side (defined variables)
    const lhs = assign.children.filter((c) =>
      ['identifier', 'expression_list'].includes(c.type),
    );

    for (const target of lhs) {
      if (target.type === 'identifier') {
        const node: DFGNode = {
          id: `dfg_${target.id}`,
          astNodeId: target.id,
          variable: target.text,
          operation: 'write',
          location: target.location,
          predecessors: [],
          successors: [],
        };
        nodes.push(node);
        nodeMap.set(target.text, node);
      }
    }

    return nodes;
  }

  /**
   * Create DFG nodes for function parameters
   */
  private createDFGNodesForParameters(
    func: ASTNode,
    nodeMap: Map<string, DFGNode>,
  ): DFGNode[] {
    const nodes: DFGNode[] = [];
    const params = func.metadata?.parameters as Array<{ name: string; type: string }> | undefined;

    if (params) {
      for (const param of params) {
        const node: DFGNode = {
          id: `dfg_param_${func.id}_${param.name}`,
          astNodeId: func.id,
          variable: param.name,
          operation: 'param',
          location: func.location,
          predecessors: [],
          successors: [],
          taintLabel: this.inferTaintLabel(param.name, param.type),
        };
        nodes.push(node);
        nodeMap.set(param.name, node);
      }
    }

    return nodes;
  }

  /**
   * Infer taint label from parameter
   */
  private inferTaintLabel(name: string, type: string): string | undefined {
    // HTTP request parameters
    if (name === 'r' && type.includes('Request')) return 'user_input';
    if (name === 'req' && type.includes('Request')) return 'user_input';
    if (name === 'c' && type.includes('Context')) return 'user_input'; // Gin context

    return undefined;
  }

  /**
   * Build DFG edges
   */
  private buildDFGEdges(
    nodes: DFGNode[],
    nodeMap: Map<string, DFGNode>,
  ): DFGEdge[] {
    const edges: DFGEdge[] = [];

    // Connect reads to their definitions
    for (const node of nodes) {
      if (node.operation === 'read') {
        const def = nodeMap.get(node.variable);
        if (def && def !== node) {
          edges.push({
            from: def.id,
            to: node.id,
            type: 'data',
            variable: node.variable,
          });
          def.successors.push(node.id);
          node.predecessors.push(def.id);
        }
      }
    }

    return edges;
  }

  /**
   * Build symbol table
   */
  async buildSymbolTable(ast: ASTNode): Promise<SymbolTable> {
    const global: Map<string, SymbolEntry> = new Map();
    const scopes: Array<{ scopeId: string; symbols: Map<string, SymbolEntry> }> = [];

    // Extract package name
    const packageNode = this.findNodesByType(ast, ['package_clause'])[0];
    const packageName = packageNode?.children[0]?.text ?? 'main';

    // Process imports
    const importNodes = this.findNodesByType(ast, ['import_declaration']);
    for (const importDecl of importNodes) {
      const imports = importDecl.metadata?.imports as Array<{ path: string; alias?: string }> | undefined;
      if (imports) {
        for (const imp of imports) {
          const alias = imp.alias ?? imp.path.split('/').pop() ?? imp.path;
          global.set(alias, {
            name: alias,
            kind: 'import',
            type: imp.path,
            location: importDecl.location,
            scope: 'global',
          });
        }
      }
    }

    // Process type declarations
    const typeDecls = this.findNodesByType(ast, ['type_declaration']);
    for (const typeDecl of typeDecls) {
      const types = typeDecl.metadata?.types as Array<{ name: string; kind: string }> | undefined;
      if (types) {
        for (const t of types) {
          global.set(t.name, {
            name: t.name,
            kind: 'type',
            type: t.kind,
            location: typeDecl.location,
            scope: 'global',
            exported: this.isExported(t.name),
          });
        }
      }
    }

    // Process function declarations
    const funcDecls = this.findNodesByType(ast, [
      'function_declaration',
      'method_declaration',
    ]);
    for (const funcDecl of funcDecls) {
      const name = funcDecl.metadata?.name as string;
      const params = funcDecl.metadata?.parameters as Array<{ name: string; type: string }> | undefined;
      const returnType = funcDecl.metadata?.returnType as string | undefined;
      const receiver = funcDecl.metadata?.receiver as string | undefined;

      if (name) {
        const fullName = receiver ? `${receiver}.${name}` : name;
        global.set(fullName, {
          name: fullName,
          kind: 'function',
          type: `func(${params?.map((p) => p.type).join(', ') ?? ''}) ${returnType ?? ''}`,
          location: funcDecl.location,
          scope: 'global',
          exported: this.isExported(name),
        });

        // Create function scope
        const funcScope: Map<string, SymbolEntry> = new Map();
        if (params) {
          for (const param of params) {
            funcScope.set(param.name, {
              name: param.name,
              kind: 'parameter',
              type: param.type,
              location: funcDecl.location,
              scope: fullName,
            });
          }
        }
        scopes.push({ scopeId: fullName, symbols: funcScope });
      }
    }

    // Process var/const declarations
    const varDecls = this.findNodesByType(ast, ['var_declaration', 'const_declaration']);
    for (const varDecl of varDecls) {
      const specs = varDecl.children.filter((c) => c.type === 'var_spec' || c.type === 'const_spec');
      for (const spec of specs) {
        const nameNode = spec.children.find((c) => c.type === 'identifier');
        const typeNode = spec.children.find((c) => c.type.includes('type'));
        if (nameNode) {
          global.set(nameNode.text, {
            name: nameNode.text,
            kind: varDecl.type === 'var_declaration' ? 'variable' : 'constant',
            type: typeNode?.text ?? 'unknown',
            location: varDecl.location,
            scope: 'global',
            exported: this.isExported(nameNode.text),
          });
        }
      }
    }

    return {
      global,
      scopes,
      packageName,
    };
  }

  /**
   * Check if Go identifier is exported (starts with uppercase)
   */
  private isExported(name: string): boolean {
    return /^[A-Z]/.test(name);
  }

  /**
   * Detect framework usage
   */
  async detectFrameworks(ast: ASTNode, symbols: SymbolTable): Promise<FrameworkModel[]> {
    const detected: FrameworkModel[] = [];
    const imports = new Set<string>();

    // Collect all imports
    for (const [, entry] of symbols.global) {
      if (entry.kind === 'import' && entry.type) {
        imports.add(entry.type);
      }
    }

    // Check against framework patterns
    for (const framework of this.frameworkModels) {
      let matched = false;

      switch (framework.id) {
        case 'go-net-http':
          matched = imports.has('net/http');
          break;
        case 'go-gin':
          matched = imports.has('github.com/gin-gonic/gin');
          break;
        case 'go-database-sql':
          matched = imports.has('database/sql');
          break;
        case 'go-os-exec':
          matched = imports.has('os/exec');
          break;
        case 'go-file-io':
          matched = imports.has('os') || imports.has('io/ioutil');
          break;
      }

      if (matched) {
        detected.push(framework);
      }
    }

    return detected;
  }

  /**
   * Create fallback AST for when tree-sitter is unavailable
   */
  private createFallbackAST(code: string, filePath: string): ASTNode {
    const lines = code.split('\n');

    return {
      id: `${filePath}#root`,
      type: 'source_file',
      text: code,
      location: {
        file: filePath,
        startLine: 1,
        endLine: lines.length,
        startColumn: 0,
        endColumn: lines[lines.length - 1]?.length ?? 0,
      },
      children: [],
      metadata: {
        fallback: true,
        lineCount: lines.length,
      },
    };
  }

  /**
   * Find nodes by type(s) in AST
   */
  private findNodesByType(ast: ASTNode, types: string[]): ASTNode[] {
    const results: ASTNode[] = [];

    const visit = (node: ASTNode) => {
      if (types.includes(node.type)) {
        results.push(node);
      }
      for (const child of node.children) {
        visit(child);
      }
    };

    visit(ast);
    return results;
  }
}
