/**
 * @fileoverview Java Language Extractor
 * @module @nahisaho/musubix-security/extractors/java-extractor
 * @trace TSK-009, TSK-010, TSK-011, TSK-012
 * @trace REQ-SEC-LANG-003, REQ-SEC-CFG-001, REQ-SEC-DFG-001
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

// Tree-sitter types
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
 * Java-specific AST node types
 */
type JavaNodeType =
  | 'program'
  | 'package_declaration'
  | 'import_declaration'
  | 'class_declaration'
  | 'interface_declaration'
  | 'enum_declaration'
  | 'annotation_type_declaration'
  | 'method_declaration'
  | 'constructor_declaration'
  | 'field_declaration'
  | 'local_variable_declaration'
  | 'formal_parameter'
  | 'if_statement'
  | 'for_statement'
  | 'enhanced_for_statement'
  | 'while_statement'
  | 'do_statement'
  | 'switch_expression'
  | 'try_statement'
  | 'throw_statement'
  | 'return_statement'
  | 'break_statement'
  | 'continue_statement'
  | 'synchronized_statement'
  | 'method_invocation'
  | 'object_creation_expression'
  | 'assignment_expression'
  | 'binary_expression'
  | 'unary_expression'
  | 'cast_expression'
  | 'identifier'
  | 'type_identifier'
  | 'string_literal'
  | 'integer_literal'
  | 'floating_point_literal'
  | 'boolean_literal'
  | 'null_literal'
  | 'block'
  | 'modifiers'
  | 'annotation';

/**
 * Java framework patterns
 */
const JAVA_FRAMEWORK_PATTERNS: FrameworkModel[] = [
  // Spring MVC
  {
    id: 'java-spring-mvc',
    name: 'Spring MVC',
    language: 'java',
    sourcePatterns: [
      { pattern: '@RequestParam', type: 'user_input' },
      { pattern: '@PathVariable', type: 'user_input' },
      { pattern: '@RequestBody', type: 'user_input' },
      { pattern: '@RequestHeader', type: 'user_input' },
      { pattern: '@CookieValue', type: 'user_input' },
      { pattern: 'HttpServletRequest.getParameter', type: 'user_input' },
      { pattern: 'HttpServletRequest.getHeader', type: 'user_input' },
      { pattern: 'HttpServletRequest.getCookies', type: 'user_input' },
    ],
    sinkPatterns: [
      { pattern: 'HttpServletResponse.getWriter', type: 'xss' },
      { pattern: 'ModelAndView', type: 'xss' },
      { pattern: 'ResponseEntity', type: 'xss' },
      { pattern: 'response.sendRedirect', type: 'open_redirect' },
    ],
    sanitizerPatterns: [
      { pattern: 'HtmlUtils.htmlEscape', type: 'xss' },
      { pattern: '@Valid', type: 'validation' },
      { pattern: '@Validated', type: 'validation' },
    ],
  },
  // JDBC
  {
    id: 'java-jdbc',
    name: 'JDBC',
    language: 'java',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'Statement.executeQuery', type: 'sql_injection' },
      { pattern: 'Statement.executeUpdate', type: 'sql_injection' },
      { pattern: 'Statement.execute', type: 'sql_injection' },
      { pattern: 'Connection.prepareStatement', type: 'sql_injection' },
    ],
    sanitizerPatterns: [
      { pattern: 'PreparedStatement.setString', type: 'sql_injection' },
      { pattern: 'PreparedStatement.setInt', type: 'sql_injection' },
    ],
  },
  // JPA/Hibernate
  {
    id: 'java-jpa',
    name: 'JPA/Hibernate',
    language: 'java',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'createQuery', type: 'sql_injection' },
      { pattern: 'createNativeQuery', type: 'sql_injection' },
    ],
    sanitizerPatterns: [
      { pattern: 'setParameter', type: 'sql_injection' },
    ],
  },
  // Runtime.exec
  {
    id: 'java-runtime',
    name: 'Runtime',
    language: 'java',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'Runtime.getRuntime().exec', type: 'command_injection' },
      { pattern: 'ProcessBuilder', type: 'command_injection' },
    ],
    sanitizerPatterns: [],
  },
  // File I/O
  {
    id: 'java-file-io',
    name: 'File I/O',
    language: 'java',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'new File', type: 'path_traversal' },
      { pattern: 'new FileInputStream', type: 'path_traversal' },
      { pattern: 'new FileOutputStream', type: 'path_traversal' },
      { pattern: 'Files.read', type: 'path_traversal' },
      { pattern: 'Files.write', type: 'path_traversal' },
      { pattern: 'Paths.get', type: 'path_traversal' },
    ],
    sanitizerPatterns: [
      { pattern: 'getCanonicalPath', type: 'path_traversal' },
      { pattern: 'normalize', type: 'path_traversal' },
    ],
  },
  // XML parsing
  {
    id: 'java-xml',
    name: 'XML Parsing',
    language: 'java',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'DocumentBuilderFactory.newInstance', type: 'xxe' },
      { pattern: 'SAXParserFactory.newInstance', type: 'xxe' },
      { pattern: 'XMLInputFactory.newInstance', type: 'xxe' },
    ],
    sanitizerPatterns: [
      { pattern: 'setFeature.*disallow-doctype-decl', type: 'xxe' },
      { pattern: 'setFeature.*external-general-entities', type: 'xxe' },
    ],
  },
  // Serialization
  {
    id: 'java-serialization',
    name: 'Serialization',
    language: 'java',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'ObjectInputStream.readObject', type: 'deserialization' },
      { pattern: 'XMLDecoder.readObject', type: 'deserialization' },
    ],
    sanitizerPatterns: [
      { pattern: 'ObjectInputFilter', type: 'deserialization' },
    ],
  },
  // Logging
  {
    id: 'java-logging',
    name: 'Logging',
    language: 'java',
    sourcePatterns: [],
    sinkPatterns: [
      { pattern: 'Logger.info', type: 'log_injection' },
      { pattern: 'Logger.warn', type: 'log_injection' },
      { pattern: 'Logger.error', type: 'log_injection' },
      { pattern: 'Logger.debug', type: 'log_injection' },
      { pattern: 'System.out.println', type: 'log_injection' },
    ],
    sanitizerPatterns: [],
  },
];

/**
 * Java language extractor implementation
 */
export class JavaExtractor extends BaseExtractor {
  private parser: TreeSitterParser | null = null;
  private tree: TreeSitterTree | null = null;
  private nodeIdCounter = 0;
  private blockIdCounter = 0;

  /**
   * Create a new Java extractor
   */
  constructor(options?: ExtractorOptions) {
    super('java', options);
    this.frameworkModels = JAVA_FRAMEWORK_PATTERNS;
  }

  /**
   * Initialize tree-sitter parser
   */
  protected async initParser(): Promise<void> {
    if (this.parser) return;

    try {
      const Parser = (await import('tree-sitter')).default;
      const Java = (await import('tree-sitter-java')).default;

      this.parser = new Parser();
      this.parser.setLanguage(Java);
    } catch {
      this.parser = null;
    }
  }

  /**
   * Parse Java source code into AST
   */
  async parseAST(code: string, filePath: string): Promise<ASTNode> {
    await this.initParser();

    if (this.parser) {
      this.tree = this.parser.parse(code);
      return this.convertTreeSitterNode(this.tree.rootNode, filePath);
    }

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
      type: node.type as JavaNodeType,
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
      case 'class_declaration':
      case 'interface_declaration':
      case 'enum_declaration': {
        const nameNode = node.childForFieldName('name');
        const superclass = node.childForFieldName('superclass');
        const interfaces = node.childForFieldName('interfaces');
        const modifiers = node.childForFieldName('modifiers');

        metadata.name = nameNode?.text;
        metadata.superclass = superclass?.text;
        metadata.interfaces = interfaces?.namedChildren.map((i) => i.text);
        metadata.modifiers = this.extractModifiers(modifiers);
        metadata.annotations = this.extractAnnotations(node);
        break;
      }

      case 'method_declaration':
      case 'constructor_declaration': {
        const nameNode = node.childForFieldName('name');
        const paramsNode = node.childForFieldName('parameters');
        const returnType = node.childForFieldName('type');
        const modifiers = node.childForFieldName('modifiers');
        const throws = node.childForFieldName('throws');

        metadata.name = nameNode?.text;
        metadata.parameters = this.extractParameters(paramsNode);
        metadata.returnType = returnType?.text;
        metadata.modifiers = this.extractModifiers(modifiers);
        metadata.throws = throws?.namedChildren.map((t) => t.text);
        metadata.annotations = this.extractAnnotations(node);
        break;
      }

      case 'field_declaration': {
        const typeNode = node.childForFieldName('type');
        const declarators = node.namedChildren.filter(
          (c) => c.type === 'variable_declarator',
        );
        const modifiers = node.childForFieldName('modifiers');

        metadata.type = typeNode?.text;
        metadata.variables = declarators.map((d) => ({
          name: d.childForFieldName('name')?.text,
          initializer: d.childForFieldName('value')?.text,
        }));
        metadata.modifiers = this.extractModifiers(modifiers);
        break;
      }

      case 'method_invocation': {
        const objectNode = node.childForFieldName('object');
        const nameNode = node.childForFieldName('name');
        const argsNode = node.childForFieldName('arguments');

        metadata.object = objectNode?.text;
        metadata.methodName = nameNode?.text;
        metadata.argumentCount = argsNode?.namedChildCount ?? 0;
        break;
      }

      case 'object_creation_expression': {
        const typeNode = node.childForFieldName('type');
        const argsNode = node.childForFieldName('arguments');

        metadata.type = typeNode?.text;
        metadata.argumentCount = argsNode?.namedChildCount ?? 0;
        break;
      }

      case 'if_statement':
      case 'for_statement':
      case 'while_statement':
      case 'do_statement':
      case 'switch_expression':
      case 'try_statement':
        metadata.isControlFlow = true;
        break;

      case 'synchronized_statement':
        metadata.isSynchronized = true;
        break;
    }

    return metadata;
  }

  /**
   * Extract modifiers
   */
  private extractModifiers(modifiersNode: TreeSitterNode | null): string[] {
    if (!modifiersNode) return [];
    return modifiersNode.namedChildren
      .filter((c) => c.type !== 'annotation' && c.type !== 'marker_annotation')
      .map((c) => c.text);
  }

  /**
   * Extract annotations
   */
  private extractAnnotations(
    node: TreeSitterNode,
  ): Array<{ name: string; arguments?: string }> {
    const modifiers = node.childForFieldName('modifiers');
    if (!modifiers) return [];

    return modifiers.namedChildren
      .filter((c) => c.type === 'annotation' || c.type === 'marker_annotation')
      .map((a) => {
        const nameNode = a.childForFieldName('name');
        const argsNode = a.childForFieldName('arguments');
        return {
          name: nameNode?.text ?? a.text.replace('@', ''),
          arguments: argsNode?.text,
        };
      });
  }

  /**
   * Extract method parameters
   */
  private extractParameters(
    paramsNode: TreeSitterNode | null,
  ): Array<{ name: string; type: string; annotations?: string[] }> {
    if (!paramsNode) return [];

    return paramsNode.namedChildren
      .filter((c) => c.type === 'formal_parameter' || c.type === 'spread_parameter')
      .map((param) => {
        const nameNode = param.childForFieldName('name');
        const typeNode = param.childForFieldName('type');
        const modifiers = param.childForFieldName('modifiers');

        return {
          name: nameNode?.text ?? '',
          type: typeNode?.text ?? 'Object',
          annotations: this.extractAnnotations(param).map((a) => a.name),
        };
      });
  }

  /**
   * Build control flow graph
   */
  async buildCFG(ast: ASTNode): Promise<ControlFlowGraph> {
    const blocks: BasicBlock[] = [];
    const edges: CFGEdge[] = [];

    // Find all methods
    const methods = this.findNodesByType(ast, [
      'method_declaration',
      'constructor_declaration',
    ]);

    for (const method of methods) {
      const methodCFG = this.buildMethodCFG(method);
      blocks.push(...methodCFG.blocks);
      edges.push(...methodCFG.edges);
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
   * Build CFG for a single method
   */
  private buildMethodCFG(method: ASTNode): { blocks: BasicBlock[]; edges: CFGEdge[] } {
    const blocks: BasicBlock[] = [];
    const edges: CFGEdge[] = [];
    const bodyNode = method.children.find((c) => c.type === 'block');

    if (!bodyNode) {
      return { blocks, edges };
    }

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
        if (currentBlock && currentBlock.statements.length > 0) {
          blocks.push(currentBlock);
        }

        const cfResult = this.processControlFlow(stmt);
        blocks.push(...cfResult.blocks);
        edges.push(...cfResult.edges);

        currentBlock = null;
      } else {
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
      'enhanced_for_statement',
      'while_statement',
      'do_statement',
      'switch_expression',
      'try_statement',
      'return_statement',
      'throw_statement',
      'break_statement',
      'continue_statement',
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
        const condBlock: BasicBlock = {
          id: `${stmt.location.file}#if_cond_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [],
        };
        blocks.push(condBlock);

        // Process then branch
        const consequence = stmt.children.find((c) => c.type === 'block');
        if (consequence) {
          const { blocks: thenBlocks, edges: thenEdges } = this.processBlock(consequence);
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
        const alternative = stmt.children.filter((c) => c.type === 'block')[1];
        if (alternative) {
          const { blocks: elseBlocks, edges: elseEdges } = this.processBlock(alternative);
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

      case 'for_statement':
      case 'enhanced_for_statement':
      case 'while_statement': {
        const headerBlock: BasicBlock = {
          id: `${stmt.location.file}#loop_header_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [],
        };
        blocks.push(headerBlock);

        const bodyBlock = stmt.children.find((c) => c.type === 'block');
        if (bodyBlock) {
          const { blocks: bodyBlocks, edges: bodyEdges } = this.processBlock(bodyBlock);
          blocks.push(...bodyBlocks);
          edges.push(...bodyEdges);

          if (bodyBlocks.length > 0) {
            headerBlock.successors.push(bodyBlocks[0].id);
            bodyBlocks[0].predecessors.push(headerBlock.id);
            edges.push({
              from: headerBlock.id,
              to: bodyBlocks[0].id,
              type: 'conditional',
              condition: 'true',
            });

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

      case 'try_statement': {
        const tryBlock: BasicBlock = {
          id: `${stmt.location.file}#try_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [],
        };
        blocks.push(tryBlock);

        // Process try body
        const tryBody = stmt.children.find((c) => c.type === 'block');
        if (tryBody) {
          const { blocks: tryBlocks, edges: tryEdges } = this.processBlock(tryBody);
          blocks.push(...tryBlocks);
          edges.push(...tryEdges);

          if (tryBlocks.length > 0) {
            tryBlock.successors.push(tryBlocks[0].id);
            tryBlocks[0].predecessors.push(tryBlock.id);
            edges.push({
              from: tryBlock.id,
              to: tryBlocks[0].id,
              type: 'sequential',
            });
          }
        }

        // Process catch clauses
        const catchClauses = stmt.children.filter((c) => c.type === 'catch_clause');
        for (const catchClause of catchClauses) {
          const catchBody = catchClause.children.find((c) => c.type === 'block');
          if (catchBody) {
            const { blocks: catchBlocks, edges: catchEdges } = this.processBlock(catchBody);
            blocks.push(...catchBlocks);
            edges.push(...catchEdges);

            if (catchBlocks.length > 0) {
              tryBlock.successors.push(catchBlocks[0].id);
              catchBlocks[0].predecessors.push(tryBlock.id);
              edges.push({
                from: tryBlock.id,
                to: catchBlocks[0].id,
                type: 'exception',
              });
            }
          }
        }

        // Process finally
        const finallyClause = stmt.children.find((c) => c.type === 'finally_clause');
        if (finallyClause) {
          const finallyBody = finallyClause.children.find((c) => c.type === 'block');
          if (finallyBody) {
            const { blocks: finallyBlocks, edges: finallyEdges } = this.processBlock(finallyBody);
            blocks.push(...finallyBlocks);
            edges.push(...finallyEdges);
          }
        }
        break;
      }

      case 'return_statement':
      case 'throw_statement': {
        const block: BasicBlock = {
          id: `${stmt.location.file}#${stmt.type}_${this.blockIdCounter++}`,
          statements: [stmt.id],
          predecessors: [],
          successors: [],
        };
        blocks.push(block);
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

    // Process all variable declarations
    const varDecls = this.findNodesByType(ast, [
      'local_variable_declaration',
      'field_declaration',
    ]);

    for (const decl of varDecls) {
      const dfgNodes = this.createDFGNodesForDeclaration(decl, nodeMap);
      nodes.push(...dfgNodes);
    }

    // Process method parameters
    const methods = this.findNodesByType(ast, [
      'method_declaration',
      'constructor_declaration',
    ]);

    for (const method of methods) {
      const paramNodes = this.createDFGNodesForParameters(method, nodeMap);
      nodes.push(...paramNodes);
    }

    // Build edges
    edges.push(...this.buildDFGEdges(nodes, nodeMap));

    return { nodes, edges };
  }

  /**
   * Create DFG nodes for variable declaration
   */
  private createDFGNodesForDeclaration(
    decl: ASTNode,
    nodeMap: Map<string, DFGNode>,
  ): DFGNode[] {
    const nodes: DFGNode[] = [];
    const variables = decl.metadata?.variables as Array<{ name: string; initializer?: string }> | undefined;

    if (variables) {
      for (const v of variables) {
        if (v.name) {
          const node: DFGNode = {
            id: `dfg_${decl.id}_${v.name}`,
            astNodeId: decl.id,
            variable: v.name,
            operation: 'write',
            location: decl.location,
            predecessors: [],
            successors: [],
          };
          nodes.push(node);
          nodeMap.set(v.name, node);
        }
      }
    }

    return nodes;
  }

  /**
   * Create DFG nodes for method parameters
   */
  private createDFGNodesForParameters(
    method: ASTNode,
    nodeMap: Map<string, DFGNode>,
  ): DFGNode[] {
    const nodes: DFGNode[] = [];
    const params = method.metadata?.parameters as Array<{ name: string; type: string; annotations?: string[] }> | undefined;
    const annotations = method.metadata?.annotations as Array<{ name: string }> | undefined;

    if (params) {
      for (const param of params) {
        const node: DFGNode = {
          id: `dfg_param_${method.id}_${param.name}`,
          astNodeId: method.id,
          variable: param.name,
          operation: 'param',
          location: method.location,
          predecessors: [],
          successors: [],
          taintLabel: this.inferTaintLabel(param, annotations),
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
  private inferTaintLabel(
    param: { name: string; type: string; annotations?: string[] },
    methodAnnotations?: Array<{ name: string }>,
  ): string | undefined {
    // Check parameter annotations
    if (param.annotations) {
      if (param.annotations.some((a) =>
        ['RequestParam', 'PathVariable', 'RequestBody', 'RequestHeader', 'CookieValue'].includes(a),
      )) {
        return 'user_input';
      }
    }

    // Check if it's a servlet request
    if (param.type.includes('HttpServletRequest')) {
      return 'user_input';
    }

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
    const packageNode = this.findNodesByType(ast, ['package_declaration'])[0];
    const packageName = packageNode?.children[0]?.text ?? 'default';

    // Process imports
    const importNodes = this.findNodesByType(ast, ['import_declaration']);
    for (const importDecl of importNodes) {
      const importPath = importDecl.text.replace(/import\s+(static\s+)?/, '').replace(';', '').trim();
      const alias = importPath.split('.').pop() ?? importPath;
      global.set(alias, {
        name: alias,
        kind: 'import',
        type: importPath,
        location: importDecl.location,
        scope: 'global',
      });
    }

    // Process classes
    const classes = this.findNodesByType(ast, [
      'class_declaration',
      'interface_declaration',
      'enum_declaration',
    ]);

    for (const cls of classes) {
      const name = cls.metadata?.name as string;
      const modifiers = cls.metadata?.modifiers as string[] | undefined;

      if (name) {
        global.set(name, {
          name,
          kind: 'class',
          type: cls.type.replace('_declaration', ''),
          location: cls.location,
          scope: 'global',
          exported: modifiers?.includes('public'),
          modifiers,
        });

        // Create class scope with methods and fields
        const classScope: Map<string, SymbolEntry> = new Map();

        // Process fields
        const fields = this.findNodesByType(cls, ['field_declaration']);
        for (const field of fields) {
          const variables = field.metadata?.variables as Array<{ name: string }> | undefined;
          const fieldType = field.metadata?.type as string | undefined;
          const fieldModifiers = field.metadata?.modifiers as string[] | undefined;

          if (variables) {
            for (const v of variables) {
              if (v.name) {
                classScope.set(v.name, {
                  name: v.name,
                  kind: 'field',
                  type: fieldType ?? 'Object',
                  location: field.location,
                  scope: name,
                  modifiers: fieldModifiers,
                });
              }
            }
          }
        }

        // Process methods
        const methods = this.findNodesByType(cls, [
          'method_declaration',
          'constructor_declaration',
        ]);

        for (const method of methods) {
          const methodName = method.metadata?.name as string;
          const params = method.metadata?.parameters as Array<{ type: string }> | undefined;
          const returnType = method.metadata?.returnType as string | undefined;
          const methodModifiers = method.metadata?.modifiers as string[] | undefined;

          if (methodName) {
            const signature = `${methodName}(${params?.map((p) => p.type).join(',') ?? ''})`;
            classScope.set(signature, {
              name: methodName,
              kind: 'method',
              type: `(${params?.map((p) => p.type).join(', ') ?? ''}) -> ${returnType ?? 'void'}`,
              location: method.location,
              scope: name,
              exported: methodModifiers?.includes('public'),
              modifiers: methodModifiers,
            });
          }
        }

        scopes.push({ scopeId: name, symbols: classScope });
      }
    }

    return {
      global,
      scopes,
      packageName,
    };
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

    // Check annotations in classes/methods
    const annotations = new Set<string>();
    const allAnnotations = this.findAnnotationsInAST(ast);
    allAnnotations.forEach((a) => annotations.add(a));

    // Check against framework patterns
    for (const framework of this.frameworkModels) {
      let matched = false;

      switch (framework.id) {
        case 'java-spring-mvc':
          matched =
            imports.has('org.springframework.web.bind.annotation.*') ||
            imports.has('org.springframework.stereotype.Controller') ||
            annotations.has('Controller') ||
            annotations.has('RestController') ||
            annotations.has('RequestMapping');
          break;

        case 'java-jdbc':
          matched =
            imports.has('java.sql.*') ||
            imports.has('java.sql.Connection') ||
            imports.has('java.sql.Statement');
          break;

        case 'java-jpa':
          matched =
            imports.has('javax.persistence.*') ||
            imports.has('jakarta.persistence.*') ||
            annotations.has('Entity') ||
            annotations.has('Query');
          break;

        case 'java-runtime':
          matched = imports.has('java.lang.Runtime') || imports.has('java.lang.ProcessBuilder');
          break;

        case 'java-file-io':
          matched =
            imports.has('java.io.*') ||
            imports.has('java.io.File') ||
            imports.has('java.nio.file.*');
          break;

        case 'java-xml':
          matched =
            imports.has('javax.xml.parsers.*') ||
            imports.has('org.xml.sax.*') ||
            imports.has('javax.xml.stream.*');
          break;

        case 'java-serialization':
          matched =
            imports.has('java.io.ObjectInputStream') ||
            imports.has('java.beans.XMLDecoder');
          break;

        case 'java-logging':
          matched =
            imports.has('org.slf4j.*') ||
            imports.has('java.util.logging.*') ||
            imports.has('org.apache.log4j.*');
          break;
      }

      if (matched) {
        detected.push(framework);
      }
    }

    return detected;
  }

  /**
   * Find all annotations in AST
   */
  private findAnnotationsInAST(ast: ASTNode): string[] {
    const annotations: string[] = [];

    const visit = (node: ASTNode) => {
      if (node.metadata?.annotations) {
        const nodeAnnotations = node.metadata.annotations as Array<{ name: string }>;
        annotations.push(...nodeAnnotations.map((a) => a.name));
      }
      for (const child of node.children) {
        visit(child);
      }
    };

    visit(ast);
    return annotations;
  }

  /**
   * Create fallback AST
   */
  private createFallbackAST(code: string, filePath: string): ASTNode {
    const lines = code.split('\n');

    return {
      id: `${filePath}#root`,
      type: 'program',
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
