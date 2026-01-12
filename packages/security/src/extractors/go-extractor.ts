/**
 * @fileoverview Go Language Extractor
 * @module @nahisaho/musubix-security/extractors/go-extractor
 * @trace TSK-GO-001, TSK-GO-002, TSK-GO-003, TSK-GO-004, TSK-GO-005
 * @trace REQ-SEC-GO-001, REQ-SEC-GO-002, REQ-SEC-GO-003, REQ-SEC-GO-004
 * @trace REQ-SEC-GO-005, REQ-SEC-GO-006, REQ-SEC-GO-007, REQ-SEC-GO-008
 */

import {
  BaseExtractor,
  type ASTNode,
  type ASTEdge,
  type DFGNode,
  type DFGEdge,
  type DataFlowGraph,
  type BasicBlock,
  type CFGEdge,
  type ControlFlowGraph,
  type SymbolTable,
  type Symbol,
  type FunctionSymbol,
  type ClassSymbol,
  type ScopeInfo,
  type FrameworkModel,
  type SupportedLanguage,
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
 * Go framework models with proper FrameworkModel interface
 * @trace REQ-SEC-GO-004
 */
const GO_FRAMEWORK_MODELS: FrameworkModel[] = [
  // net/http (Standard Library HTTP Server)
  {
    name: 'net/http',
    languages: ['go'],
    sources: [
      { pattern: /r\.URL\.Query\(\)/, type: 'user_input', description: 'URL query parameters', taintLabel: 'user_input' },
      { pattern: /r\.FormValue\(/, type: 'user_input', description: 'Form value access', taintLabel: 'user_input' },
      { pattern: /r\.PostFormValue\(/, type: 'user_input', description: 'POST form value', taintLabel: 'user_input' },
      { pattern: /r\.Header\.Get\(/, type: 'user_input', description: 'HTTP header access', taintLabel: 'user_input' },
      { pattern: /r\.Body/, type: 'user_input', description: 'Request body', taintLabel: 'user_input' },
      { pattern: /r\.Cookies\(\)/, type: 'user_input', description: 'Cookie access', taintLabel: 'user_input' },
    ],
    sinks: [
      { pattern: /fmt\.Fprintf\(w,/, type: 'xss', vulnerabilityType: 'xss', severity: 'high' },
      { pattern: /w\.Write\(/, type: 'xss', vulnerabilityType: 'xss', severity: 'high' },
      { pattern: /http\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
    ],
    sanitizers: [
      { pattern: /html\.EscapeString\(/, sanitizes: ['xss'] },
      { pattern: /template\.HTMLEscapeString\(/, sanitizes: ['xss'] },
    ],
  },

  // database/sql (Standard Library Database)
  {
    name: 'database/sql',
    languages: ['go'],
    sources: [],
    sinks: [
      { pattern: /db\.Query\([^,)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /db\.QueryRow\([^,)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /db\.Exec\([^,)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /db\.Prepare\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /fmt\.Sprintf\([^)]*SELECT/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    ],
    sanitizers: [
      { pattern: /db\.Query\([^,]+,\s*\w+\)/, sanitizes: ['sql_injection'] },
      { pattern: /db\.QueryRow\([^,]+,\s*\w+\)/, sanitizes: ['sql_injection'] },
    ],
  },

  // os/exec (Command Execution)
  {
    name: 'os/exec',
    languages: ['go'],
    sources: [
      { pattern: /os\.Args/, type: 'user_input', description: 'Command line arguments', taintLabel: 'user_input' },
      { pattern: /os\.Getenv\(/, type: 'user_input', description: 'Environment variable', taintLabel: 'env_input' },
    ],
    sinks: [
      { pattern: /exec\.Command\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
      { pattern: /exec\.CommandContext\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
    ],
    sanitizers: [],
  },

  // os (File Operations)
  {
    name: 'os',
    languages: ['go'],
    sources: [],
    sinks: [
      { pattern: /os\.Open\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /os\.OpenFile\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /os\.Create\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /os\.ReadFile\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /os\.WriteFile\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /ioutil\.ReadFile\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    ],
    sanitizers: [
      { pattern: /filepath\.Clean\(/, sanitizes: ['path_traversal'] },
      { pattern: /filepath\.Base\(/, sanitizes: ['path_traversal'] },
    ],
  },

  // encoding/xml (XML Processing)
  {
    name: 'encoding/xml',
    languages: ['go'],
    sources: [],
    sinks: [
      { pattern: /xml\.Unmarshal\(/, type: 'xml', vulnerabilityType: 'xxe', severity: 'high' },
      { pattern: /xml\.NewDecoder\(/, type: 'xml', vulnerabilityType: 'xxe', severity: 'high' },
    ],
    sanitizers: [],
  },

  // Gin Framework
  {
    name: 'Gin',
    languages: ['go'],
    sources: [
      { pattern: /c\.Query\(/, type: 'user_input', description: 'Gin query parameter', taintLabel: 'user_input' },
      { pattern: /c\.Param\(/, type: 'user_input', description: 'Gin path parameter', taintLabel: 'user_input' },
      { pattern: /c\.PostForm\(/, type: 'user_input', description: 'Gin POST form', taintLabel: 'user_input' },
      { pattern: /c\.ShouldBindJSON\(/, type: 'user_input', description: 'Gin JSON binding', taintLabel: 'user_input' },
      { pattern: /c\.GetHeader\(/, type: 'user_input', description: 'Gin header access', taintLabel: 'user_input' },
      { pattern: /c\.Cookie\(/, type: 'user_input', description: 'Gin cookie access', taintLabel: 'user_input' },
    ],
    sinks: [
      { pattern: /c\.HTML\(/, type: 'xss', vulnerabilityType: 'xss', severity: 'high' },
      { pattern: /c\.String\(/, type: 'xss', vulnerabilityType: 'xss', severity: 'medium' },
      { pattern: /c\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
    ],
    sanitizers: [],
  },

  // Echo Framework
  {
    name: 'Echo',
    languages: ['go'],
    sources: [
      { pattern: /c\.QueryParam\(/, type: 'user_input', description: 'Echo query parameter', taintLabel: 'user_input' },
      { pattern: /c\.Param\(/, type: 'user_input', description: 'Echo path parameter', taintLabel: 'user_input' },
      { pattern: /c\.FormValue\(/, type: 'user_input', description: 'Echo form value', taintLabel: 'user_input' },
      { pattern: /c\.Bind\(/, type: 'user_input', description: 'Echo request binding', taintLabel: 'user_input' },
      { pattern: /c\.Request\(\)\.Header\.Get\(/, type: 'user_input', description: 'Echo header access', taintLabel: 'user_input' },
    ],
    sinks: [
      { pattern: /c\.HTML\(/, type: 'xss', vulnerabilityType: 'xss', severity: 'high' },
      { pattern: /c\.String\(/, type: 'xss', vulnerabilityType: 'xss', severity: 'medium' },
      { pattern: /c\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
    ],
    sanitizers: [],
  },

  // Fiber Framework
  {
    name: 'Fiber',
    languages: ['go'],
    sources: [
      { pattern: /c\.Query\(/, type: 'user_input', description: 'Fiber query parameter', taintLabel: 'user_input' },
      { pattern: /c\.Params\(/, type: 'user_input', description: 'Fiber path parameter', taintLabel: 'user_input' },
      { pattern: /c\.FormValue\(/, type: 'user_input', description: 'Fiber form value', taintLabel: 'user_input' },
      { pattern: /c\.BodyParser\(/, type: 'user_input', description: 'Fiber body parser', taintLabel: 'user_input' },
      { pattern: /c\.Get\(/, type: 'user_input', description: 'Fiber header access', taintLabel: 'user_input' },
    ],
    sinks: [
      { pattern: /c\.SendString\(/, type: 'xss', vulnerabilityType: 'xss', severity: 'medium' },
      { pattern: /c\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
    ],
    sanitizers: [],
  },

  // GORM ORM
  {
    name: 'GORM',
    languages: ['go'],
    sources: [],
    sinks: [
      { pattern: /db\.Raw\(/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /db\.Exec\(/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /db\.Where\([^,)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    ],
    sanitizers: [
      { pattern: /db\.Where\([^,]+,\s*\w+\)/, sanitizes: ['sql_injection'] },
    ],
  },

  // Go SSRF vulnerabilities
  {
    name: 'Go SSRF',
    languages: ['go'],
    sources: [],
    sinks: [
      { pattern: /http\.Get\(/, type: 'ssrf', vulnerabilityType: 'ssrf', severity: 'high' },
      { pattern: /http\.Post\(/, type: 'ssrf', vulnerabilityType: 'ssrf', severity: 'high' },
      { pattern: /http\.NewRequest\(/, type: 'ssrf', vulnerabilityType: 'ssrf', severity: 'high' },
      { pattern: /client\.Do\(/, type: 'ssrf', vulnerabilityType: 'ssrf', severity: 'high' },
    ],
    sanitizers: [
      { pattern: /url\.Parse\(/, sanitizes: ['ssrf'] },
    ],
  },
];

/**
 * Check if a Go identifier is exported (starts with uppercase)
 * @param name The identifier name to check
 * @returns true if exported, false otherwise
 */
function isExported(name: string): boolean {
  if (!name || name.length === 0) return false;
  const firstChar = name.charAt(0);
  return firstChar >= 'A' && firstChar <= 'Z';
}

/**
 * Go Language Extractor
 * @trace TSK-GO-001, REQ-SEC-GO-001
 */
export class GoExtractor extends BaseExtractor {
  readonly language: SupportedLanguage = 'go';
  readonly extensions: string[] = ['.go'];

  private parser: TreeSitterParser | null = null;
  private tree: TreeSitterTree | null = null;
  private nodeIdCounter = 0;
  private blockIdCounter = 0;

  /**
   * Get framework models for Go
   * @trace REQ-SEC-GO-004
   */
  getFrameworkModels(): FrameworkModel[] {
    return GO_FRAMEWORK_MODELS;
  }

  /**
   * Initialize tree-sitter parser
   * @trace REQ-SEC-GO-002
   */
  private async initParser(): Promise<void> {
    if (this.parser) return;

    try {
      const Parser = (await import('tree-sitter')).default;
      const Go = (await import('tree-sitter-go')).default;

      this.parser = new Parser();
      this.parser.setLanguage(Go);
    } catch {
      // tree-sitter-go not available, use fallback
      this.parser = null;
    }
  }

  /**
   * Build AST from source code
   * @trace TSK-GO-002, REQ-SEC-GO-002
   */
  protected async buildAST(
    source: string,
    filePath: string
  ): Promise<{ ast: ASTNode; astNodes: Map<string, ASTNode>; astEdges: ASTEdge[] }> {
    await this.initParser();

    this.nodeIdCounter = 0;
    const astNodes = new Map<string, ASTNode>();
    const astEdges: ASTEdge[] = [];

    let ast: ASTNode;

    if (this.parser) {
      this.tree = this.parser.parse(source);
      ast = this.convertTreeSitterNode(this.tree.rootNode, filePath, astNodes, astEdges);
    } else {
      ast = this.createFallbackAST(source, filePath, astNodes);
    }

    return { ast, astNodes, astEdges };
  }

  /**
   * Convert tree-sitter node to AST format
   */
  private convertTreeSitterNode(
    node: TreeSitterNode,
    filePath: string,
    astNodes: Map<string, ASTNode>,
    astEdges: ASTEdge[]
  ): ASTNode {
    const id = `${filePath}#${this.nodeIdCounter++}`;
    const childIds: string[] = [];

    for (const child of node.namedChildren) {
      const childNode = this.convertTreeSitterNode(child, filePath, astNodes, astEdges);
      childIds.push(childNode.id);
      astEdges.push({
        from: id,
        to: childNode.id,
        label: 'child',
      });
    }

    const astNode: ASTNode = {
      id,
      type: node.type,
      text: node.text,
      location: {
        file: filePath,
        startLine: node.startPosition.row + 1,
        endLine: node.endPosition.row + 1,
        startColumn: node.startPosition.column,
        endColumn: node.endPosition.column,
      },
      properties: this.extractNodeProperties(node),
      children: childIds,
      metadata: {},
    };

    astNodes.set(id, astNode);
    return astNode;
  }

  /**
   * Extract properties from node
   * @trace REQ-SEC-GO-003
   */
  private extractNodeProperties(node: TreeSitterNode): Record<string, unknown> {
    const props: Record<string, unknown> = {};

    switch (node.type) {
      case 'function_declaration': {
        const nameNode = node.childForFieldName('name');
        const paramsNode = node.childForFieldName('parameters');
        const resultNode = node.childForFieldName('result');
        const name = nameNode?.text;
        props.name = name;
        props.parameters = paramsNode?.namedChildren.map((p) => p.text) ?? [];
        props.returnType = resultNode?.text;
        props.isExported = name ? isExported(name) : false;
        break;
      }

      case 'method_declaration': {
        const nameNode = node.childForFieldName('name');
        const receiverNode = node.childForFieldName('receiver');
        const paramsNode = node.childForFieldName('parameters');
        const resultNode = node.childForFieldName('result');
        const name = nameNode?.text;
        props.name = name;
        props.receiver = receiverNode?.text;
        props.parameters = paramsNode?.namedChildren.map((p) => p.text) ?? [];
        props.returnType = resultNode?.text;
        props.isExported = name ? isExported(name) : false;
        break;
      }

      case 'type_declaration': {
        const specNode = node.namedChildren[0];
        if (specNode?.type === 'type_spec') {
          const nameNode = specNode.childForFieldName('name');
          const typeNode = specNode.childForFieldName('type');
          const name = nameNode?.text;
          props.name = name;
          props.underlyingType = typeNode?.type;
          props.isExported = name ? isExported(name) : false;
        }
        break;
      }

      case 'struct_type': {
        const fields: Array<{ name: string; type: string; tag?: string }> = [];
        for (const fieldDecl of node.namedChildren) {
          if (fieldDecl.type === 'field_declaration') {
            const fieldNameNode = fieldDecl.childForFieldName('name');
            const fieldTypeNode = fieldDecl.childForFieldName('type');
            const tagNode = fieldDecl.namedChildren.find((n) => n.type === 'raw_string_literal');
            fields.push({
              name: fieldNameNode?.text ?? '',
              type: fieldTypeNode?.text ?? '',
              tag: tagNode?.text,
            });
          }
        }
        props.fields = fields;
        break;
      }

      case 'interface_type': {
        const methods: string[] = [];
        for (const methodSpec of node.namedChildren) {
          if (methodSpec.type === 'method_spec') {
            const methodNameNode = methodSpec.childForFieldName('name');
            if (methodNameNode) {
              methods.push(methodNameNode.text);
            }
          }
        }
        props.methods = methods;
        break;
      }

      case 'call_expression': {
        const functionNode = node.childForFieldName('function');
        const argsNode = node.childForFieldName('arguments');
        props.functionName = functionNode?.text;
        props.argumentCount = argsNode?.namedChildCount ?? 0;
        break;
      }

      case 'selector_expression': {
        const operandNode = node.childForFieldName('operand');
        const fieldNode = node.childForFieldName('field');
        props.operand = operandNode?.text;
        props.field = fieldNode?.text;
        break;
      }

      case 'short_var_declaration':
      case 'var_declaration':
      case 'assignment_statement': {
        const leftNode = node.childForFieldName('left');
        const rightNode = node.childForFieldName('right');
        props.left = leftNode?.text;
        props.right = rightNode?.text;
        break;
      }

      case 'package_clause': {
        const pkgNameNode = node.childForFieldName('name');
        props.packageName = pkgNameNode?.text;
        break;
      }

      case 'import_declaration': {
        const specs: string[] = [];
        for (const child of node.namedChildren) {
          if (child.type === 'import_spec' || child.type === 'import_spec_list') {
            const pathNode = child.childForFieldName('path') ?? child;
            specs.push(pathNode.text.replace(/"/g, ''));
          }
        }
        props.imports = specs;
        break;
      }

      case 'if_statement':
        props.hasElse = node.namedChildren.some((n) => n.type === 'block' && n !== node.namedChildren[0]);
        break;

      case 'for_statement':
        props.hasRange = node.text.includes('range');
        break;

      case 'switch_statement':
      case 'type_switch_statement':
        props.caseCount = node.namedChildren.filter((n) => n.type === 'expression_case' || n.type === 'type_case').length;
        break;

      case 'go_statement':
        props.isGoroutine = true;
        break;

      case 'defer_statement':
        props.isDeferred = true;
        break;

      case 'select_statement':
        props.caseCount = node.namedChildren.filter((n) => n.type === 'communication_case').length;
        break;
    }

    return props;
  }

  /**
   * Create fallback AST when tree-sitter is unavailable
   */
  private createFallbackAST(
    source: string,
    filePath: string,
    astNodes: Map<string, ASTNode>
  ): ASTNode {
    const lines = source.split('\n');
    const id = `${filePath}#root`;

    const ast: ASTNode = {
      id,
      type: 'source_file',
      text: source,
      location: {
        file: filePath,
        startLine: 1,
        endLine: lines.length,
        startColumn: 0,
        endColumn: lines[lines.length - 1]?.length ?? 0,
      },
      properties: { fallback: true, lineCount: lines.length },
      children: [],
      metadata: {},
    };

    astNodes.set(id, ast);
    return ast;
  }

  /**
   * Build Data Flow Graph
   * @trace TSK-GO-003, REQ-SEC-GO-005
   */
  protected async buildDFG(
    astNodes: Map<string, ASTNode>,
    _astEdges: ASTEdge[],
    frameworkModels: FrameworkModel[]
  ): Promise<DataFlowGraph> {
    const nodes = new Map<string, DFGNode>();
    const edges: DFGEdge[] = [];
    const sources: string[] = [];
    const sinks: string[] = [];

    const models = frameworkModels.length > 0 ? frameworkModels : GO_FRAMEWORK_MODELS;

    for (const [_nodeId, astNode] of astNodes) {
      if (!astNode.text) continue;

      // Check for sources
      for (const model of models) {
        for (const source of model.sources) {
          if (source.pattern.test(astNode.text)) {
            const dfgId = `dfg_source_${astNode.id}`;
            nodes.set(dfgId, {
              id: dfgId,
              astNodeId: astNode.id,
              nodeType: 'source',
              taintLabel: source.taintLabel,
              expression: astNode.text,
              location: astNode.location,
              properties: { sourceType: source.type, framework: model.name },
            });
            sources.push(dfgId);
          }
        }

        // Check for sinks
        for (const sink of model.sinks) {
          if (sink.pattern.test(astNode.text)) {
            const dfgId = `dfg_sink_${astNode.id}`;
            nodes.set(dfgId, {
              id: dfgId,
              astNodeId: astNode.id,
              nodeType: 'sink',
              expression: astNode.text,
              location: astNode.location,
              properties: {
                sinkType: sink.type,
                vulnerabilityType: sink.vulnerabilityType,
                severity: sink.severity,
                framework: model.name,
              },
            });
            sinks.push(dfgId);
          }
        }

        // Check for sanitizers
        for (const sanitizer of model.sanitizers) {
          if (sanitizer.pattern.test(astNode.text)) {
            const dfgId = `dfg_sanitizer_${astNode.id}`;
            nodes.set(dfgId, {
              id: dfgId,
              astNodeId: astNode.id,
              nodeType: 'sanitizer',
              expression: astNode.text,
              location: astNode.location,
              properties: { sanitizes: sanitizer.sanitizes, framework: model.name },
            });
          }
        }
      }

      // Handle variable declarations and assignments
      if (
        astNode.type === 'short_var_declaration' ||
        astNode.type === 'var_declaration' ||
        astNode.type === 'assignment_statement'
      ) {
        const dfgId = `dfg_assign_${astNode.id}`;
        nodes.set(dfgId, {
          id: dfgId,
          astNodeId: astNode.id,
          nodeType: 'propagator',
          variable: astNode.properties.left as string,
          operation: 'write',
          expression: astNode.text,
          location: astNode.location,
          properties: {},
        });
      }
    }

    return { nodes, edges, sources, sinks };
  }

  /**
   * Build Control Flow Graph
   * @trace TSK-GO-004, REQ-SEC-GO-006
   */
  protected async buildCFG(
    astNodes: Map<string, ASTNode>,
    _astEdges: ASTEdge[]
  ): Promise<ControlFlowGraph> {
    const blocks = new Map<string, BasicBlock>();
    const edges: CFGEdge[] = [];
    const entryBlocks: string[] = [];
    const exitBlocks: string[] = [];

    // Find functions and build CFG for each
    for (const [_nodeId, astNode] of astNodes) {
      if (astNode.type === 'function_declaration' || astNode.type === 'method_declaration') {
        const blockId = `block_${this.blockIdCounter++}`;
        blocks.set(blockId, {
          id: blockId,
          statements: [astNode.id],
          predecessors: [],
          successors: [],
        });
        entryBlocks.push(blockId);
        exitBlocks.push(blockId);
      }
    }

    // Add entry and exit blocks if none found
    if (entryBlocks.length === 0) {
      const entryId = 'entry_block';
      const exitId = 'exit_block';

      blocks.set(entryId, {
        id: entryId,
        statements: [],
        predecessors: [],
        successors: [exitId],
        isEntry: true,
      });

      blocks.set(exitId, {
        id: exitId,
        statements: [],
        predecessors: [entryId],
        successors: [],
        isExit: true,
      });

      entryBlocks.push(entryId);
      exitBlocks.push(exitId);

      edges.push({
        from: entryId,
        to: exitId,
        edgeType: 'normal',
      });
    }

    return {
      blocks,
      edges,
      entryBlocks,
      exitBlocks,
      entry: entryBlocks[0],
      exit: exitBlocks[exitBlocks.length - 1],
    };
  }

  /**
   * Extract symbols from AST
   * @trace TSK-GO-005, REQ-SEC-GO-007
   */
  protected async extractSymbols(
    astNodes: Map<string, ASTNode>
  ): Promise<SymbolTable> {
    const symbols = new Map<string, Symbol>();
    const functions = new Map<string, FunctionSymbol>();
    const classes = new Map<string, ClassSymbol>();
    const scopes = new Map<string, ScopeInfo>();

    // Package scope
    let packageName = 'main';
    for (const [, astNode] of astNodes) {
      if (astNode.type === 'package_clause' && astNode.properties.packageName) {
        packageName = astNode.properties.packageName as string;
        break;
      }
    }

    const packageScope: ScopeInfo = {
      id: packageName,
      symbols: [],
      kind: 'global',
    };
    scopes.set(packageName, packageScope);

    for (const [_nodeId, astNode] of astNodes) {
      switch (astNode.type) {
        case 'function_declaration': {
          const funcId = `func_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'anonymous';
          const params = (astNode.properties.parameters as string[]) ?? [];
          const isExp = astNode.properties.isExported as boolean ?? false;

          const funcSymbol: FunctionSymbol = {
            name,
            kind: 'function',
            location: astNode.location,
            scopeId: packageName,
            properties: {
              isExported: isExp,
            },
            parameters: params.map((p, i) => ({
              name: p,
              index: i,
            })),
            returnType: astNode.properties.returnType as string | undefined,
          };

          functions.set(funcId, funcSymbol);
          symbols.set(funcId, funcSymbol);
          packageScope.symbols.push(funcId);
          break;
        }

        case 'method_declaration': {
          const methodId = `method_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'anonymous';
          const params = (astNode.properties.parameters as string[]) ?? [];
          const receiver = astNode.properties.receiver as string | undefined;
          const isExp = astNode.properties.isExported as boolean ?? false;

          const methodSymbol: FunctionSymbol = {
            name,
            kind: 'method',
            location: astNode.location,
            scopeId: packageName,
            properties: {
              receiver,
              isExported: isExp,
            },
            parameters: params.map((p, i) => ({
              name: p,
              index: i,
            })),
            returnType: astNode.properties.returnType as string | undefined,
          };

          functions.set(methodId, methodSymbol);
          symbols.set(methodId, methodSymbol);
          packageScope.symbols.push(methodId);
          break;
        }

        case 'type_declaration': {
          const typeId = `type_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'Anonymous';
          const underlyingType = astNode.properties.underlyingType as string | undefined;
          const isExp = astNode.properties.isExported as boolean ?? false;

          if (underlyingType === 'struct_type') {
            const structSymbol: ClassSymbol = {
              name,
              kind: 'class',
              location: astNode.location,
              scopeId: packageName,
              methods: [],
              properties: [],
            };

            classes.set(typeId, structSymbol);
            const structAsSymbol: Symbol = {
              name,
              kind: 'class',
              location: astNode.location,
              scopeId: packageName,
              properties: {
                structType: true,
                isExported: isExp,
              },
            };
            symbols.set(typeId, structAsSymbol);
          } else if (underlyingType === 'interface_type') {
            const interfaceSymbol: Symbol = {
              name,
              kind: 'interface',
              location: astNode.location,
              scopeId: packageName,
              properties: {
                isExported: isExp,
              },
            };
            symbols.set(typeId, interfaceSymbol);
          } else {
            // Type alias
            const typeSymbol: Symbol = {
              name,
              kind: 'type',
              location: astNode.location,
              scopeId: packageName,
              properties: {
                underlyingType,
                isExported: isExp,
              },
            };
            symbols.set(typeId, typeSymbol);
          }
          packageScope.symbols.push(typeId);
          break;
        }

        case 'const_declaration':
        case 'var_declaration': {
          const varId = `var_${astNode.id}`;
          const name = (astNode.properties.left as string) ?? 'anonymous';
          const isConst = astNode.type === 'const_declaration';

          const varSymbol: Symbol = {
            name,
            kind: isConst ? 'constant' : 'variable',
            location: astNode.location,
            scopeId: packageName,
            properties: {
              isExported: isExported(name),
            },
          };

          symbols.set(varId, varSymbol);
          packageScope.symbols.push(varId);
          break;
        }
      }
    }

    return {
      symbols,
      functions,
      classes,
      scopes,
      global: symbols,
    };
  }

  /**
   * Check if identifier is exported (public)
   * Go exports identifiers starting with uppercase
   */
  isExported(name: string): boolean {
    return isExported(name);
  }
}

/**
 * Create Go extractor instance
 * @trace REQ-SEC-GO-001
 */
export function createGoExtractor(): GoExtractor {
  return new GoExtractor();
}
