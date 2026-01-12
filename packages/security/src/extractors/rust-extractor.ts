/**
 * @fileoverview Rust Language Extractor
 * @module @nahisaho/musubix-security/extractors/rust-extractor
 * @trace TSK-025, TSK-026
 * @trace REQ-SEC-LANG-006, REQ-SEC-CFG-001, REQ-SEC-DFG-001
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
 * Rust framework models with proper FrameworkModel interface
 */
const RUST_FRAMEWORK_MODELS: FrameworkModel[] = [
  // Unsafe code
  {
    name: 'Rust Unsafe',
    languages: ['rust'],
    sources: [],
    sinks: [
      { pattern: /unsafe\s*\{/, type: 'unsafe', vulnerabilityType: 'unsafe_code', severity: 'high' },
      { pattern: /std::mem::transmute/, type: 'unsafe', vulnerabilityType: 'unsafe_code', severity: 'critical' },
      { pattern: /from_raw_parts/, type: 'unsafe', vulnerabilityType: 'unsafe_code', severity: 'critical' },
      { pattern: /as_ptr\(\)/, type: 'unsafe', vulnerabilityType: 'unsafe_code', severity: 'high' },
    ],
    sanitizers: [],
  },
  // Process/Command execution
  {
    name: 'Rust Process',
    languages: ['rust'],
    sources: [
      { pattern: /env::args\(\)/, type: 'user_input', description: 'Command line args', taintLabel: 'user_input' },
      { pattern: /env::var\(/, type: 'user_input', description: 'Environment variable', taintLabel: 'env_input' },
      { pattern: /std::io::stdin/, type: 'user_input', description: 'Standard input', taintLabel: 'user_input' },
    ],
    sinks: [
      { pattern: /Command::new\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
      { pattern: /\.arg\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'high' },
      { pattern: /\.spawn\(\)/, type: 'command', vulnerabilityType: 'command_injection', severity: 'high' },
    ],
    sanitizers: [],
  },
  // File system
  {
    name: 'Rust FS',
    languages: ['rust'],
    sources: [],
    sinks: [
      { pattern: /File::open\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /File::create\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /fs::read\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /fs::write\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /fs::remove/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    ],
    sanitizers: [
      { pattern: /canonicalize\(\)/, sanitizes: ['path_traversal'] },
    ],
  },
  // Actix-web
  {
    name: 'Actix-web',
    languages: ['rust'],
    sources: [
      { pattern: /web::Query</, type: 'user_input', description: 'Query parameters', taintLabel: 'user_input' },
      { pattern: /web::Json</, type: 'user_input', description: 'JSON body', taintLabel: 'user_input' },
      { pattern: /web::Path</, type: 'user_input', description: 'Path parameters', taintLabel: 'user_input' },
      { pattern: /web::Form</, type: 'user_input', description: 'Form data', taintLabel: 'user_input' },
      { pattern: /HttpRequest/, type: 'user_input', description: 'HTTP request', taintLabel: 'user_input' },
    ],
    sinks: [
      { pattern: /HttpResponse::Ok\(\)\.body\(/, type: 'xss', vulnerabilityType: 'xss', severity: 'high' },
    ],
    sanitizers: [],
  },
  // Rocket
  {
    name: 'Rocket',
    languages: ['rust'],
    sources: [
      { pattern: /Form</, type: 'user_input', description: 'Form data', taintLabel: 'user_input' },
      { pattern: /Query</, type: 'user_input', description: 'Query parameters', taintLabel: 'user_input' },
      { pattern: /Json</, type: 'user_input', description: 'JSON body', taintLabel: 'user_input' },
    ],
    sinks: [],
    sanitizers: [],
  },
  // SQLx
  {
    name: 'SQLx',
    languages: ['rust'],
    sources: [],
    sinks: [
      { pattern: /sqlx::query\([^!]/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /sqlx::query_as\(/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /\.execute\(/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'high' },
      { pattern: /\.fetch/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'high' },
    ],
    sanitizers: [
      { pattern: /\.bind\(/, sanitizes: ['sql_injection'] },
      { pattern: /sqlx::query!/, sanitizes: ['sql_injection'] },
    ],
  },
  // Diesel
  {
    name: 'Diesel',
    languages: ['rust'],
    sources: [],
    sinks: [
      { pattern: /sql_query\(/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    ],
    sanitizers: [],
  },
  // Serde deserialization
  {
    name: 'Serde',
    languages: ['rust'],
    sources: [
      { pattern: /serde_json::from_str/, type: 'deserialize', description: 'JSON deserialization', taintLabel: 'deserialize' },
      { pattern: /serde_json::from_slice/, type: 'deserialize', description: 'JSON deserialization', taintLabel: 'deserialize' },
      { pattern: /serde_yaml::from_str/, type: 'deserialize', description: 'YAML deserialization', taintLabel: 'deserialize' },
    ],
    sinks: [],
    sanitizers: [],
  },
  // Memory safety
  {
    name: 'Rust Memory',
    languages: ['rust'],
    sources: [],
    sinks: [
      { pattern: /Box::from_raw\(/, type: 'memory', vulnerabilityType: 'memory_safety', severity: 'critical' },
      { pattern: /std::mem::forget\(/, type: 'memory', vulnerabilityType: 'memory_safety', severity: 'high' },
      { pattern: /ManuallyDrop/, type: 'memory', vulnerabilityType: 'memory_safety', severity: 'high' },
    ],
    sanitizers: [],
  },
  // Panic handling
  {
    name: 'Rust Panic',
    languages: ['rust'],
    sources: [],
    sinks: [
      { pattern: /\.unwrap\(\)/, type: 'panic', vulnerabilityType: 'panic', severity: 'medium' },
      { pattern: /\.expect\(/, type: 'panic', vulnerabilityType: 'panic', severity: 'medium' },
      { pattern: /panic!/, type: 'panic', vulnerabilityType: 'panic', severity: 'medium' },
      { pattern: /unreachable!/, type: 'panic', vulnerabilityType: 'panic', severity: 'medium' },
    ],
    sanitizers: [
      { pattern: /unwrap_or/, sanitizes: ['panic'] },
      { pattern: /\.ok\(\)/, sanitizes: ['panic'] },
      { pattern: /\?/, sanitizes: ['panic'] },
    ],
  },
];

/**
 * Rust Language Extractor
 * @trace TSK-025
 */
export class RustExtractor extends BaseExtractor {
  readonly language: SupportedLanguage = 'rust';
  readonly extensions: string[] = ['.rs'];

  private parser: TreeSitterParser | null = null;
  private tree: TreeSitterTree | null = null;
  private nodeIdCounter = 0;
  private blockIdCounter = 0;

  /**
   * Get framework models for Rust
   */
  getFrameworkModels(): FrameworkModel[] {
    return RUST_FRAMEWORK_MODELS;
  }

  /**
   * Initialize tree-sitter parser
   */
  private async initParser(): Promise<void> {
    if (this.parser) return;

    try {
      const Parser = (await import('tree-sitter')).default;
      const Rust = (await import('tree-sitter-rust')).default;

      this.parser = new Parser();
      this.parser.setLanguage(Rust);
    } catch {
      this.parser = null;
    }
  }

  /**
   * Build AST from source code
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
   */
  private extractNodeProperties(node: TreeSitterNode): Record<string, unknown> {
    const props: Record<string, unknown> = {};

    switch (node.type) {
      case 'function_item': {
        const nameNode = node.childForFieldName('name');
        const paramsNode = node.childForFieldName('parameters');
        const returnNode = node.childForFieldName('return_type');
        props.name = nameNode?.text;
        props.parameters = paramsNode?.namedChildren.map((p) => p.text) ?? [];
        props.returnType = returnNode?.text;
        props.isAsync = node.text.startsWith('async');
        props.isUnsafe = node.text.includes('unsafe');
        break;
      }

      case 'struct_item': {
        const nameNode = node.childForFieldName('name');
        props.name = nameNode?.text;
        break;
      }

      case 'enum_item': {
        const nameNode = node.childForFieldName('name');
        props.name = nameNode?.text;
        break;
      }

      case 'impl_item': {
        const typeNode = node.childForFieldName('type');
        const traitNode = node.childForFieldName('trait');
        props.typeName = typeNode?.text;
        props.traitName = traitNode?.text;
        break;
      }

      case 'call_expression':
      case 'method_call_expression': {
        const functionNode = node.childForFieldName('function');
        props.functionName = functionNode?.text;
        break;
      }

      case 'unsafe_block':
        props.isUnsafe = true;
        break;

      case 'let_declaration': {
        const patternNode = node.childForFieldName('pattern');
        const valueNode = node.childForFieldName('value');
        props.pattern = patternNode?.text;
        props.value = valueNode?.text;
        break;
      }
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

    const models = frameworkModels.length > 0 ? frameworkModels : RUST_FRAMEWORK_MODELS;

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
              properties: { sourceType: source.type },
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
              properties: { sinkType: sink.type, vulnerabilityType: sink.vulnerabilityType },
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
              properties: { sanitizes: sanitizer.sanitizes },
            });
          }
        }
      }

      // Handle let declarations (assignments)
      if (astNode.type === 'let_declaration') {
        const dfgId = `dfg_let_${astNode.id}`;
        nodes.set(dfgId, {
          id: dfgId,
          astNodeId: astNode.id,
          nodeType: 'propagator',
          variable: astNode.properties.pattern as string,
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
      if (astNode.type === 'function_item') {
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
   */
  protected async extractSymbols(
    astNodes: Map<string, ASTNode>
  ): Promise<SymbolTable> {
    const symbols = new Map<string, Symbol>();
    const functions = new Map<string, FunctionSymbol>();
    const classes = new Map<string, ClassSymbol>();
    const scopes = new Map<string, ScopeInfo>();

    // Global scope
    const globalScope: ScopeInfo = {
      id: 'global',
      symbols: [],
      kind: 'global',
    };
    scopes.set('global', globalScope);

    for (const [_nodeId, astNode] of astNodes) {
      switch (astNode.type) {
        case 'function_item': {
          const funcId = `func_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'anonymous';
          const params = (astNode.properties.parameters as string[]) ?? [];

          const funcSymbol: FunctionSymbol = {
            name,
            kind: 'function',
            location: astNode.location,
            scopeId: 'global',
            properties: {
              isAsync: astNode.properties.isAsync,
              isUnsafe: astNode.properties.isUnsafe,
            },
            parameters: params.map((p, i) => ({
              name: p,
              index: i,
            })),
            returnType: astNode.properties.returnType as string | undefined,
            isAsync: astNode.properties.isAsync as boolean | undefined,
          };

          functions.set(funcId, funcSymbol);
          symbols.set(funcId, funcSymbol);
          globalScope.symbols.push(funcId);
          break;
        }

        case 'struct_item': {
          const structId = `struct_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'Anonymous';

          const structSymbol: ClassSymbol = {
            name,
            kind: 'class',
            location: astNode.location,
            scopeId: 'global',
            methods: [],
            properties: [],
          };

          classes.set(structId, structSymbol);
          // ClassSymbol has different properties type, store as generic symbol
          const structAsSymbol: Symbol = {
            name,
            kind: 'class',
            location: astNode.location,
            scopeId: 'global',
            properties: { methods: [], structFields: [] },
          };
          symbols.set(structId, structAsSymbol);
          globalScope.symbols.push(structId);
          break;
        }

        case 'enum_item': {
          const enumId = `enum_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'Anonymous';

          const enumSymbol: Symbol = {
            name,
            kind: 'enum',
            location: astNode.location,
            scopeId: 'global',
            properties: {},
          };

          symbols.set(enumId, enumSymbol);
          globalScope.symbols.push(enumId);
          break;
        }

        case 'trait_item': {
          const traitId = `trait_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'Anonymous';

          const traitSymbol: Symbol = {
            name,
            kind: 'interface',
            location: astNode.location,
            scopeId: 'global',
            properties: {},
          };

          symbols.set(traitId, traitSymbol);
          globalScope.symbols.push(traitId);
          break;
        }

        case 'impl_item': {
          const implId = `impl_${astNode.id}`;
          const typeName = astNode.properties.typeName as string | undefined;
          const traitName = astNode.properties.traitName as string | undefined;

          const implSymbol: Symbol = {
            name: traitName ? `impl ${traitName} for ${typeName}` : `impl ${typeName}`,
            kind: 'type',
            location: astNode.location,
            scopeId: 'global',
            properties: { typeName, traitName },
          };

          symbols.set(implId, implSymbol);
          globalScope.symbols.push(implId);
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
   * Check if node is unsafe
   */
  isUnsafe(astNode: ASTNode): boolean {
    if (astNode.type === 'unsafe_block') return true;
    if (astNode.properties?.isUnsafe) return true;
    if (astNode.text?.includes('unsafe')) return true;
    return false;
  }
}

/**
 * Create Rust extractor instance
 */
export function createRustExtractor(): RustExtractor {
  return new RustExtractor();
}
