/**
 * @fileoverview Ruby Language Extractor
 * @module @nahisaho/musubix-security/extractors/ruby-extractor
 * @trace TSK-023, TSK-024
 * @trace REQ-SEC-LANG-005, REQ-SEC-CFG-001, REQ-SEC-DFG-001
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
 * Ruby framework models with proper FrameworkModel interface
 */
const RUBY_FRAMEWORK_MODELS: FrameworkModel[] = [
  // Rails
  {
    name: 'Rails',
    languages: ['ruby'],
    sources: [
      { pattern: /params\[/, type: 'user_input', description: 'Rails params access', taintLabel: 'user_input' },
      { pattern: /request\.body/, type: 'user_input', description: 'Request body', taintLabel: 'user_input' },
      { pattern: /cookies\[/, type: 'user_input', description: 'Cookie access', taintLabel: 'user_input' },
      { pattern: /session\[/, type: 'user_input', description: 'Session access', taintLabel: 'user_input' },
    ],
    sinks: [
      { pattern: /render\s+html:/, type: 'xss', vulnerabilityType: 'xss', severity: 'high' },
      { pattern: /redirect_to\s/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
      { pattern: /send_file\s/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    ],
    sanitizers: [
      { pattern: /html_escape/, sanitizes: ['xss'] },
      { pattern: /\bh\(/, sanitizes: ['xss'] },
      { pattern: /sanitize\(/, sanitizes: ['xss'] },
    ],
  },
  // ActiveRecord
  {
    name: 'ActiveRecord',
    languages: ['ruby'],
    sources: [],
    sinks: [
      { pattern: /\.where\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /\.find_by_sql\(/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
      { pattern: /\.execute\(/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    ],
    sanitizers: [
      { pattern: /sanitize_sql/, sanitizes: ['sql_injection'] },
    ],
  },
  // System commands
  {
    name: 'Ruby System',
    languages: ['ruby'],
    sources: [
      { pattern: /ARGV/, type: 'user_input', description: 'Command line args', taintLabel: 'user_input' },
      { pattern: /ENV\[/, type: 'user_input', description: 'Environment variable', taintLabel: 'env_input' },
    ],
    sinks: [
      { pattern: /system\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
      { pattern: /exec\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
      { pattern: /`.*`/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
      { pattern: /%x\{/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
      { pattern: /IO\.popen\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
      { pattern: /Open3\./, type: 'command', vulnerabilityType: 'command_injection', severity: 'high' },
    ],
    sanitizers: [
      { pattern: /Shellwords\.escape/, sanitizes: ['command_injection'] },
    ],
  },
  // File operations
  {
    name: 'Ruby File IO',
    languages: ['ruby'],
    sources: [],
    sinks: [
      { pattern: /File\.open\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /File\.read\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /File\.write\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
      { pattern: /FileUtils\./, type: 'file', vulnerabilityType: 'path_traversal', severity: 'medium' },
    ],
    sanitizers: [
      { pattern: /File\.expand_path/, sanitizes: ['path_traversal'] },
      { pattern: /File\.basename/, sanitizes: ['path_traversal'] },
    ],
  },
  // Deserialization
  {
    name: 'Ruby Deserialization',
    languages: ['ruby'],
    sources: [],
    sinks: [
      { pattern: /Marshal\.load\(/, type: 'deserialize', vulnerabilityType: 'deserialization', severity: 'critical' },
      { pattern: /YAML\.load\(/, type: 'deserialize', vulnerabilityType: 'deserialization', severity: 'critical' },
    ],
    sanitizers: [
      { pattern: /YAML\.safe_load/, sanitizes: ['deserialization'] },
    ],
  },
  // Eval
  {
    name: 'Ruby Eval',
    languages: ['ruby'],
    sources: [],
    sinks: [
      { pattern: /eval\(/, type: 'code', vulnerabilityType: 'code_injection', severity: 'critical' },
      { pattern: /instance_eval/, type: 'code', vulnerabilityType: 'code_injection', severity: 'critical' },
      { pattern: /class_eval/, type: 'code', vulnerabilityType: 'code_injection', severity: 'high' },
      { pattern: /\.send\(/, type: 'code', vulnerabilityType: 'code_injection', severity: 'high' },
    ],
    sanitizers: [],
  },
];

/**
 * Ruby Language Extractor
 * @trace TSK-023
 */
export class RubyExtractor extends BaseExtractor {
  readonly language: SupportedLanguage = 'ruby';
  readonly extensions: string[] = ['.rb', '.erb', '.rake'];

  private parser: TreeSitterParser | null = null;
  private tree: TreeSitterTree | null = null;
  private nodeIdCounter = 0;
  private blockIdCounter = 0;

  /**
   * Get framework models for Ruby
   */
  getFrameworkModels(): FrameworkModel[] {
    return RUBY_FRAMEWORK_MODELS;
  }

  /**
   * Initialize tree-sitter parser
   */
  private async initParser(): Promise<void> {
    if (this.parser) return;

    try {
      const Parser = (await import('tree-sitter')).default;
      const Ruby = (await import('tree-sitter-ruby')).default;

      this.parser = new Parser();
      this.parser.setLanguage(Ruby);
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
      case 'method':
      case 'singleton_method': {
        const nameNode = node.childForFieldName('name');
        const paramsNode = node.childForFieldName('parameters');
        props.name = nameNode?.text;
        props.parameters = paramsNode?.namedChildren.map((p) => p.text) ?? [];
        break;
      }

      case 'class': {
        const nameNode = node.childForFieldName('name');
        const superNode = node.childForFieldName('superclass');
        props.name = nameNode?.text;
        props.superclass = superNode?.text;
        break;
      }

      case 'module': {
        const nameNode = node.childForFieldName('name');
        props.name = nameNode?.text;
        break;
      }

      case 'call':
      case 'method_call':
      case 'command': {
        const methodNode = node.childForFieldName('method');
        const receiverNode = node.childForFieldName('receiver');
        props.methodName = methodNode?.text;
        props.receiver = receiverNode?.text;
        break;
      }

      case 'assignment': {
        const leftNode = node.childForFieldName('left');
        const rightNode = node.childForFieldName('right');
        props.left = leftNode?.text;
        props.right = rightNode?.text;
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
      type: 'program',
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

    const models = frameworkModels.length > 0 ? frameworkModels : RUBY_FRAMEWORK_MODELS;

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

      // Handle assignments
      if (astNode.type === 'assignment') {
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
   */
  protected async buildCFG(
    astNodes: Map<string, ASTNode>,
    _astEdges: ASTEdge[]
  ): Promise<ControlFlowGraph> {
    const blocks = new Map<string, BasicBlock>();
    const edges: CFGEdge[] = [];
    const entryBlocks: string[] = [];
    const exitBlocks: string[] = [];

    // Find methods and build CFG for each
    for (const [_nodeId, astNode] of astNodes) {
      if (astNode.type === 'method' || astNode.type === 'singleton_method') {
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
        case 'method':
        case 'singleton_method': {
          const funcId = `func_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'anonymous';
          const params = (astNode.properties.parameters as string[]) ?? [];

          const funcSymbol: FunctionSymbol = {
            name,
            kind: 'method',
            location: astNode.location,
            scopeId: 'global',
            properties: {},
            parameters: params.map((p, i) => ({
              name: p,
              index: i,
            })),
          };

          functions.set(funcId, funcSymbol);
          symbols.set(funcId, funcSymbol);
          globalScope.symbols.push(funcId);
          break;
        }

        case 'class': {
          const classId = `class_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'Anonymous';
          const superClass = astNode.properties.superclass as string | undefined;

          const classSymbol: ClassSymbol = {
            name,
            kind: 'class',
            location: astNode.location,
            scopeId: 'global',
            superClass,
            methods: [],
            properties: [],
          };

          classes.set(classId, classSymbol);
          // ClassSymbol has different properties type, store as generic symbol
          const classAsSymbol: Symbol = {
            name,
            kind: 'class',
            location: astNode.location,
            scopeId: 'global',
            properties: { superClass, methods: [], classProperties: [] },
          };
          symbols.set(classId, classAsSymbol);
          globalScope.symbols.push(classId);
          break;
        }

        case 'module': {
          const moduleId = `module_${astNode.id}`;
          const name = (astNode.properties.name as string) ?? 'Anonymous';

          const moduleSymbol: Symbol = {
            name,
            kind: 'interface', // modules as interfaces
            location: astNode.location,
            scopeId: 'global',
            properties: {},
          };

          symbols.set(moduleId, moduleSymbol);
          globalScope.symbols.push(moduleId);
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
}

/**
 * Create Ruby extractor instance
 */
export function createRubyExtractor(): RubyExtractor {
  return new RubyExtractor();
}
