/**
 * @nahisaho/musubix-codegraph - AST Parser
 *
 * Tree-sitter based AST parser for code entity extraction
 * Enhanced with ExtractorRegistry for 16-language support (v2.3.2)
 *
 * @see REQ-CG-AST-001 - Multi-language support
 * @see REQ-CG-AST-002 - Entity extraction
 * @see REQ-CG-AST-003 - Relation extraction
 * @see REQ-CG-MULTILANG-001 to REQ-CG-MULTILANG-013 (v2.3.2)
 * @see DES-CG-002
 * @see TSK-CG-003, TSK-CG-010
 */

import type {
  Language,
  Entity,
  Relation,
  ParseResult,
  ParserOptions,
  EntityType,
} from '../types.js';
import {
  getLanguageFromExtension,
  generateEntityId,
  generateRelationId,
  LANGUAGE_EXTENSIONS,
} from '../types.js';
import { extractorRegistry } from './extractors/index.js';
import * as fs from 'fs/promises';
import * as path from 'path';

// Dynamic imports for tree-sitter (optional dependency)
type Parser = {
  setLanguage(language: unknown): void;
  parse(input: string): SyntaxTree;
};

type SyntaxTree = {
  rootNode: SyntaxNode;
};

type SyntaxNode = {
  type: string;
  text: string;
  startPosition: { row: number; column: number };
  endPosition: { row: number; column: number };
  children: SyntaxNode[];
  namedChildren: SyntaxNode[];
  childForFieldName(name: string): SyntaxNode | null;
  parent: SyntaxNode | null;
};

/**
 * AST Parser using Tree-sitter
 * Enhanced with ExtractorRegistry for multi-language support (v2.3.2)
 */
export class ASTParser {
  private options: Required<ParserOptions>;
  private parser: Parser | null = null;
  private languages = new Map<Language, unknown>();
  private initialized = false;
  private useExtractors = true; // Use new extractor system by default

  constructor(options: Partial<ParserOptions> = {}) {
    this.options = {
      languages: options.languages ?? ['typescript', 'javascript', 'python'],
      includeComments: options.includeComments ?? true,
      extractDocstrings: options.extractDocstrings ?? true,
    };
  }

  /**
   * Initialize tree-sitter and load language grammars
   * Now supports 16 languages via ExtractorRegistry
   */
  private async ensureInitialized(): Promise<void> {
    if (this.initialized) return;

    try {
      // Dynamic import of tree-sitter
      const Parser = (await import('tree-sitter')).default;
      this.parser = new Parser();

      // Load grammars dynamically based on available extractors
      await this.loadAvailableGrammars();

      this.initialized = true;
    } catch {
      // Tree-sitter not available, will use fallback parsing
      this.initialized = true;
    }
  }

  /**
   * Load grammar for a specific language
   */
  private async loadGrammar(language: Language): Promise<boolean> {
    if (this.languages.has(language)) return true;

    const grammarMap: Record<Language, string> = {
      typescript: 'tree-sitter-typescript',
      javascript: 'tree-sitter-typescript',
      python: 'tree-sitter-python',
      rust: 'tree-sitter-rust',
      go: 'tree-sitter-go',
      java: 'tree-sitter-java',
      php: 'tree-sitter-php',
      csharp: 'tree-sitter-c-sharp',
      c: 'tree-sitter-c',
      cpp: 'tree-sitter-cpp',
      ruby: 'tree-sitter-ruby',
      hcl: 'tree-sitter-hcl',
      kotlin: 'tree-sitter-kotlin',
      swift: 'tree-sitter-swift',
      scala: 'tree-sitter-scala',
      lua: 'tree-sitter-lua',
    };

    const grammarModule = grammarMap[language];
    if (!grammarModule) return false;

    try {
      const mod = await import(grammarModule);
      const grammar = mod.default;
      
      // Handle TypeScript/JavaScript special case
      if (language === 'typescript' || language === 'javascript') {
        if (grammar.typescript) {
          this.languages.set('typescript', grammar.typescript);
          this.languages.set('javascript', grammar.typescript);
        } else {
          this.languages.set(language, grammar);
        }
      } else {
        this.languages.set(language, grammar);
      }
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Load all available grammars
   */
  private async loadAvailableGrammars(): Promise<void> {
    // Load TypeScript/JavaScript grammar (commonly available)
    try {
      const TypeScript = (await import('tree-sitter-typescript')).default;
      this.languages.set('typescript', TypeScript.typescript);
      this.languages.set('javascript', TypeScript.typescript);
    } catch {
      // TypeScript grammar not available
    }

    // Load Python grammar (commonly available)
    try {
      const Python = (await import('tree-sitter-python')).default;
      this.languages.set('python', Python);
    } catch {
      // Python grammar not available
    }
  }

  /**
   * Parse a source file
   */
  async parseFile(filePath: string): Promise<ParseResult> {
    const startTime = Date.now();
    const maxFileSize = 1024 * 1024; // 1MB default

    try {
      const content = await fs.readFile(filePath, 'utf-8');

      if (content.length > maxFileSize) {
        return {
          entities: [],
          relations: [],
          errors: [{ message: `File exceeds max size` }],
          stats: { linesOfCode: 0, parseTimeMs: Date.now() - startTime },
        };
      }

      const language = getLanguageFromExtension(filePath);
      if (!language) {
        return {
          entities: [],
          relations: [],
          errors: [{ message: `Unsupported file type: ${filePath}` }],
          stats: { linesOfCode: 0, parseTimeMs: Date.now() - startTime },
        };
      }

      return await this.parseContent(content, language, filePath);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      return {
        entities: [],
        relations: [],
        errors: [{ message: `Failed to read file: ${message}` }],
        stats: { linesOfCode: 0, parseTimeMs: Date.now() - startTime },
      };
    }
  }

  /**
   * Parse source code content
   * Enhanced to use ExtractorRegistry for 16-language support
   */
  async parseContent(
    content: string,
    language: Language,
    filePath?: string
  ): Promise<ParseResult> {
    await this.ensureInitialized();
    const startTime = Date.now();
    const lines = content.split('\n');

    // Try using ExtractorRegistry-based parsing first (v2.3.2)
    if (this.useExtractors && extractorRegistry.hasExtractor(language)) {
      try {
        return await this.parseWithExtractor(content, language, filePath);
      } catch {
        // Fall back to legacy parsing
      }
    }

    // Try tree-sitter parsing 
    if (this.parser && this.languages.has(language)) {
      try {
        return this.parseWithTreeSitter(content, language, filePath, lines.length);
      } catch {
        // Fall back to regex parsing
      }
    }

    // Try to load grammar on-demand
    if (this.parser && await this.loadGrammar(language)) {
      try {
        return this.parseWithTreeSitter(content, language, filePath, lines.length);
      } catch {
        // Fall back to regex parsing
      }
    }

    // Fallback: regex-based parsing
    return this.parseWithRegex(content, language, filePath, lines.length, startTime);
  }

  /**
   * Parse using ExtractorRegistry (v2.3.2)
   * Supports 16 languages with unified interface
   */
  private async parseWithExtractor(
    content: string,
    language: Language,
    filePath?: string
  ): Promise<ParseResult> {
    const extractor = await extractorRegistry.getExtractor(language);
    if (!extractor) {
      throw new Error(`No extractor for language: ${language}`);
    }

    // Get grammar for tree-sitter
    let grammar = this.languages.get(language);
    if (!grammar) {
      await this.loadGrammar(language);
      grammar = this.languages.get(language);
    }

    if (!grammar || !this.parser) {
      throw new Error(`Grammar not available for: ${language}`);
    }

    this.parser.setLanguage(grammar);
    const tree = this.parser.parse(content);

    // Use extractor to parse - cast tree to proper type expected by extractor
    return extractor.extract(
      tree as unknown as Parameters<typeof extractor.extract>[0],
      filePath || 'unknown',
      content
    );
  }

  /**
   * Parse using tree-sitter
   */
  private parseWithTreeSitter(
    content: string,
    language: Language,
    filePath: string | undefined,
    lineCount: number
  ): ParseResult {
    const startTime = Date.now();
    const grammar = this.languages.get(language);

    if (!grammar || !this.parser) {
      throw new Error('Grammar not loaded');
    }

    this.parser.setLanguage(grammar);
    const tree = this.parser.parse(content);
    const entities: Entity[] = [];
    const relations: Relation[] = [];

    // Add file entity
    entities.push(this.createEntity({
      type: 'file',
      name: filePath ? path.basename(filePath) : 'unknown',
      language,
      filePath,
      startLine: 1,
      endLine: lineCount,
    }));

    // Extract entities from AST
    this.extractFromNode(tree.rootNode, entities, relations, language, filePath, content);

    return {
      entities,
      relations,
      errors: [],
      stats: {
        linesOfCode: lineCount,
        parseTimeMs: Date.now() - startTime,
      },
    };
  }

  /**
   * Extract entities from AST node recursively
   */
  private extractFromNode(
    node: SyntaxNode,
    entities: Entity[],
    relations: Relation[],
    language: Language,
    filePath: string | undefined,
    content: string
  ): void {
    const extracted = this.extractEntity(node, language, filePath, content);
    if (extracted) {
      entities.push(extracted.entity);
      relations.push(...extracted.relations);
    }

    for (const child of node.namedChildren) {
      this.extractFromNode(child, entities, relations, language, filePath, content);
    }
  }

  /**
   * Extract entity from a single AST node
   */
  private extractEntity(
    node: SyntaxNode,
    language: Language,
    filePath: string | undefined,
    content: string
  ): { entity: Entity; relations: Relation[] } | null {
    const entityType = this.getEntityType(node.type, language);
    if (!entityType) return null;

    const nameNode = this.findNameNode(node);
    if (!nameNode) return null;

    const name = nameNode.text;
    if (!name) return null;

    const sourceLines = content.split('\n');
    const startLine = node.startPosition.row + 1;
    const endLine = node.endPosition.row + 1;
    const sourceCode = sourceLines.slice(startLine - 1, endLine).join('\n');

    const entity = this.createEntity({
      type: entityType,
      name,
      language,
      filePath,
      startLine,
      endLine,
      sourceCode,
    });

    // Extract docstring
    if (this.options.extractDocstrings) {
      const docstring = this.extractDocstring(node, language, content);
      if (docstring) {
        entity.docstring = docstring;
      }
    }

    // Extract relations
    const relations = this.extractRelations(node, entity.id, language);

    return { entity, relations };
  }

  /**
   * Create entity with required metadata
   */
  private createEntity(params: {
    type: EntityType;
    name: string;
    language?: Language;
    filePath?: string;
    startLine?: number;
    endLine?: number;
    sourceCode?: string;
  }): Entity {
    const id = generateEntityId(params.type, params.name, params.filePath);
    return {
      id,
      name: params.name,
      type: params.type,
      language: params.language,
      filePath: params.filePath,
      startLine: params.startLine,
      endLine: params.endLine,
      sourceCode: params.sourceCode,
      metadata: {},
    };
  }

  /**
   * Create relation with required weight and metadata
   */
  private createRelation(
    sourceId: string,
    targetId: string,
    type: 'extends' | 'implements' | 'calls' | 'contains' | 'imports'
  ): Relation {
    return {
      id: generateRelationId(sourceId, targetId, type),
      sourceId,
      targetId,
      type,
      weight: 1.0,
      metadata: {},
    };
  }

  /**
   * Map AST node type to entity type
   */
  private getEntityType(nodeType: string, language: Language): EntityType | null {
    if (language === 'typescript' || language === 'javascript') {
      switch (nodeType) {
        case 'class_declaration':
        case 'class':
          return 'class';
        case 'interface_declaration':
          return 'interface';
        case 'function_declaration':
        case 'arrow_function':
        case 'function':
          return 'function';
        case 'method_definition':
          return 'method';
        case 'property_definition':
          return 'property';
        case 'variable_declarator':
          return 'variable';
        case 'type_alias_declaration':
          return 'type';
        case 'enum_declaration':
          return 'enum';
        case 'import_statement':
          return 'import';
        case 'export_statement':
          return 'export';
        case 'namespace_declaration':
          return 'namespace';
      }
    }

    if (language === 'python') {
      switch (nodeType) {
        case 'class_definition':
          return 'class';
        case 'function_definition':
          return 'function';
        case 'assignment':
          return 'variable';
        case 'import_statement':
        case 'import_from_statement':
          return 'import';
      }
    }

    return null;
  }

  /**
   * Find the name node within an entity node
   */
  private findNameNode(node: SyntaxNode): SyntaxNode | null {
    const nameNode = node.childForFieldName('name');
    if (nameNode) return nameNode;

    for (const child of node.namedChildren) {
      if (child.type === 'identifier' || child.type === 'type_identifier') {
        return child;
      }
    }

    return null;
  }

  /**
   * Extract docstring from node
   */
  private extractDocstring(node: SyntaxNode, language: Language, content: string): string | null {
    const lines = content.split('\n');
    const startLine = node.startPosition.row;

    if (language === 'typescript' || language === 'javascript') {
      if (startLine > 0) {
        const prevLines: string[] = [];
        for (let i = startLine - 1; i >= 0 && i >= startLine - 20; i--) {
          const line = lines[i].trim();
          if (line.endsWith('*/')) {
            prevLines.unshift(line);
            for (let j = i - 1; j >= 0; j--) {
              const docLine = lines[j].trim();
              prevLines.unshift(docLine);
              if (docLine.startsWith('/**') || docLine.startsWith('/*')) {
                return prevLines.join('\n');
              }
            }
            break;
          }
          if (line === '' || line.startsWith('*')) {
            continue;
          }
          break;
        }
      }
    }

    if (language === 'python') {
      for (const child of node.namedChildren) {
        if (child.type === 'block') {
          for (const blockChild of child.namedChildren) {
            if (blockChild.type === 'expression_statement') {
              for (const exprChild of blockChild.namedChildren) {
                if (exprChild.type === 'string') {
                  return exprChild.text;
                }
              }
            }
            break;
          }
        }
      }
    }

    return null;
  }

  /**
   * Extract relations from node
   */
  private extractRelations(node: SyntaxNode, entityId: string, language: Language): Relation[] {
    const relations: Relation[] = [];

    if (language === 'typescript' || language === 'javascript') {
      const extendsClause = node.childForFieldName('superclass');
      if (extendsClause) {
        const superName = extendsClause.text;
        if (superName) {
          relations.push(this.createRelation(entityId, superName, 'extends'));
        }
      }

      const implementsNode = node.namedChildren.find(c => c.type === 'implements_clause');
      if (implementsNode) {
        for (const child of implementsNode.namedChildren) {
          if (child.type === 'type_identifier') {
            relations.push(this.createRelation(entityId, child.text, 'implements'));
          }
        }
      }
    }

    return relations;
  }

  /**
   * Fallback regex-based parsing
   * Enhanced in v3.0.7 to support all 16 languages
   */
  private parseWithRegex(
    content: string,
    language: Language,
    filePath: string | undefined,
    lineCount: number,
    startTime: number
  ): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];

    // Add file entity
    entities.push(this.createEntity({
      type: 'file',
      name: filePath ? path.basename(filePath) : 'unknown',
      language,
      filePath,
      startLine: 1,
      endLine: lineCount,
    }));

    // Helper to get line number from index
    const getLineNum = (index: number): number =>
      content.substring(0, index).split('\n').length;

    // Language-specific extraction
    switch (language) {
      case 'typescript':
      case 'javascript':
        this.extractTypeScriptEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'python':
        this.extractPythonEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'c':
      case 'cpp':
        this.extractCEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'rust':
        this.extractRustEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'go':
        this.extractGoEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'java':
        this.extractJavaEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'csharp':
        this.extractCSharpEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'php':
        this.extractPhpEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'ruby':
        this.extractRubyEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'kotlin':
        this.extractKotlinEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'swift':
        this.extractSwiftEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'scala':
        this.extractScalaEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'lua':
        this.extractLuaEntities(content, language, filePath, entities, getLineNum);
        break;
      case 'hcl':
        this.extractHclEntities(content, language, filePath, entities, getLineNum);
        break;
    }

    return {
      entities,
      relations,
      errors: [],
      stats: {
        linesOfCode: lineCount,
        parseTimeMs: Date.now() - startTime,
      },
    };
  }

  /**
   * Extract TypeScript/JavaScript entities (v3.0.7)
   */
  private extractTypeScriptEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*(export\s+)?(abstract\s+)?class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Functions
    const funcRegex = /^\s*(export\s+)?(async\s+)?function\s+(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Arrow functions with const
    const arrowRegex = /^\s*(export\s+)?const\s+(\w+)\s*=\s*(async\s+)?\([^)]*\)\s*(:\s*[^=]+)?\s*=>/gm;
    while ((match = arrowRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Interfaces
    const interfaceRegex = /^\s*(export\s+)?interface\s+(\w+)/gm;
    while ((match = interfaceRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'interface', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Types
    const typeRegex = /^\s*(export\s+)?type\s+(\w+)/gm;
    while ((match = typeRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'type', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums
    const enumRegex = /^\s*(export\s+)?enum\s+(\w+)/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Python entities (v3.0.7)
   */
  private extractPythonEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Functions (including async)
    const funcRegex = /^(async\s+)?def\s+(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract C/C++ entities (v3.0.7)
   */
  private extractCEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Function definitions (return_type function_name(params) {)
    const funcRegex = /^(?!(?:if|for|while|switch)\s*\()(\w[\w\s\*]+?)\s+(\w+)\s*\([^)]*\)\s*\{/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      const name = match[2];
      // Skip common keywords
      if (!['if', 'for', 'while', 'switch', 'return'].includes(name)) {
        entities.push(this.createEntity({
          type: 'function', name, language, filePath,
          startLine: getLineNum(match.index), endLine: getLineNum(match.index),
        }));
      }
    }

    // Structs
    const structRegex = /\bstruct\s+(\w+)\s*\{/gm;
    while ((match = structRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'struct', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Unions
    const unionRegex = /\bunion\s+(\w+)\s*\{/gm;
    while ((match = unionRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'union', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums
    const enumRegex = /\benum\s+(\w+)\s*\{/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Typedefs
    const typedefRegex = /\btypedef\s+(?:struct\s+)?(?:\w+\s+)*(\w+)\s*;/gm;
    while ((match = typedefRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'typedef', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Macros
    const macroRegex = /^#define\s+(\w+)/gm;
    while ((match = macroRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'macro', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // C++ classes (for cpp language)
    if (language === 'cpp') {
      const classRegex = /\bclass\s+(\w+)(?:\s*:\s*(?:public|private|protected)\s+\w+)?\s*\{/gm;
      while ((match = classRegex.exec(content)) !== null) {
        entities.push(this.createEntity({
          type: 'class', name: match[1], language, filePath,
          startLine: getLineNum(match.index), endLine: getLineNum(match.index),
        }));
      }

      // C++ namespaces
      const nsRegex = /\bnamespace\s+(\w+)\s*\{/gm;
      while ((match = nsRegex.exec(content)) !== null) {
        entities.push(this.createEntity({
          type: 'namespace', name: match[1], language, filePath,
          startLine: getLineNum(match.index), endLine: getLineNum(match.index),
        }));
      }

      // C++ templates
      const templateRegex = /\btemplate\s*<[^>]+>\s*(?:class|struct)\s+(\w+)/gm;
      while ((match = templateRegex.exec(content)) !== null) {
        entities.push(this.createEntity({
          type: 'class', name: match[1], language, filePath,
          startLine: getLineNum(match.index), endLine: getLineNum(match.index),
        }));
      }
    }
  }

  /**
   * Extract Rust entities (v3.0.7)
   */
  private extractRustEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Functions
    const funcRegex = /^\s*(pub\s+)?(async\s+)?fn\s+(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Structs
    const structRegex = /^\s*(pub\s+)?struct\s+(\w+)/gm;
    while ((match = structRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'struct', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums
    const enumRegex = /^\s*(pub\s+)?enum\s+(\w+)/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Traits
    const traitRegex = /^\s*(pub\s+)?trait\s+(\w+)/gm;
    while ((match = traitRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'trait', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Impl blocks
    const implRegex = /^\s*impl(?:<[^>]+>)?\s+(\w+)/gm;
    while ((match = implRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'impl', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Modules
    const modRegex = /^\s*(pub\s+)?mod\s+(\w+)/gm;
    while ((match = modRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'module', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Type aliases
    const typeRegex = /^\s*(pub\s+)?type\s+(\w+)/gm;
    while ((match = typeRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'type', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Macros
    const macroRegex = /^\s*macro_rules!\s+(\w+)/gm;
    while ((match = macroRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'macro', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Go entities (v3.0.7)
   */
  private extractGoEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Functions
    const funcRegex = /^func\s+(?:\([^)]+\)\s+)?(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Structs
    const structRegex = /^type\s+(\w+)\s+struct\b/gm;
    while ((match = structRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'struct', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Interfaces
    const interfaceRegex = /^type\s+(\w+)\s+interface\b/gm;
    while ((match = interfaceRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'interface', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Type aliases
    const typeRegex = /^type\s+(\w+)\s+(?!struct|interface)\w/gm;
    while ((match = typeRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'type', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Constants
    const constRegex = /^const\s+(\w+)\s*=/gm;
    while ((match = constRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'constant', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Variables
    const varRegex = /^var\s+(\w+)\s+/gm;
    while ((match = varRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'variable', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Java entities (v3.0.7)
   */
  private extractJavaEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*(public|private|protected)?\s*(abstract|final)?\s*class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Interfaces
    const interfaceRegex = /^\s*(public|private|protected)?\s*interface\s+(\w+)/gm;
    while ((match = interfaceRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'interface', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums
    const enumRegex = /^\s*(public|private|protected)?\s*enum\s+(\w+)/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Methods
    const methodRegex = /^\s*(public|private|protected)?\s*(static)?\s*(abstract)?\s*(?:<[\w,\s]+>\s*)?(\w+(?:<[^>]+>)?)\s+(\w+)\s*\([^)]*\)\s*(?:throws\s+[\w,\s]+)?\s*\{/gm;
    while ((match = methodRegex.exec(content)) !== null) {
      const name = match[5];
      if (!['if', 'for', 'while', 'switch', 'try', 'catch'].includes(name)) {
        entities.push(this.createEntity({
          type: 'method', name, language, filePath,
          startLine: getLineNum(match.index), endLine: getLineNum(match.index),
        }));
      }
    }

    // Records (Java 14+)
    const recordRegex = /^\s*(public|private|protected)?\s*record\s+(\w+)/gm;
    while ((match = recordRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'record', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract C# entities (v3.0.7)
   */
  private extractCSharpEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*(public|private|protected|internal)?\s*(abstract|sealed|static|partial)?\s*class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Interfaces
    const interfaceRegex = /^\s*(public|private|protected|internal)?\s*interface\s+(\w+)/gm;
    while ((match = interfaceRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'interface', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Structs
    const structRegex = /^\s*(public|private|protected|internal)?\s*(readonly)?\s*struct\s+(\w+)/gm;
    while ((match = structRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'struct', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums
    const enumRegex = /^\s*(public|private|protected|internal)?\s*enum\s+(\w+)/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Records
    const recordRegex = /^\s*(public|private|protected|internal)?\s*record\s+(\w+)/gm;
    while ((match = recordRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'record', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Namespaces
    const nsRegex = /^\s*namespace\s+([\w.]+)/gm;
    while ((match = nsRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'namespace', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Methods
    const methodRegex = /^\s*(public|private|protected|internal)?\s*(static|virtual|override|abstract|async)?\s*(?:<[\w,\s]+>\s*)?(\w+(?:<[^>]+>)?)\s+(\w+)\s*\([^)]*\)/gm;
    while ((match = methodRegex.exec(content)) !== null) {
      const name = match[4];
      if (!['if', 'for', 'while', 'switch', 'using', 'lock', 'try', 'catch'].includes(name)) {
        entities.push(this.createEntity({
          type: 'method', name, language, filePath,
          startLine: getLineNum(match.index), endLine: getLineNum(match.index),
        }));
      }
    }
  }

  /**
   * Extract PHP entities (v3.0.7)
   */
  private extractPhpEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*(abstract|final)?\s*class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Interfaces
    const interfaceRegex = /^\s*interface\s+(\w+)/gm;
    while ((match = interfaceRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'interface', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Traits
    const traitRegex = /^\s*trait\s+(\w+)/gm;
    while ((match = traitRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'trait', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums (PHP 8.1+)
    const enumRegex = /^\s*enum\s+(\w+)/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Functions
    const funcRegex = /^\s*function\s+(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Methods
    const methodRegex = /^\s*(public|private|protected)?\s*(static)?\s*function\s+(\w+)/gm;
    while ((match = methodRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'method', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Ruby entities (v3.0.7)
   */
  private extractRubyEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Modules
    const moduleRegex = /^\s*module\s+(\w+)/gm;
    while ((match = moduleRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'module', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Methods (def)
    const methodRegex = /^\s*def\s+(self\.)?(\w+[?!=]?)/gm;
    while ((match = methodRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'method', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Kotlin entities (v3.0.7)
   */
  private extractKotlinEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*(open|abstract|sealed|data|inner)?\s*class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Objects
    const objectRegex = /^\s*(companion\s+)?object\s+(\w+)?/gm;
    while ((match = objectRegex.exec(content)) !== null) {
      const name = match[2] || 'Companion';
      entities.push(this.createEntity({
        type: 'object', name, language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Interfaces
    const interfaceRegex = /^\s*interface\s+(\w+)/gm;
    while ((match = interfaceRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'interface', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums
    const enumRegex = /^\s*enum\s+class\s+(\w+)/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Functions
    const funcRegex = /^\s*(suspend\s+)?(fun)\s+(?:<[\w,\s]+>\s*)?(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Swift entities (v3.0.7)
   */
  private extractSwiftEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*(open|public|internal|fileprivate|private)?\s*(final)?\s*class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Structs
    const structRegex = /^\s*(public|internal|fileprivate|private)?\s*struct\s+(\w+)/gm;
    while ((match = structRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'struct', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Protocols
    const protocolRegex = /^\s*(public|internal|fileprivate|private)?\s*protocol\s+(\w+)/gm;
    while ((match = protocolRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'protocol', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Enums
    const enumRegex = /^\s*(public|internal|fileprivate|private)?\s*enum\s+(\w+)/gm;
    while ((match = enumRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'enum', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Functions
    const funcRegex = /^\s*(public|internal|fileprivate|private)?\s*(static|class|override)?\s*func\s+(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Extensions
    const extRegex = /^\s*extension\s+(\w+)/gm;
    while ((match = extRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'extension', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Scala entities (v3.0.7)
   */
  private extractScalaEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Classes
    const classRegex = /^\s*(abstract|sealed|final|case)?\s*class\s+(\w+)/gm;
    while ((match = classRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'class', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Objects
    const objectRegex = /^\s*(case\s+)?object\s+(\w+)/gm;
    while ((match = objectRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'object', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Traits
    const traitRegex = /^\s*(sealed)?\s*trait\s+(\w+)/gm;
    while ((match = traitRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'trait', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Functions (def)
    const funcRegex = /^\s*(override\s+)?(def)\s+(\w+)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[3], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Type aliases
    const typeRegex = /^\s*type\s+(\w+)/gm;
    while ((match = typeRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'type', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract Lua entities (v3.0.7)
   */
  private extractLuaEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Functions
    const funcRegex = /^\s*(local\s+)?function\s+(\w+(?:\.\w+)*)/gm;
    while ((match = funcRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Anonymous functions assigned to variables
    const varFuncRegex = /^\s*(local\s+)?(\w+)\s*=\s*function\s*\(/gm;
    while ((match = varFuncRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'function', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Tables (pseudo-classes)
    const tableRegex = /^\s*(local\s+)?(\w+)\s*=\s*\{/gm;
    while ((match = tableRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'table', name: match[2], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Extract HCL (Terraform) entities (v3.0.7)
   */
  private extractHclEntities(
    content: string,
    language: Language,
    filePath: string | undefined,
    entities: Entity[],
    getLineNum: (index: number) => number
  ): void {
    let match;

    // Resources
    const resourceRegex = /^resource\s+"(\w+)"\s+"(\w+)"/gm;
    while ((match = resourceRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'resource', name: `${match[1]}.${match[2]}`, language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Data sources
    const dataRegex = /^data\s+"(\w+)"\s+"(\w+)"/gm;
    while ((match = dataRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'data', name: `${match[1]}.${match[2]}`, language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Variables
    const varRegex = /^variable\s+"(\w+)"/gm;
    while ((match = varRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'variable', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Outputs
    const outputRegex = /^output\s+"(\w+)"/gm;
    while ((match = outputRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'output', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Modules
    const moduleRegex = /^module\s+"(\w+)"/gm;
    while ((match = moduleRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'module', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Locals
    const localsRegex = /^locals\s*\{/gm;
    while ((match = localsRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'locals', name: 'locals', language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }

    // Providers
    const providerRegex = /^provider\s+"(\w+)"/gm;
    while ((match = providerRegex.exec(content)) !== null) {
      entities.push(this.createEntity({
        type: 'provider', name: match[1], language, filePath,
        startLine: getLineNum(match.index), endLine: getLineNum(match.index),
      }));
    }
  }

  /**
   * Get supported languages
   * Now returns all 16 supported languages (v2.3.2)
   */
  getSupportedLanguages(): Language[] {
    // Get languages from ExtractorRegistry (16 languages)
    const registryLanguages = extractorRegistry.getRegisteredLanguages();
    if (registryLanguages.length > 0) {
      return registryLanguages;
    }

    // Fallback to LANGUAGE_EXTENSIONS
    return Object.values(LANGUAGE_EXTENSIONS).filter(
      (v, i, a) => a.indexOf(v) === i
    ) as Language[];
  }

  /**
   * Check if a language is supported
   */
  isLanguageSupported(language: Language): boolean {
    return extractorRegistry.hasExtractor(language);
  }

  /**
   * Preload all extractors for faster parsing
   */
  async preloadExtractors(): Promise<void> {
    await extractorRegistry.preloadAll();
  }
}
