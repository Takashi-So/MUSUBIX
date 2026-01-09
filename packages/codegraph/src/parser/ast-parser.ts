/**
 * @nahisaho/musubix-codegraph - AST Parser
 *
 * Tree-sitter based AST parser for code entity extraction
 *
 * @see REQ-CG-AST-001 - Multi-language support
 * @see REQ-CG-AST-002 - Entity extraction
 * @see REQ-CG-AST-003 - Relation extraction
 * @see DES-CG-002
 * @see TSK-CG-010
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
 */
export class ASTParser {
  private options: Required<ParserOptions>;
  private parser: Parser | null = null;
  private languages = new Map<Language, unknown>();
  private initialized = false;

  constructor(options: Partial<ParserOptions> = {}) {
    this.options = {
      languages: options.languages ?? ['typescript', 'javascript', 'python'],
      includeComments: options.includeComments ?? true,
      extractDocstrings: options.extractDocstrings ?? true,
    };
  }

  /**
   * Initialize tree-sitter and load language grammars
   */
  private async ensureInitialized(): Promise<void> {
    if (this.initialized) return;

    try {
      // Dynamic import of tree-sitter
      const Parser = (await import('tree-sitter')).default;
      this.parser = new Parser();

      // Load TypeScript/JavaScript grammar
      try {
        const TypeScript = (await import('tree-sitter-typescript')).default;
        this.languages.set('typescript', TypeScript.typescript);
        this.languages.set('javascript', TypeScript.typescript);
      } catch {
        // TypeScript grammar not available
      }

      // Load Python grammar
      try {
        const Python = (await import('tree-sitter-python')).default;
        this.languages.set('python', Python);
      } catch {
        // Python grammar not available
      }

      this.initialized = true;
    } catch {
      // Tree-sitter not available, will use fallback parsing
      this.initialized = true;
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
   */
  async parseContent(
    content: string,
    language: Language,
    filePath?: string
  ): Promise<ParseResult> {
    await this.ensureInitialized();
    const startTime = Date.now();
    const lines = content.split('\n');

    // Try tree-sitter parsing first
    if (this.parser && this.languages.has(language)) {
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

    if (language === 'typescript' || language === 'javascript') {
      const classRegex = /^\s*(export\s+)?(abstract\s+)?class\s+(\w+)/gm;
      let match;
      while ((match = classRegex.exec(content)) !== null) {
        const lineNum = content.substring(0, match.index).split('\n').length;
        entities.push(this.createEntity({
          type: 'class',
          name: match[3],
          language,
          filePath,
          startLine: lineNum,
          endLine: lineNum,
        }));
      }

      const funcRegex = /^\s*(export\s+)?(async\s+)?function\s+(\w+)/gm;
      while ((match = funcRegex.exec(content)) !== null) {
        const lineNum = content.substring(0, match.index).split('\n').length;
        entities.push(this.createEntity({
          type: 'function',
          name: match[3],
          language,
          filePath,
          startLine: lineNum,
          endLine: lineNum,
        }));
      }

      const interfaceRegex = /^\s*(export\s+)?interface\s+(\w+)/gm;
      while ((match = interfaceRegex.exec(content)) !== null) {
        const lineNum = content.substring(0, match.index).split('\n').length;
        entities.push(this.createEntity({
          type: 'interface',
          name: match[2],
          language,
          filePath,
          startLine: lineNum,
          endLine: lineNum,
        }));
      }

      const typeRegex = /^\s*(export\s+)?type\s+(\w+)/gm;
      while ((match = typeRegex.exec(content)) !== null) {
        const lineNum = content.substring(0, match.index).split('\n').length;
        entities.push(this.createEntity({
          type: 'type',
          name: match[2],
          language,
          filePath,
          startLine: lineNum,
          endLine: lineNum,
        }));
      }

      const enumRegex = /^\s*(export\s+)?enum\s+(\w+)/gm;
      while ((match = enumRegex.exec(content)) !== null) {
        const lineNum = content.substring(0, match.index).split('\n').length;
        entities.push(this.createEntity({
          type: 'enum',
          name: match[2],
          language,
          filePath,
          startLine: lineNum,
          endLine: lineNum,
        }));
      }
    }

    if (language === 'python') {
      const classRegex = /^class\s+(\w+)/gm;
      let match;
      while ((match = classRegex.exec(content)) !== null) {
        const lineNum = content.substring(0, match.index).split('\n').length;
        entities.push(this.createEntity({
          type: 'class',
          name: match[1],
          language,
          filePath,
          startLine: lineNum,
          endLine: lineNum,
        }));
      }

      const funcRegex = /^def\s+(\w+)/gm;
      while ((match = funcRegex.exec(content)) !== null) {
        const lineNum = content.substring(0, match.index).split('\n').length;
        entities.push(this.createEntity({
          type: 'function',
          name: match[1],
          language,
          filePath,
          startLine: lineNum,
          endLine: lineNum,
        }));
      }
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
   * Get supported languages
   */
  getSupportedLanguages(): Language[] {
    return Object.values(LANGUAGE_EXTENSIONS).filter(
      (v, i, a) => a.indexOf(v) === i
    ) as Language[];
  }
}
