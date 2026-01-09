/**
 * @nahisaho/musubix-codegraph - Base Extractor
 *
 * Abstract base class for language-specific AST extractors
 *
 * @see REQ-CG-MULTILANG-NFR-003 - Extensibility
 * @see DES-CG-BASE
 * @see TSK-CG-001
 */

import type {
  Language,
  Entity,
  Relation,
  ParseResult,
  EntityType,
  RelationType,
} from '../../types.js';
import { generateEntityId, generateRelationId } from '../../types.js';

/**
 * Syntax tree type from tree-sitter
 */
export interface SyntaxTree {
  rootNode: SyntaxNode;
}

/**
 * Syntax node type from tree-sitter
 */
export interface SyntaxNode {
  type: string;
  text: string;
  startPosition: { row: number; column: number };
  endPosition: { row: number; column: number };
  children: SyntaxNode[];
  namedChildren: SyntaxNode[];
  childForFieldName(name: string): SyntaxNode | null;
  parent: SyntaxNode | null;
}

/**
 * Language configuration for extractors
 * @see DES-CG-BASE
 */
export interface LanguageConfig {
  /** Language identifier */
  name: Language;
  /** Supported file extensions */
  extensions: string[];
  /** Tree-sitter grammar name */
  treeSitterName: string;
  /** AST node types for functions */
  functionNodes: string[];
  /** AST node types for classes/structs */
  classNodes: string[];
  /** AST node types for imports */
  importNodes: string[];
  /** AST node types for interfaces (optional) */
  interfaceNodes?: string[];
  /** AST node types for modules/namespaces (optional) */
  moduleNodes?: string[];
}

/**
 * Options for creating an entity
 */
export interface CreateEntityOptions {
  type: EntityType;
  name: string;
  filePath?: string;
  startLine: number;
  endLine: number;
  language: Language;
  namespace?: string;
  docstring?: string;
  signature?: string;
  sourceCode?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Options for creating a relation
 */
export interface CreateRelationOptions {
  type: RelationType;
  sourceId: string;
  targetId: string;
  filePath?: string;
  weight?: number;
  metadata?: Record<string, unknown>;
}

/**
 * Abstract base class for language extractors
 *
 * Implements Template Method pattern for AST extraction.
 * Subclasses implement language-specific extraction logic.
 *
 * @see DES-CG-BASE
 * @see TSK-CG-001
 */
export abstract class BaseExtractor {
  /**
   * Language configuration for this extractor
   */
  abstract readonly config: LanguageConfig;

  /**
   * Get the language identifier for this extractor
   * @returns Language name
   */
  getLanguage(): Language {
    return this.config.name;
  }

  /**
   * Get the configuration for this extractor
   * @returns Language configuration
   */
  getConfig(): LanguageConfig {
    return this.config;
  }

  /**
   * Extract entities and relations from AST
   *
   * Template method - must be implemented by subclasses
   *
   * @param tree - Parsed syntax tree
   * @param filePath - Source file path
   * @param sourceCode - Original source code
   * @returns Parse result with entities and relations
   */
  abstract extract(
    tree: SyntaxTree,
    filePath: string,
    sourceCode: string
  ): ParseResult;

  /**
   * Create an entity with generated ID
   *
   * Factory method for consistent entity creation
   *
   * @param options - Entity creation options
   * @returns Created entity
   */
  protected createEntity(options: CreateEntityOptions): Entity {
    const id = generateEntityId(
      options.type,
      options.name,
      options.filePath
    );

    return {
      id,
      type: options.type,
      name: options.name,
      namespace: options.namespace,
      filePath: options.filePath,
      startLine: options.startLine,
      endLine: options.endLine,
      signature: options.signature,
      docstring: options.docstring,
      sourceCode: options.sourceCode,
      language: options.language,
      metadata: options.metadata || {},
      createdAt: new Date(),
      updatedAt: new Date(),
    };
  }

  /**
   * Create a relation between entities
   *
   * Factory method for consistent relation creation
   *
   * @param options - Relation creation options
   * @returns Created relation
   */
  protected createRelation(options: CreateRelationOptions): Relation {
    const id = generateRelationId(
      options.sourceId,
      options.targetId,
      options.type
    );

    return {
      id,
      type: options.type,
      sourceId: options.sourceId,
      targetId: options.targetId,
      weight: options.weight ?? 1.0,
      metadata: options.metadata || {},
      createdAt: new Date(),
    };
  }

  /**
   * Walk AST tree with visitor pattern
   *
   * Depth-first traversal of the syntax tree
   *
   * @param node - Starting node
   * @param visitor - Visitor callback function
   * @param depth - Current depth (default 0)
   */
  protected walkTree(
    node: SyntaxNode,
    visitor: (node: SyntaxNode, depth: number) => void,
    depth: number = 0
  ): void {
    visitor(node, depth);

    for (const child of node.namedChildren) {
      this.walkTree(child, visitor, depth + 1);
    }
  }

  /**
   * Get text content from AST node
   *
   * @param node - Syntax node
   * @returns Node text content
   */
  protected getNodeText(node: SyntaxNode): string {
    return node.text;
  }

  /**
   * Find child node by field name
   *
   * @param node - Parent node
   * @param field - Field name
   * @returns Child node or null
   */
  protected getChildByField(node: SyntaxNode, field: string): SyntaxNode | null {
    return node.childForFieldName(field);
  }

  /**
   * Find first child by node type
   *
   * @param node - Parent node
   * @param type - Node type to find
   * @returns First matching child or null
   */
  protected findChildByType(node: SyntaxNode, type: string): SyntaxNode | null {
    for (const child of node.namedChildren) {
      if (child.type === type) {
        return child;
      }
    }
    return null;
  }

  /**
   * Find all children by node type
   *
   * @param node - Parent node
   * @param type - Node type to find
   * @returns Array of matching children
   */
  protected findChildrenByType(node: SyntaxNode, type: string): SyntaxNode[] {
    return node.namedChildren.filter((child) => child.type === type);
  }

  /**
   * Extract name from identifier node
   *
   * @param node - Identifier node
   * @returns Identifier name
   */
  protected extractIdentifier(node: SyntaxNode): string {
    const identifierNode =
      node.childForFieldName('name') ||
      this.findChildByType(node, 'identifier') ||
      this.findChildByType(node, 'type_identifier');

    return identifierNode?.text || node.text;
  }

  /**
   * Extract docstring/comment above a node
   *
   * @param node - Target node
   * @returns Docstring text or undefined
   */
  protected extractDocstring(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.namedChildren;
    const nodeIndex = siblings.indexOf(node);

    if (nodeIndex > 0) {
      const prevSibling = siblings[nodeIndex - 1];
      if (
        prevSibling.type === 'comment' ||
        prevSibling.type === 'block_comment' ||
        prevSibling.type === 'doc_comment' ||
        prevSibling.type === 'string' // For Python docstrings
      ) {
        return this.cleanDocstring(prevSibling.text);
      }
    }

    return undefined;
  }

  /**
   * Clean docstring by removing comment markers
   *
   * @param raw - Raw docstring text
   * @returns Cleaned docstring
   */
  protected cleanDocstring(raw: string): string {
    return raw
      .replace(/^\/\*\*?|\*\/$/g, '') // Remove /* */ markers
      .replace(/^\/\/\s?/gm, '') // Remove // markers
      .replace(/^\s*\*\s?/gm, '') // Remove leading * in block comments
      .replace(/^["']{3}|["']{3}$/g, '') // Remove Python triple quotes
      .trim();
  }

  /**
   * Get line number from node position
   *
   * @param node - Syntax node
   * @param position - 'start' or 'end'
   * @returns 1-indexed line number
   */
  protected getLineNumber(node: SyntaxNode, position: 'start' | 'end'): number {
    const pos = position === 'start' ? node.startPosition : node.endPosition;
    return pos.row + 1; // Convert to 1-indexed
  }

  /**
   * Create a file entity for the current source file
   *
   * @param filePath - Source file path
   * @param sourceCode - Source code content
   * @returns File entity
   */
  protected createFileEntity(filePath: string, sourceCode: string): Entity {
    const lines = sourceCode.split('\n');
    const fileName = filePath.split('/').pop() || filePath;

    return this.createEntity({
      type: 'file',
      name: fileName,
      filePath,
      startLine: 1,
      endLine: lines.length,
      language: this.config.name,
    });
  }

  /**
   * Check if a node type is a function declaration
   *
   * @param nodeType - AST node type
   * @returns True if function node
   */
  protected isFunctionNode(nodeType: string): boolean {
    return this.config.functionNodes.includes(nodeType);
  }

  /**
   * Check if a node type is a class declaration
   *
   * @param nodeType - AST node type
   * @returns True if class node
   */
  protected isClassNode(nodeType: string): boolean {
    return this.config.classNodes.includes(nodeType);
  }

  /**
   * Check if a node type is an import statement
   *
   * @param nodeType - AST node type
   * @returns True if import node
   */
  protected isImportNode(nodeType: string): boolean {
    return this.config.importNodes.includes(nodeType);
  }

  /**
   * Check if a node type is an interface declaration
   *
   * @param nodeType - AST node type
   * @returns True if interface node
   */
  protected isInterfaceNode(nodeType: string): boolean {
    return this.config.interfaceNodes?.includes(nodeType) ?? false;
  }

  /**
   * Check if a node type is a module/namespace declaration
   *
   * @param nodeType - AST node type
   * @returns True if module node
   */
  protected isModuleNode(nodeType: string): boolean {
    return this.config.moduleNodes?.includes(nodeType) ?? false;
  }
}
