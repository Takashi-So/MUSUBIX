/**
 * YATA Local - Knowledge Graph Auto Updater
 *
 * Automatically extracts entities and relationships from code
 * and updates the knowledge graph.
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local
 * @see REQ-YATA-AUTO-001
 */

import type {
  EntityType,
  RelationType,
} from './types.js';

/**
 * Extracted entity from code analysis
 */
export interface ExtractedEntity {
  type: EntityType;
  name: string;
  namespace: string;
  filePath: string;
  line?: number;
  description?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Extracted relationship from code analysis
 */
export interface ExtractedRelationship {
  sourceName: string;
  sourceNamespace: string;
  targetName: string;
  targetNamespace: string;
  type: RelationType;
  metadata?: Record<string, unknown>;
}

/**
 * Code analysis result
 */
export interface CodeAnalysisResult {
  filePath: string;
  entities: ExtractedEntity[];
  relationships: ExtractedRelationship[];
  errors: string[];
}

/**
 * Update result
 */
export interface UpdateResult {
  success: boolean;
  entitiesAdded: number;
  entitiesUpdated: number;
  entitiesDeleted: number;
  relationshipsAdded: number;
  relationshipsDeleted: number;
  errors: string[];
}

/**
 * TypeScript/JavaScript AST node types
 */
type ASTNodeType =
  | 'ClassDeclaration'
  | 'InterfaceDeclaration'
  | 'FunctionDeclaration'
  | 'MethodDefinition'
  | 'VariableDeclaration'
  | 'TypeAlias'
  | 'EnumDeclaration'
  | 'ImportDeclaration'
  | 'ExportDeclaration';

/**
 * Simple AST node representation
 */
interface SimpleASTNode {
  type: ASTNodeType;
  name: string;
  line: number;
  endLine?: number;
  modifiers?: string[];
  extends?: string;
  implements?: string[];
  parameters?: string[];
  returnType?: string;
  members?: SimpleASTNode[];
  importFrom?: string;
  exportName?: string;
}

/**
 * Knowledge Graph Auto Updater
 *
 * Analyzes TypeScript/JavaScript code and automatically
 * updates the knowledge graph with extracted entities
 * and relationships.
 */
export class KnowledgeGraphUpdater {
  /**
   * Analyze TypeScript/JavaScript code and extract entities
   */
  analyzeCode(content: string, filePath: string): CodeAnalysisResult {
    const entities: ExtractedEntity[] = [];
    const relationships: ExtractedRelationship[] = [];
    const errors: string[] = [];
    const namespace = this.extractNamespace(filePath);

    try {
      const ast = this.parseSimpleAST(content);

      for (const node of ast) {
        const result = this.processNode(node, namespace, filePath);
        entities.push(...result.entities);
        relationships.push(...result.relationships);
      }

      // Extract import relationships
      const imports = this.extractImports(content, filePath);
      relationships.push(...imports);

    } catch (error) {
      errors.push(
        `Failed to analyze ${filePath}: ${error instanceof Error ? error.message : String(error)}`
      );
    }

    return { filePath, entities, relationships, errors };
  }

  /**
   * Extract namespace from file path
   */
  private extractNamespace(filePath: string): string {
    // Remove extension and convert to namespace
    const withoutExt = filePath.replace(/\.(ts|tsx|js|jsx|mjs|cjs)$/, '');
    // Convert path separators to dots
    const namespace = withoutExt
      .replace(/^(src|lib|dist)\//, '')
      .replace(/\//g, '.')
      .replace(/^\.+|\.+$/g, '');
    return namespace || 'root';
  }

  /**
   * Parse content into simple AST nodes
   */
  private parseSimpleAST(content: string): SimpleASTNode[] {
    const nodes: SimpleASTNode[] = [];
    const lines = content.split('\n');

    // Class/Interface detection regex
    const classRegex = /^(?:export\s+)?(?:abstract\s+)?class\s+(\w+)(?:\s+extends\s+(\w+))?(?:\s+implements\s+([\w,\s]+))?/;
    const interfaceRegex = /^(?:export\s+)?interface\s+(\w+)(?:\s+extends\s+([\w,\s]+))?/;
    const functionRegex = /^(?:export\s+)?(?:async\s+)?function\s+(\w+)/;
    const constFunctionRegex = /^(?:export\s+)?const\s+(\w+)\s*=\s*(?:async\s+)?\(?/;
    const typeRegex = /^(?:export\s+)?type\s+(\w+)\s*=/;
    const enumRegex = /^(?:export\s+)?enum\s+(\w+)/;
    const importRegex = /^import\s+(?:{([^}]+)}|\*\s+as\s+(\w+)|(\w+))\s+from\s+['"]([^'"]+)['"]/;
    const methodRegex = /^\s+(?:public\s+|private\s+|protected\s+)?(?:static\s+)?(?:async\s+)?(\w+)\s*\(/;

    let currentClass: SimpleASTNode | null = null;
    let braceCount = 0;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const lineNum = i + 1;
      const trimmed = line.trim();

      // Skip empty lines and comments
      if (!trimmed || trimmed.startsWith('//') || trimmed.startsWith('*')) {
        continue;
      }

      // Track brace depth for class scope
      braceCount += (line.match(/{/g) || []).length;
      braceCount -= (line.match(/}/g) || []).length;

      // Check for class end
      if (currentClass && braceCount === 0) {
        currentClass.endLine = lineNum;
        currentClass = null;
      }

      // Class declaration
      const classMatch = trimmed.match(classRegex);
      if (classMatch) {
        const node: SimpleASTNode = {
          type: 'ClassDeclaration',
          name: classMatch[1],
          line: lineNum,
          modifiers: trimmed.includes('abstract') ? ['abstract'] : [],
          extends: classMatch[2],
          implements: classMatch[3]?.split(',').map(s => s.trim()),
          members: [],
        };
        nodes.push(node);
        currentClass = node;
        continue;
      }

      // Interface declaration
      const interfaceMatch = trimmed.match(interfaceRegex);
      if (interfaceMatch) {
        nodes.push({
          type: 'InterfaceDeclaration',
          name: interfaceMatch[1],
          line: lineNum,
          extends: interfaceMatch[2],
        });
        continue;
      }

      // Function declaration
      const functionMatch = trimmed.match(functionRegex);
      if (functionMatch && !currentClass) {
        nodes.push({
          type: 'FunctionDeclaration',
          name: functionMatch[1],
          line: lineNum,
          modifiers: trimmed.includes('async') ? ['async'] : [],
        });
        continue;
      }

      // Const function (arrow function)
      const constFunctionMatch = trimmed.match(constFunctionRegex);
      if (constFunctionMatch && !currentClass) {
        // Check if it's actually a function (has => or function keyword)
        if (trimmed.includes('=>') || lines.slice(i, i + 3).join('').includes('=>')) {
          nodes.push({
            type: 'FunctionDeclaration',
            name: constFunctionMatch[1],
            line: lineNum,
            modifiers: trimmed.includes('async') ? ['async'] : [],
          });
          continue;
        }
      }

      // Type alias
      const typeMatch = trimmed.match(typeRegex);
      if (typeMatch) {
        nodes.push({
          type: 'TypeAlias',
          name: typeMatch[1],
          line: lineNum,
        });
        continue;
      }

      // Enum
      const enumMatch = trimmed.match(enumRegex);
      if (enumMatch) {
        nodes.push({
          type: 'EnumDeclaration',
          name: enumMatch[1],
          line: lineNum,
        });
        continue;
      }

      // Import
      const importMatch = trimmed.match(importRegex);
      if (importMatch) {
        const names = importMatch[1] || importMatch[2] || importMatch[3];
        nodes.push({
          type: 'ImportDeclaration',
          name: names,
          line: lineNum,
          importFrom: importMatch[4],
        });
        continue;
      }

      // Method (inside class)
      if (currentClass) {
        const methodMatch = line.match(methodRegex);
        if (methodMatch && !['if', 'for', 'while', 'switch', 'catch', 'constructor'].includes(methodMatch[1])) {
          currentClass.members?.push({
            type: 'MethodDefinition',
            name: methodMatch[1],
            line: lineNum,
            modifiers: this.extractMethodModifiers(line),
          });
        }
      }
    }

    return nodes;
  }

  /**
   * Extract method modifiers
   */
  private extractMethodModifiers(line: string): string[] {
    const modifiers: string[] = [];
    if (line.includes('public')) modifiers.push('public');
    if (line.includes('private')) modifiers.push('private');
    if (line.includes('protected')) modifiers.push('protected');
    if (line.includes('static')) modifiers.push('static');
    if (line.includes('async')) modifiers.push('async');
    return modifiers;
  }

  /**
   * Process AST node and extract entities/relationships
   */
  private processNode(
    node: SimpleASTNode,
    namespace: string,
    filePath: string
  ): { entities: ExtractedEntity[]; relationships: ExtractedRelationship[] } {
    const entities: ExtractedEntity[] = [];
    const relationships: ExtractedRelationship[] = [];

    switch (node.type) {
      case 'ClassDeclaration': {
        entities.push({
          type: 'class',
          name: node.name,
          namespace,
          filePath,
          line: node.line,
          metadata: {
            modifiers: node.modifiers,
            endLine: node.endLine,
          },
        });

        // Extends relationship
        if (node.extends) {
          relationships.push({
            sourceName: node.name,
            sourceNamespace: namespace,
            targetName: node.extends,
            targetNamespace: namespace, // May need resolution
            type: 'extends',
          });
        }

        // Implements relationships
        if (node.implements) {
          for (const iface of node.implements) {
            relationships.push({
              sourceName: node.name,
              sourceNamespace: namespace,
              targetName: iface,
              targetNamespace: namespace,
              type: 'implements',
            });
          }
        }

        // Process methods
        if (node.members) {
          for (const member of node.members) {
            if (member.type === 'MethodDefinition') {
              entities.push({
                type: 'method',
                name: member.name,
                namespace: `${namespace}.${node.name}`,
                filePath,
                line: member.line,
                metadata: { modifiers: member.modifiers },
              });

              // Method belongs to class
              relationships.push({
                sourceName: node.name,
                sourceNamespace: namespace,
                targetName: member.name,
                targetNamespace: `${namespace}.${node.name}`,
                type: 'has-method',
              });
            }
          }
        }
        break;
      }

      case 'InterfaceDeclaration': {
        entities.push({
          type: 'interface',
          name: node.name,
          namespace,
          filePath,
          line: node.line,
        });

        // Interface extends
        if (node.extends) {
          const extendsList = node.extends.split(',').map(s => s.trim());
          for (const ext of extendsList) {
            relationships.push({
              sourceName: node.name,
              sourceNamespace: namespace,
              targetName: ext,
              targetNamespace: namespace,
              type: 'extends',
            });
          }
        }
        break;
      }

      case 'FunctionDeclaration': {
        entities.push({
          type: 'function',
          name: node.name,
          namespace,
          filePath,
          line: node.line,
          metadata: { modifiers: node.modifiers },
        });
        break;
      }

      case 'TypeAlias': {
        entities.push({
          type: 'type',
          name: node.name,
          namespace,
          filePath,
          line: node.line,
        });
        break;
      }

      case 'EnumDeclaration': {
        entities.push({
          type: 'enum',
          name: node.name,
          namespace,
          filePath,
          line: node.line,
        });
        break;
      }
    }

    return { entities, relationships };
  }

  /**
   * Extract import relationships
   */
  private extractImports(
    content: string,
    filePath: string
  ): ExtractedRelationship[] {
    const relationships: ExtractedRelationship[] = [];
    const namespace = this.extractNamespace(filePath);
    const importRegex = /import\s+(?:{([^}]+)}|\*\s+as\s+(\w+)|(\w+))\s+from\s+['"]([^'"]+)['"]/g;

    let match;
    while ((match = importRegex.exec(content)) !== null) {
      const importedNames = match[1] || match[2] || match[3];
      const importFrom = match[4];
      const targetNamespace = this.resolveImportPath(importFrom, filePath);

      // Create import relationships for each imported name
      const names = importedNames.split(',').map(s => s.trim());
      for (const name of names) {
        if (name) {
          // Handle "Name as Alias" syntax
          const actualName = name.includes(' as ')
            ? name.split(' as ')[0].trim()
            : name;

          relationships.push({
            sourceName: namespace,
            sourceNamespace: namespace,
            targetName: actualName,
            targetNamespace: targetNamespace,
            type: 'imports',
          });
        }
      }
    }

    return relationships;
  }

  /**
   * Resolve import path to namespace
   */
  private resolveImportPath(importPath: string, currentFile: string): string {
    if (importPath.startsWith('.')) {
      // Relative import
      const currentDir = currentFile.replace(/\/[^/]+$/, '');
      const resolved = this.resolvePath(currentDir, importPath);
      return this.extractNamespace(resolved);
    } else if (importPath.startsWith('@')) {
      // Scoped package
      return importPath.replace(/\//g, '.');
    } else {
      // Node module
      return importPath;
    }
  }

  /**
   * Simple path resolution
   */
  private resolvePath(currentDir: string, relativePath: string): string {
    const parts = currentDir.split('/');
    const relParts = relativePath.split('/');

    for (const part of relParts) {
      if (part === '..') {
        parts.pop();
      } else if (part !== '.') {
        parts.push(part.replace(/\.(ts|tsx|js|jsx)$/, ''));
      }
    }

    return parts.join('/');
  }
}

/**
 * Factory function
 */
export function createKnowledgeGraphUpdater(): KnowledgeGraphUpdater {
  return new KnowledgeGraphUpdater();
}
