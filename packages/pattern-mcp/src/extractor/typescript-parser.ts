/**
 * @fileoverview TypeScript AST parser using TypeScript Compiler API
 * @traceability TSK-PATTERN-001, REQ-PATTERN-001-F001
 */

import ts from 'typescript';
import type { ASTNode, Position } from '../types.js';

/**
 * TypeScript parser options
 */
export interface TypeScriptParserOptions {
  /** Include position information */
  includePositions: boolean;
  /** Include node values (identifiers, literals) */
  includeValues: boolean;
  /** Maximum depth to parse */
  maxDepth: number;
}

/**
 * TypeScript AST parser
 * 
 * @description
 * Parses TypeScript/JavaScript source code into a normalized AST
 * using the TypeScript Compiler API.
 */
export class TypeScriptParser {
  private options: TypeScriptParserOptions;

  constructor(options: Partial<TypeScriptParserOptions> = {}) {
    this.options = {
      includePositions: options.includePositions ?? true,
      includeValues: options.includeValues ?? true,
      maxDepth: options.maxDepth ?? 20,
    };
  }

  /**
   * Parse TypeScript/JavaScript source code to AST
   */
  parse(source: string, fileName = 'source.ts'): ASTNode {
    const sourceFile = ts.createSourceFile(
      fileName,
      source,
      ts.ScriptTarget.Latest,
      true,
      ts.ScriptKind.TS
    );

    return this.convertNode(sourceFile, source, 0);
  }

  /**
   * Convert TypeScript AST node to normalized ASTNode
   */
  private convertNode(node: ts.Node, source: string, depth: number): ASTNode {
    const children: ASTNode[] = [];

    if (depth < this.options.maxDepth) {
      ts.forEachChild(node, (child) => {
        children.push(this.convertNode(child, source, depth + 1));
      });
    }

    const result: ASTNode = {
      type: this.getNodeTypeName(node),
      children,
      startPosition: this.getPosition(node.getStart(), source),
      endPosition: this.getPosition(node.getEnd(), source),
    };

    // Include values for identifiers and literals
    if (this.options.includeValues) {
      const value = this.extractValue(node, source);
      if (value !== undefined) {
        result.value = value;
      }
    }

    return result;
  }

  /**
   * Get human-readable node type name
   */
  private getNodeTypeName(node: ts.Node): string {
    return ts.SyntaxKind[node.kind];
  }

  /**
   * Extract value from node (for identifiers, literals)
   */
  private extractValue(node: ts.Node, _source: string): string | undefined {
    if (ts.isIdentifier(node)) {
      return node.text;
    }
    if (ts.isStringLiteral(node)) {
      return node.text;
    }
    if (ts.isNumericLiteral(node)) {
      return node.text;
    }
    if (ts.isTemplateHead(node) || ts.isTemplateMiddle(node) || ts.isTemplateTail(node)) {
      return node.text;
    }
    return undefined;
  }

  /**
   * Convert position offset to row/column
   */
  private getPosition(offset: number, source: string): Position {
    if (!this.options.includePositions) {
      return { row: 0, column: 0 };
    }

    let row = 0;
    let column = 0;
    for (let i = 0; i < offset && i < source.length; i++) {
      if (source[i] === '\n') {
        row++;
        column = 0;
      } else {
        column++;
      }
    }
    return { row, column };
  }

  /**
   * Get all function declarations in source
   */
  getFunctions(source: string): FunctionInfo[] {
    const sourceFile = ts.createSourceFile(
      'source.ts',
      source,
      ts.ScriptTarget.Latest,
      true,
      ts.ScriptKind.TS
    );

    const functions: FunctionInfo[] = [];

    const visit = (node: ts.Node): void => {
      if (ts.isFunctionDeclaration(node) && node.name) {
        functions.push({
          name: node.name.text,
          parameters: node.parameters.map(p => ({
            name: p.name.getText(),
            type: p.type?.getText() ?? 'any',
          })),
          returnType: node.type?.getText() ?? 'void',
          startLine: sourceFile.getLineAndCharacterOfPosition(node.getStart()).line + 1,
          endLine: sourceFile.getLineAndCharacterOfPosition(node.getEnd()).line + 1,
        });
      }

      if (ts.isMethodDeclaration(node) && node.name) {
        functions.push({
          name: node.name.getText(),
          parameters: node.parameters.map(p => ({
            name: p.name.getText(),
            type: p.type?.getText() ?? 'any',
          })),
          returnType: node.type?.getText() ?? 'void',
          startLine: sourceFile.getLineAndCharacterOfPosition(node.getStart()).line + 1,
          endLine: sourceFile.getLineAndCharacterOfPosition(node.getEnd()).line + 1,
        });
      }

      if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) {
        const parent = node.parent;
        let name = '<anonymous>';
        if (ts.isVariableDeclaration(parent) && ts.isIdentifier(parent.name)) {
          name = parent.name.text;
        }
        functions.push({
          name,
          parameters: node.parameters.map(p => ({
            name: p.name.getText(),
            type: p.type?.getText() ?? 'any',
          })),
          returnType: node.type?.getText() ?? 'void',
          startLine: sourceFile.getLineAndCharacterOfPosition(node.getStart()).line + 1,
          endLine: sourceFile.getLineAndCharacterOfPosition(node.getEnd()).line + 1,
        });
      }

      ts.forEachChild(node, visit);
    };

    visit(sourceFile);
    return functions;
  }

  /**
   * Get all class declarations in source
   */
  getClasses(source: string): ClassInfo[] {
    const sourceFile = ts.createSourceFile(
      'source.ts',
      source,
      ts.ScriptTarget.Latest,
      true,
      ts.ScriptKind.TS
    );

    const classes: ClassInfo[] = [];

    const visit = (node: ts.Node): void => {
      if (ts.isClassDeclaration(node) && node.name) {
        const methods: string[] = [];
        const properties: string[] = [];

        node.members.forEach(member => {
          if (ts.isMethodDeclaration(member) && member.name) {
            methods.push(member.name.getText());
          }
          if (ts.isPropertyDeclaration(member) && member.name) {
            properties.push(member.name.getText());
          }
        });

        classes.push({
          name: node.name.text,
          methods,
          properties,
          startLine: sourceFile.getLineAndCharacterOfPosition(node.getStart()).line + 1,
          endLine: sourceFile.getLineAndCharacterOfPosition(node.getEnd()).line + 1,
        });
      }

      ts.forEachChild(node, visit);
    };

    visit(sourceFile);
    return classes;
  }

  /**
   * Get imports from source
   */
  getImports(source: string): ImportInfo[] {
    const sourceFile = ts.createSourceFile(
      'source.ts',
      source,
      ts.ScriptTarget.Latest,
      true,
      ts.ScriptKind.TS
    );

    const imports: ImportInfo[] = [];

    const visit = (node: ts.Node): void => {
      if (ts.isImportDeclaration(node)) {
        const moduleSpecifier = node.moduleSpecifier;
        if (ts.isStringLiteral(moduleSpecifier)) {
          const namedImports: string[] = [];
          let defaultImport: string | undefined;

          if (node.importClause) {
            if (node.importClause.name) {
              defaultImport = node.importClause.name.text;
            }
            if (node.importClause.namedBindings) {
              if (ts.isNamedImports(node.importClause.namedBindings)) {
                node.importClause.namedBindings.elements.forEach(el => {
                  namedImports.push(el.name.text);
                });
              }
            }
          }

          imports.push({
            module: moduleSpecifier.text,
            namedImports,
            defaultImport,
          });
        }
      }

      ts.forEachChild(node, visit);
    };

    visit(sourceFile);
    return imports;
  }
}

/**
 * Function information extracted from AST
 */
export interface FunctionInfo {
  name: string;
  parameters: { name: string; type: string }[];
  returnType: string;
  startLine: number;
  endLine: number;
}

/**
 * Class information extracted from AST
 */
export interface ClassInfo {
  name: string;
  methods: string[];
  properties: string[];
  startLine: number;
  endLine: number;
}

/**
 * Import information extracted from AST
 */
export interface ImportInfo {
  module: string;
  namedImports: string[];
  defaultImport?: string;
}
