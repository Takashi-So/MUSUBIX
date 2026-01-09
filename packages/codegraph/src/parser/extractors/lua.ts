/**
 * @nahisaho/musubix-codegraph - Lua Extractor
 *
 * AST extractor for Lua source files
 *
 * @see REQ-CG-MULTILANG-013
 * @see DES-CG-LUA
 * @see TSK-CG-034
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Lua language extractor
 */
export class LuaExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'lua',
    extensions: ['.lua'],
    treeSitterName: 'lua',
    functionNodes: ['function_declaration', 'function_definition'],
    classNodes: [],
    importNodes: ['function_call'],
    interfaceNodes: [],
    moduleNodes: [],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    // Track tables that represent classes
    const classLikeTables = new Map<string, string>();

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'function_declaration': {
          const entity = this.extractFunction(node, filePath);
          if (entity) {
            entities.push(entity);
            
            // Check if it's a method (table.method or table:method)
            const nameNode = this.getChildByField(node, 'name');
            if (nameNode?.type === 'method_index_expression' || 
                nameNode?.type === 'dot_index_expression') {
              const tableName = this.getTableName(nameNode);
              if (tableName && classLikeTables.has(tableName)) {
                relations.push(
                  this.createRelation({
                    type: 'member_of',
                    sourceId: entity.id,
                    targetId: classLikeTables.get(tableName)!,
                  })
                );
              } else {
                relations.push(
                  this.createRelation({
                    type: 'contains',
                    sourceId: fileEntityId,
                    targetId: entity.id,
                  })
                );
              }
            } else {
              relations.push(
                this.createRelation({
                  type: 'contains',
                  sourceId: fileEntityId,
                  targetId: entity.id,
                })
              );
            }
          }
          break;
        }

        case 'local_function': {
          const entity = this.extractLocalFunction(node, filePath);
          if (entity) {
            entities.push(entity);
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: fileEntityId,
                targetId: entity.id,
              })
            );
          }
          break;
        }

        case 'variable_declaration':
        case 'local_variable_declaration': {
          // Check if this is a class-like table definition
          const classEntity = this.extractClassLikeTable(node, filePath);
          if (classEntity) {
            entities.push(classEntity);
            classLikeTables.set(classEntity.name, classEntity.id);
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: fileEntityId,
                targetId: classEntity.id,
              })
            );
          }
          break;
        }

        case 'function_call': {
          // Check for require
          const fnName = this.getCallName(node);
          if (fnName === 'require' || fnName === 'dofile' || fnName === 'loadfile') {
            const importRelations = this.extractRequire(node, fileEntityId);
            relations.push(...importRelations);
          }
          break;
        }
      }
    });

    return {
      entities,
      relations,
      errors: [],
      stats: {
        linesOfCode: sourceCode.split('\n').length,
        parseTimeMs: Date.now() - startTime,
      },
    };
  }

  private extractFunction(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    let name = '<anonymous>';

    if (nameNode) {
      if (nameNode.type === 'identifier') {
        name = nameNode.text;
      } else if (nameNode.type === 'method_index_expression' ||
                 nameNode.type === 'dot_index_expression') {
        // Handle Class:method or Class.method
        name = nameNode.text;
      }
    }

    return this.createEntity({
      type: 'function',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'lua',
      docstring: this.extractLuaDocComment(node),
    });
  }

  private extractLocalFunction(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'function',
      name: `local ${name}`,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'lua',
      docstring: this.extractLuaDocComment(node),
      metadata: {
        isLocal: true,
      },
    });
  }

  private extractClassLikeTable(node: SyntaxNode, filePath: string): Entity | null {
    // Look for patterns like:
    // local MyClass = {}
    // MyClass = setmetatable({}, {...})
    const declarator = this.findChildByType(node, 'variable_declarator') ||
      this.findChildByType(node, 'assignment_statement');
    
    if (!declarator) return null;

    const nameNode = this.findChildByType(declarator, 'identifier');
    if (!nameNode) return null;

    const name = nameNode.text;
    
    // Check if value is a table constructor or setmetatable call
    const valueNode = this.getChildByField(declarator, 'value') ||
      this.findChildByType(node, 'table_constructor') ||
      this.findChildByType(node, 'function_call');

    if (!valueNode) return null;

    // Simple heuristic: if name starts with uppercase, treat as class-like
    if (name[0] !== name[0].toUpperCase()) return null;

    return this.createEntity({
      type: 'table',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'lua',
      metadata: {
        classLike: true,
      },
    });
  }

  private getTableName(node: SyntaxNode): string | null {
    const tableNode = this.getChildByField(node, 'table');
    return tableNode?.text || null;
  }

  private getCallName(node: SyntaxNode): string | null {
    const fnNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'identifier');
    return fnNode?.text || null;
  }

  private extractRequire(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];
    const argsNode = this.getChildByField(node, 'arguments');

    if (argsNode) {
      const stringNode = this.findChildByType(argsNode, 'string');
      if (stringNode) {
        const path = stringNode.text.replace(/['"]/g, '');
        relations.push(
          this.createRelation({
            type: 'imports',
            sourceId: fileEntityId,
            targetId: `module:${path}`,
          })
        );
      }
    }

    return relations;
  }

  private extractLuaDocComment(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);
    const docLines: string[] = [];

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment') {
        const text = sibling.text;
        if (text.startsWith('---')) {
          // LuaDoc style
          docLines.unshift(text.replace(/^---\s?/, ''));
        } else if (text.startsWith('--')) {
          docLines.unshift(text.replace(/^--\s?/, ''));
        } else if (text.startsWith('--[[')) {
          // Multi-line comment
          return this.cleanDocstring(text);
        }
      } else {
        break;
      }
    }

    return docLines.length > 0 ? docLines.join('\n') : undefined;
  }
}
