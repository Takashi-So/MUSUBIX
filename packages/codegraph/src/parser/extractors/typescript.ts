/**
 * @nahisaho/musubix-codegraph - TypeScript/JavaScript Extractor
 *
 * AST extractor for TypeScript and JavaScript source files
 *
 * @see REQ-CG-AST-002
 * @see DES-CG-TS
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * TypeScript/JavaScript language extractor
 */
export class TypeScriptExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'typescript',
    extensions: ['.ts', '.tsx', '.js', '.jsx', '.mjs', '.cjs'],
    treeSitterName: 'typescript',
    functionNodes: [
      'function_declaration',
      'arrow_function',
      'method_definition',
      'function_expression',
    ],
    classNodes: ['class_declaration'],
    importNodes: ['import_statement'],
    interfaceNodes: ['interface_declaration', 'type_alias_declaration'],
    moduleNodes: ['module'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    // Add file entity
    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    // Current context for tracking parent class/interface
    let currentClassId: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'function_declaration':
        case 'arrow_function':
        case 'function_expression': {
          const entity = this.extractFunction(node, filePath);
          if (entity) {
            entities.push(entity);
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: currentClassId || fileEntityId,
                targetId: entity.id,
              })
            );
          }
          break;
        }

        case 'class_declaration': {
          const entity = this.extractClass(node, filePath);
          if (entity) {
            entities.push(entity);
            currentClassId = entity.id;
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: fileEntityId,
                targetId: entity.id,
              })
            );
            // Extract inheritance
            const heritage = this.extractHeritage(node, filePath, entity.id);
            relations.push(...heritage);
          }
          break;
        }

        case 'interface_declaration': {
          const entity = this.extractInterface(node, filePath);
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

        case 'method_definition': {
          const entity = this.extractMethod(node, filePath);
          if (entity && currentClassId) {
            entities.push(entity);
            relations.push(
              this.createRelation({
                type: 'member_of',
                sourceId: entity.id,
                targetId: currentClassId,
              })
            );
          }
          break;
        }

        case 'import_statement': {
          const importRelations = this.extractImport(node, filePath, fileEntityId);
          relations.push(...importRelations);
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
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'function',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'typescript',
      docstring: this.extractDocstring(node),
    });
  }

  private extractClass(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'class',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'typescript',
      docstring: this.extractDocstring(node),
    });
  }

  private extractInterface(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'interface',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'typescript',
      docstring: this.extractDocstring(node),
    });
  }

  private extractMethod(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'method',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'typescript',
      docstring: this.extractDocstring(node),
    });
  }

  private extractHeritage(
    node: SyntaxNode,
    _filePath: string,
    classId: string
  ): Relation[] {
    const relations: Relation[] = [];
    const heritageClause = this.findChildByType(node, 'class_heritage');

    if (heritageClause) {
      for (const child of heritageClause.namedChildren) {
        if (child.type === 'extends_clause') {
          const typeName = this.findChildByType(child, 'identifier')?.text;
          if (typeName) {
            relations.push(
              this.createRelation({
                type: 'extends',
                sourceId: classId,
                targetId: `external:${typeName}`,
              })
            );
          }
        } else if (child.type === 'implements_clause') {
          for (const impl of child.namedChildren) {
            const typeName =
              impl.type === 'identifier'
                ? impl.text
                : this.findChildByType(impl, 'identifier')?.text;
            if (typeName) {
              relations.push(
                this.createRelation({
                  type: 'implements',
                  sourceId: classId,
                  targetId: `external:${typeName}`,
                })
              );
            }
          }
        }
      }
    }

    return relations;
  }

  private extractImport(
    node: SyntaxNode,
    _filePath: string,
    fileEntityId: string
  ): Relation[] {
    const relations: Relation[] = [];
    const sourceNode = this.findChildByType(node, 'string');
    const modulePath = sourceNode?.text?.replace(/['"]/g, '');

    if (modulePath) {
      relations.push(
        this.createRelation({
          type: 'imports',
          sourceId: fileEntityId,
          targetId: `module:${modulePath}`,
        })
      );
    }

    return relations;
  }
}

/**
 * JavaScript extractor (uses TypeScript extractor with JS config)
 */
export class JavaScriptExtractor extends TypeScriptExtractor {
  override readonly config: LanguageConfig = {
    name: 'javascript',
    extensions: ['.js', '.jsx', '.mjs', '.cjs'],
    treeSitterName: 'javascript',
    functionNodes: [
      'function_declaration',
      'arrow_function',
      'method_definition',
      'function_expression',
    ],
    classNodes: ['class_declaration'],
    importNodes: ['import_statement'],
    interfaceNodes: [],
    moduleNodes: [],
  };
}
