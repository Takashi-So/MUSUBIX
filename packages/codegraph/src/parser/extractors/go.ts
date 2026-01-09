/**
 * @nahisaho/musubix-codegraph - Go Extractor
 *
 * AST extractor for Go source files
 *
 * @see REQ-CG-MULTILANG-002
 * @see DES-CG-GO
 * @see TSK-CG-011
 */

import type { ParseResult, Entity, Relation, EntityType } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Go language extractor
 */
export class GoExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'go',
    extensions: ['.go'],
    treeSitterName: 'go',
    functionNodes: ['function_declaration', 'method_declaration'],
    classNodes: ['type_declaration'],
    importNodes: ['import_declaration'],
    interfaceNodes: ['type_declaration'],
    moduleNodes: ['package_clause'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    // Add file entity
    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    // Track package name
    let packageName: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'package_clause': {
          const nameNode = this.getChildByField(node, 'name') ||
            this.findChildByType(node, 'package_identifier');
          if (nameNode) {
            packageName = nameNode.text;
            const entity = this.createEntity({
              type: 'package',
              name: packageName,
              filePath,
              startLine: this.getLineNumber(node, 'start'),
              endLine: this.getLineNumber(node, 'end'),
              language: 'go',
            });
            entities.push(entity);
          }
          break;
        }

        case 'function_declaration': {
          const entity = this.extractFunction(node, filePath);
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

        case 'method_declaration': {
          const result = this.extractMethod(node, filePath);
          if (result) {
            entities.push(result.entity);
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: fileEntityId,
                targetId: result.entity.id,
              })
            );
            if (result.receiverType) {
              relations.push(
                this.createRelation({
                  type: 'member_of',
                  sourceId: result.entity.id,
                  targetId: `type:${result.receiverType}`,
                })
              );
            }
          }
          break;
        }

        case 'type_declaration': {
          const typeEntities = this.extractTypeDeclaration(node, filePath);
          for (const entity of typeEntities) {
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

        case 'import_declaration': {
          const importRelations = this.extractImport(node, fileEntityId);
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
      language: 'go',
      docstring: this.extractGoDocComment(node),
    });
  }

  private extractMethod(
    node: SyntaxNode,
    filePath: string
  ): { entity: Entity; receiverType: string | null } | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    // Extract receiver type
    const receiverNode = this.getChildByField(node, 'receiver');
    let receiverType: string | null = null;

    if (receiverNode) {
      const parameterDecl = this.findChildByType(receiverNode, 'parameter_declaration');
      if (parameterDecl) {
        const typeNode = this.getChildByField(parameterDecl, 'type');
        if (typeNode) {
          // Handle pointer receivers (*Type)
          receiverType = typeNode.text.replace(/^\*/, '');
        }
      }
    }

    const entity = this.createEntity({
      type: 'method',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'go',
      docstring: this.extractGoDocComment(node),
      metadata: {
        receiverType,
      },
    });

    return { entity, receiverType };
  }

  private extractTypeDeclaration(node: SyntaxNode, filePath: string): Entity[] {
    const entities: Entity[] = [];

    // Handle type spec (can be multiple in one declaration)
    for (const child of node.namedChildren) {
      if (child.type === 'type_spec') {
        const entity = this.extractTypeSpec(child, filePath);
        if (entity) {
          entities.push(entity);
        }
      }
    }

    return entities;
  }

  private extractTypeSpec(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const typeNode = this.getChildByField(node, 'type');

    let entityType: EntityType;
    if (typeNode?.type === 'struct_type') {
      entityType = 'struct';
    } else if (typeNode?.type === 'interface_type') {
      entityType = 'interface';
    } else {
      entityType = 'type';
    }

    return this.createEntity({
      type: entityType,
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'go',
      docstring: this.extractGoDocComment(node),
    });
  }

  private extractImport(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];

    // Handle both single import and import blocks
    const processImportSpec = (spec: SyntaxNode) => {
      const pathNode = this.getChildByField(spec, 'path');
      const path = pathNode?.text?.replace(/"/g, '');
      if (path) {
        relations.push(
          this.createRelation({
            type: 'imports',
            sourceId: fileEntityId,
            targetId: `module:${path}`,
          })
        );
      }
    };

    for (const child of node.namedChildren) {
      if (child.type === 'import_spec') {
        processImportSpec(child);
      } else if (child.type === 'import_spec_list') {
        for (const innerChild of child.namedChildren) {
          if (innerChild.type === 'import_spec') {
            processImportSpec(innerChild);
          }
        }
      }
    }

    return relations;
  }

  private extractGoDocComment(node: SyntaxNode): string | undefined {
    // Look for // comments before the node
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);

    const docComments: string[] = [];
    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment') {
        if (sibling.text.startsWith('//')) {
          docComments.unshift(sibling.text.replace(/^\/\/\s?/, ''));
        } else if (sibling.text.startsWith('/*')) {
          docComments.unshift(this.cleanDocstring(sibling.text));
          break;
        }
      } else {
        break;
      }
    }

    return docComments.length > 0 ? docComments.join('\n') : undefined;
  }
}
