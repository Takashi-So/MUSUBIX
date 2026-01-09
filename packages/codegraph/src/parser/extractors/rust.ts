/**
 * @nahisaho/musubix-codegraph - Rust Extractor
 *
 * AST extractor for Rust source files
 *
 * @see REQ-CG-MULTILANG-001
 * @see DES-CG-RUST
 * @see TSK-CG-010
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Rust language extractor
 */
export class RustExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'rust',
    extensions: ['.rs'],
    treeSitterName: 'rust',
    functionNodes: ['function_item'],
    classNodes: ['struct_item', 'enum_item'],
    importNodes: ['use_declaration'],
    interfaceNodes: ['trait_item'],
    moduleNodes: ['mod_item'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    // Add file entity
    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentImplTarget: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'function_item': {
          const entity = this.extractFunction(node, filePath);
          if (entity) {
            entities.push(entity);
            relations.push(
              this.createRelation({
                type: currentImplTarget ? 'member_of' : 'contains',
                sourceId: entity.id,
                targetId: currentImplTarget || fileEntityId,
              })
            );
          }
          break;
        }

        case 'struct_item': {
          const entity = this.extractStruct(node, filePath);
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

        case 'enum_item': {
          const entity = this.extractEnum(node, filePath);
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

        case 'trait_item': {
          const entity = this.extractTrait(node, filePath);
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

        case 'impl_item': {
          const result = this.extractImpl(node, filePath);
          if (result) {
            entities.push(result.entity);
            currentImplTarget = result.entity.id;
            relations.push(...result.relations);
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: fileEntityId,
                targetId: result.entity.id,
              })
            );
          }
          break;
        }

        case 'mod_item': {
          const entity = this.extractModule(node, filePath);
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

        case 'use_declaration': {
          const importRelations = this.extractUse(node, fileEntityId);
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
      language: 'rust',
      docstring: this.extractRustDocComment(node),
    });
  }

  private extractStruct(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'struct',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'rust',
      docstring: this.extractRustDocComment(node),
    });
  }

  private extractEnum(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'enum',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'rust',
      docstring: this.extractRustDocComment(node),
    });
  }

  private extractTrait(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'trait',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'rust',
      docstring: this.extractRustDocComment(node),
    });
  }

  private extractImpl(
    node: SyntaxNode,
    filePath: string
  ): { entity: Entity; relations: Relation[] } | null {
    const relations: Relation[] = [];

    // Get impl target type
    const typeNode = this.getChildByField(node, 'type');
    const typeName = typeNode?.text || '<anonymous>';

    // Check if impl for trait
    const traitNode = this.getChildByField(node, 'trait');
    const traitName = traitNode?.text;

    const entity = this.createEntity({
      type: 'impl',
      name: traitName ? `impl ${traitName} for ${typeName}` : `impl ${typeName}`,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'rust',
      metadata: {
        targetType: typeName,
        traitName: traitName,
      },
    });

    // Add implements relation if trait impl
    if (traitName) {
      relations.push(
        this.createRelation({
          type: 'implements',
          sourceId: entity.id,
          targetId: `external:${traitName}`,
        })
      );
    }

    return { entity, relations };
  }

  private extractModule(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'module',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'rust',
      docstring: this.extractRustDocComment(node),
    });
  }

  private extractUse(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];

    // Extract the use path
    const pathNode = this.findChildByType(node, 'use_wildcard') ||
      this.findChildByType(node, 'use_list') ||
      this.findChildByType(node, 'scoped_identifier') ||
      this.findChildByType(node, 'identifier');

    if (pathNode) {
      relations.push(
        this.createRelation({
          type: 'imports',
          sourceId: fileEntityId,
          targetId: `module:${pathNode.text}`,
        })
      );
    }

    return relations;
  }

  private extractRustDocComment(node: SyntaxNode): string | undefined {
    // Look for /// or /** comments before the node
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);

    // Collect all preceding doc comments
    const docComments: string[] = [];
    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'line_comment' && sibling.text.startsWith('///')) {
        docComments.unshift(sibling.text.replace(/^\/\/\/\s?/, ''));
      } else if (sibling.type === 'block_comment' && sibling.text.startsWith('/**')) {
        docComments.unshift(this.cleanDocstring(sibling.text));
        break;
      } else if (sibling.type !== 'line_comment') {
        break;
      }
    }

    return docComments.length > 0 ? docComments.join('\n') : undefined;
  }
}
