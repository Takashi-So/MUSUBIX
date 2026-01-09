/**
 * @nahisaho/musubix-codegraph - HCL/Terraform Extractor
 *
 * AST extractor for HCL/Terraform source files
 *
 * @see REQ-CG-MULTILANG-009
 * @see DES-CG-HCL
 * @see TSK-CG-030
 */

import type { ParseResult, Entity, Relation, EntityType } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * HCL/Terraform language extractor
 */
export class HclExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'hcl',
    extensions: ['.tf', '.tfvars', '.hcl'],
    treeSitterName: 'hcl',
    functionNodes: [],
    classNodes: ['block'],
    importNodes: [],
    interfaceNodes: [],
    moduleNodes: [],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    this.walkTree(tree.rootNode, (node) => {
      if (node.type === 'block') {
        const result = this.extractBlock(node, filePath);
        if (result) {
          entities.push(result.entity);
          relations.push(
            this.createRelation({
              type: 'contains',
              sourceId: fileEntityId,
              targetId: result.entity.id,
            })
          );
          relations.push(...result.relations);
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

  private extractBlock(
    node: SyntaxNode,
    filePath: string
  ): { entity: Entity; relations: Relation[] } | null {
    const relations: Relation[] = [];
    const children = node.namedChildren;
    
    if (children.length === 0) return null;

    // First child is the block type (resource, variable, module, etc.)
    const blockType = children[0]?.text;
    if (!blockType) return null;

    // Second child is typically the resource type for resources
    // Third child is the name
    let name = '<anonymous>';
    let resourceType: string | undefined;

    if (blockType === 'resource' || blockType === 'data') {
      // resource "aws_instance" "example" {}
      if (children[1]?.type === 'string_lit') {
        resourceType = children[1].text.replace(/"/g, '');
      }
      if (children[2]?.type === 'string_lit') {
        name = children[2].text.replace(/"/g, '');
      }
      // resourceType is stored in metadata for reference
    } else if (blockType === 'variable' || blockType === 'output' || blockType === 'locals') {
      // variable "name" {}
      if (children[1]?.type === 'string_lit') {
        name = children[1].text.replace(/"/g, '');
      }
    } else if (blockType === 'module') {
      // module "name" {}
      if (children[1]?.type === 'string_lit') {
        name = children[1].text.replace(/"/g, '');
      }
      // Extract module source for relations
      const body = this.findChildByType(node, 'body');
      if (body) {
        const sourceAttr = this.findAttribute(body, 'source');
        if (sourceAttr) {
          relations.push(
            this.createRelation({
              type: 'imports',
              sourceId: `hcl:module:${name}`,
              targetId: `module:${sourceAttr}`,
            })
          );
        }
      }
    } else if (blockType === 'provider') {
      // provider "aws" {}
      if (children[1]?.type === 'string_lit') {
        name = children[1].text.replace(/"/g, '');
      }
    } else if (blockType === 'terraform') {
      name = 'terraform';
    }

    // Map HCL block types to EntityType
    const entityType: EntityType = this.mapBlockTypeToEntityType(blockType);

    const entity = this.createEntity({
      type: entityType,
      name: `${blockType}.${name}`,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'hcl',
      metadata: {
        blockType,
        resourceType,
      },
    });

    return { entity, relations };
  }

  private mapBlockTypeToEntityType(blockType: string): EntityType {
    switch (blockType) {
      case 'resource': return 'resource';
      case 'data': return 'data';
      case 'provider': return 'provider';
      case 'locals': return 'locals';
      case 'output': return 'output';
      case 'terraform': return 'terraform';
      case 'variable': return 'variable';
      case 'module': return 'module';
      default: return 'unknown';
    }
  }

  private findAttribute(body: SyntaxNode, attrName: string): string | null {
    for (const child of body.namedChildren) {
      if (child.type === 'attribute') {
        const nameNode = this.getChildByField(child, 'name');
        if (nameNode?.text === attrName) {
          const valueNode = this.getChildByField(child, 'val');
          if (valueNode?.type === 'string_lit') {
            return valueNode.text.replace(/"/g, '');
          }
        }
      }
    }
    return null;
  }
}
