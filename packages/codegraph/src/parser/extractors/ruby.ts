/**
 * @nahisaho/musubix-codegraph - Ruby Extractor
 *
 * AST extractor for Ruby source files
 *
 * @see REQ-CG-MULTILANG-008
 * @see DES-CG-RUBY
 * @see TSK-CG-024
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Ruby language extractor
 */
export class RubyExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'ruby',
    extensions: ['.rb', '.rake', '.gemspec'],
    treeSitterName: 'ruby',
    functionNodes: ['method', 'singleton_method'],
    classNodes: ['class'],
    importNodes: ['call'],
    interfaceNodes: [],
    moduleNodes: ['module'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentClassId: string | null = null;
    let currentModuleId: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'module': {
          const entity = this.extractModule(node, filePath);
          if (entity) {
            entities.push(entity);
            currentModuleId = entity.id;
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

        case 'class': {
          const entity = this.extractClass(node, filePath);
          if (entity) {
            entities.push(entity);
            currentClassId = entity.id;
            const parentId = currentModuleId || fileEntityId;
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: parentId,
                targetId: entity.id,
              })
            );
            const heritage = this.extractHeritage(node, entity.id);
            relations.push(...heritage);
          }
          break;
        }

        case 'method':
        case 'singleton_method': {
          const entity = this.extractMethod(node, filePath);
          if (entity) {
            entities.push(entity);
            const parentId = currentClassId || currentModuleId || fileEntityId;
            relations.push(
              this.createRelation({
                type: currentClassId ? 'member_of' : 'contains',
                sourceId: entity.id,
                targetId: parentId,
              })
            );
          }
          break;
        }

        case 'call': {
          // Check for require/require_relative
          const methodNode = this.getChildByField(node, 'method');
          if (methodNode) {
            const methodName = methodNode.text;
            if (methodName === 'require' || methodName === 'require_relative') {
              const importRelations = this.extractRequire(node, fileEntityId);
              relations.push(...importRelations);
            }
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

  private extractModule(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'module',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'ruby',
      docstring: this.extractRubyDocComment(node),
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
      language: 'ruby',
      docstring: this.extractRubyDocComment(node),
    });
  }

  private extractMethod(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const isSingleton = node.type === 'singleton_method';

    return this.createEntity({
      type: 'method',
      name: isSingleton ? `self.${name}` : name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'ruby',
      docstring: this.extractRubyDocComment(node),
      metadata: {
        singleton: isSingleton,
      },
    });
  }

  private extractHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];
    const superclassNode = this.getChildByField(node, 'superclass');

    if (superclassNode) {
      const name = superclassNode.text;
      relations.push(
        this.createRelation({
          type: 'extends',
          sourceId: classId,
          targetId: `external:${name}`,
        })
      );
    }

    return relations;
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

  private extractRubyDocComment(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);
    const docLines: string[] = [];

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment') {
        docLines.unshift(sibling.text.replace(/^#\s?/, ''));
      } else {
        break;
      }
    }

    return docLines.length > 0 ? docLines.join('\n') : undefined;
  }
}
