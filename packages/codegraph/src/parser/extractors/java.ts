/**
 * @nahisaho/musubix-codegraph - Java Extractor
 *
 * AST extractor for Java source files
 *
 * @see REQ-CG-MULTILANG-003
 * @see DES-CG-JAVA
 * @see TSK-CG-012
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Java language extractor
 */
export class JavaExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'java',
    extensions: ['.java'],
    treeSitterName: 'java',
    functionNodes: ['method_declaration', 'constructor_declaration'],
    classNodes: ['class_declaration'],
    importNodes: ['import_declaration'],
    interfaceNodes: ['interface_declaration'],
    moduleNodes: ['package_declaration'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    // Add file entity
    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentClassId: string | null = null;
    let packageName: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'package_declaration': {
          const nameNode = this.findChildByType(node, 'scoped_identifier') ||
            this.findChildByType(node, 'identifier');
          if (nameNode) {
            packageName = nameNode.text;
            const entity = this.createEntity({
              type: 'package',
              name: packageName,
              filePath,
              startLine: this.getLineNumber(node, 'start'),
              endLine: this.getLineNumber(node, 'end'),
              language: 'java',
            });
            entities.push(entity);
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
            const heritage = this.extractHeritage(node, entity.id);
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

        case 'enum_declaration': {
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

        case 'method_declaration': {
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

        case 'constructor_declaration': {
          const entity = this.extractConstructor(node, filePath);
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

        case 'field_declaration': {
          const fieldEntities = this.extractField(node, filePath);
          for (const entity of fieldEntities) {
            entities.push(entity);
            if (currentClassId) {
              relations.push(
                this.createRelation({
                  type: 'member_of',
                  sourceId: entity.id,
                  targetId: currentClassId,
                })
              );
            }
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

  private extractClass(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'class',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'java',
      docstring: this.extractJavadoc(node),
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
      language: 'java',
      docstring: this.extractJavadoc(node),
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
      language: 'java',
      docstring: this.extractJavadoc(node),
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
      language: 'java',
      docstring: this.extractJavadoc(node),
    });
  }

  private extractConstructor(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<constructor>';

    return this.createEntity({
      type: 'constructor',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'java',
      docstring: this.extractJavadoc(node),
    });
  }

  private extractField(node: SyntaxNode, filePath: string): Entity[] {
    const entities: Entity[] = [];
    const declarators = node.namedChildren.filter(
      (child) => child.type === 'variable_declarator'
    );

    for (const declarator of declarators) {
      const nameNode = this.getChildByField(declarator, 'name');
      const name = nameNode?.text || '<anonymous>';

      entities.push(
        this.createEntity({
          type: 'field',
          name,
          filePath,
          startLine: this.getLineNumber(node, 'start'),
          endLine: this.getLineNumber(node, 'end'),
          language: 'java',
        })
      );
    }

    return entities;
  }

  private extractHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];

    // Check superclass
    const superclassNode = this.getChildByField(node, 'superclass');
    if (superclassNode) {
      const typeName = this.findChildByType(superclassNode, 'type_identifier')?.text;
      if (typeName) {
        relations.push(
          this.createRelation({
            type: 'extends',
            sourceId: classId,
            targetId: `external:${typeName}`,
          })
        );
      }
    }

    // Check interfaces
    const interfacesNode = this.getChildByField(node, 'interfaces');
    if (interfacesNode) {
      for (const child of interfacesNode.namedChildren) {
        const typeName =
          child.type === 'type_identifier'
            ? child.text
            : this.findChildByType(child, 'type_identifier')?.text;
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

    return relations;
  }

  private extractImport(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];
    const pathNode =
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

  private extractJavadoc(node: SyntaxNode): string | undefined {
    // Look for block comment before the node
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'block_comment' && sibling.text.startsWith('/**')) {
        return this.cleanDocstring(sibling.text);
      } else if (sibling.type !== 'line_comment' && sibling.type !== 'modifiers') {
        break;
      }
    }

    return undefined;
  }
}
