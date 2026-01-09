/**
 * @nahisaho/musubix-codegraph - Swift Extractor
 *
 * AST extractor for Swift source files
 *
 * @see REQ-CG-MULTILANG-011
 * @see DES-CG-SWIFT
 * @see TSK-CG-032
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Swift language extractor
 */
export class SwiftExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'swift',
    extensions: ['.swift'],
    treeSitterName: 'swift',
    functionNodes: ['function_declaration', 'init_declaration'],
    classNodes: ['class_declaration', 'struct_declaration'],
    importNodes: ['import_declaration'],
    interfaceNodes: ['protocol_declaration'],
    moduleNodes: [],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentClassId: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
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
            const heritage = this.extractHeritage(node, entity.id);
            relations.push(...heritage);
          }
          break;
        }

        case 'struct_declaration': {
          const entity = this.extractStruct(node, filePath);
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
            const heritage = this.extractHeritage(node, entity.id);
            relations.push(...heritage);
          }
          break;
        }

        case 'protocol_declaration': {
          const entity = this.extractProtocol(node, filePath);
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

        case 'extension_declaration': {
          const entity = this.extractExtension(node, filePath);
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

        case 'function_declaration': {
          const entity = this.extractFunction(node, filePath);
          if (entity) {
            entities.push(entity);
            const parentId = currentClassId || fileEntityId;
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

        case 'init_declaration': {
          const entity = this.extractInit(node, filePath);
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

        case 'property_declaration': {
          const entity = this.extractProperty(node, filePath);
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
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'type_identifier') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'class',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
      docstring: this.extractSwiftDocComment(node),
    });
  }

  private extractStruct(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'type_identifier') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'struct',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
      docstring: this.extractSwiftDocComment(node),
    });
  }

  private extractProtocol(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'type_identifier') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'protocol',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
      docstring: this.extractSwiftDocComment(node),
    });
  }

  private extractEnum(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'type_identifier') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'enum',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
      docstring: this.extractSwiftDocComment(node),
    });
  }

  private extractExtension(node: SyntaxNode, filePath: string): Entity | null {
    const typeNode = this.getChildByField(node, 'extended_type') ||
      this.findChildByType(node, 'type_identifier');
    const name = typeNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'extension',
      name: `extension ${name}`,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
      metadata: {
        extendedType: name,
      },
    });
  }

  private extractFunction(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'function',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
      docstring: this.extractSwiftDocComment(node),
    });
  }

  private extractInit(node: SyntaxNode, filePath: string): Entity | null {
    return this.createEntity({
      type: 'initializer',
      name: 'init',
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
      docstring: this.extractSwiftDocComment(node),
    });
  }

  private extractProperty(node: SyntaxNode, filePath: string): Entity | null {
    const patternNode = this.findChildByType(node, 'pattern');
    const nameNode = patternNode ? 
      this.findChildByType(patternNode, 'simple_identifier') : null;
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'property',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'swift',
    });
  }

  private extractHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];
    const inheritanceClause = this.findChildByType(node, 'type_inheritance_clause');

    if (inheritanceClause) {
      let isFirst = true;
      for (const child of inheritanceClause.namedChildren) {
        const typeName = child.type === 'type_identifier' ? child.text :
          this.findChildByType(child, 'type_identifier')?.text;
        if (typeName) {
          relations.push(
            this.createRelation({
              type: isFirst ? 'extends' : 'implements',
              sourceId: classId,
              targetId: `external:${typeName}`,
            })
          );
          isFirst = false;
        }
      }
    }

    return relations;
  }

  private extractImport(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];
    const identNode = this.findChildByType(node, 'identifier') ||
      this.findChildByType(node, 'simple_identifier');

    if (identNode) {
      relations.push(
        this.createRelation({
          type: 'imports',
          sourceId: fileEntityId,
          targetId: `module:${identNode.text}`,
        })
      );
    }

    return relations;
  }

  private extractSwiftDocComment(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);
    const docLines: string[] = [];

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment') {
        if (sibling.text.startsWith('///')) {
          docLines.unshift(sibling.text.replace(/^\/\/\/\s?/, ''));
        } else if (sibling.text.startsWith('/**')) {
          return this.cleanDocstring(sibling.text);
        }
      } else {
        break;
      }
    }

    return docLines.length > 0 ? docLines.join('\n') : undefined;
  }
}
