/**
 * @nahisaho/musubix-codegraph - C# Extractor
 *
 * AST extractor for C# source files
 *
 * @see REQ-CG-MULTILANG-005
 * @see DES-CG-CSHARP
 * @see TSK-CG-021
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * C# language extractor
 */
export class CSharpExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'csharp',
    extensions: ['.cs'],
    treeSitterName: 'c_sharp',
    functionNodes: ['method_declaration', 'local_function_statement'],
    classNodes: ['class_declaration', 'struct_declaration', 'record_declaration'],
    importNodes: ['using_directive'],
    interfaceNodes: ['interface_declaration'],
    moduleNodes: ['namespace_declaration'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentClassId: string | null = null;
    let currentNamespace: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'namespace_declaration':
        case 'file_scoped_namespace_declaration': {
          const nameNode = this.getChildByField(node, 'name');
          if (nameNode) {
            currentNamespace = nameNode.text;
            const entity = this.createEntity({
              type: 'namespace',
              name: currentNamespace,
              filePath,
              startLine: this.getLineNumber(node, 'start'),
              endLine: this.getLineNumber(node, 'end'),
              language: 'csharp',
            });
            entities.push(entity);
          }
          break;
        }

        case 'class_declaration':
        case 'struct_declaration':
        case 'record_declaration': {
          const entity = this.extractClass(node, filePath, currentNamespace);
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

        case 'interface_declaration': {
          const entity = this.extractInterface(node, filePath, currentNamespace);
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
          const entity = this.extractEnum(node, filePath, currentNamespace);
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

        case 'using_directive': {
          const importRelations = this.extractUsing(node, fileEntityId);
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

  private extractClass(
    node: SyntaxNode,
    filePath: string,
    namespace: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const fullName = namespace ? `${namespace}.${name}` : name;

    const entityType = node.type === 'struct_declaration' ? 'struct' :
      node.type === 'record_declaration' ? 'record' : 'class';

    return this.createEntity({
      type: entityType,
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'csharp',
      docstring: this.extractXmlDoc(node),
    });
  }

  private extractInterface(
    node: SyntaxNode,
    filePath: string,
    namespace: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const fullName = namespace ? `${namespace}.${name}` : name;

    return this.createEntity({
      type: 'interface',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'csharp',
      docstring: this.extractXmlDoc(node),
    });
  }

  private extractEnum(
    node: SyntaxNode,
    filePath: string,
    namespace: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const fullName = namespace ? `${namespace}.${name}` : name;

    return this.createEntity({
      type: 'enum',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'csharp',
      docstring: this.extractXmlDoc(node),
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
      language: 'csharp',
      docstring: this.extractXmlDoc(node),
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
      language: 'csharp',
      docstring: this.extractXmlDoc(node),
    });
  }

  private extractProperty(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'property',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'csharp',
      docstring: this.extractXmlDoc(node),
    });
  }

  private extractHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];
    const baseList = this.findChildByType(node, 'base_list');

    if (baseList) {
      let isFirst = true;
      for (const child of baseList.namedChildren) {
        const typeName = child.type === 'identifier' ? child.text :
          this.findChildByType(child, 'identifier')?.text ||
          this.findChildByType(child, 'generic_name')?.text;
        
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

  private extractUsing(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'qualified_name') ||
      this.findChildByType(node, 'identifier');

    if (nameNode) {
      relations.push(
        this.createRelation({
          type: 'imports',
          sourceId: fileEntityId,
          targetId: `module:${nameNode.text}`,
        })
      );
    }

    return relations;
  }

  private extractXmlDoc(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);
    const docLines: string[] = [];

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment' && sibling.text.startsWith('///')) {
        docLines.unshift(sibling.text.replace(/^\/\/\/\s?/, ''));
      } else if (sibling.type !== 'comment') {
        break;
      }
    }

    return docLines.length > 0 ? docLines.join('\n') : undefined;
  }
}
