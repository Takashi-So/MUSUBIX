/**
 * @nahisaho/musubix-codegraph - Kotlin Extractor
 *
 * AST extractor for Kotlin source files
 *
 * @see REQ-CG-MULTILANG-010
 * @see DES-CG-KOTLIN
 * @see TSK-CG-031
 */

import type { ParseResult, Entity, Relation, EntityType } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Kotlin language extractor
 */
export class KotlinExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'kotlin',
    extensions: ['.kt', '.kts'],
    treeSitterName: 'kotlin',
    functionNodes: ['function_declaration'],
    classNodes: ['class_declaration', 'object_declaration'],
    importNodes: ['import_header'],
    interfaceNodes: ['interface_declaration'],
    moduleNodes: ['package_header'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentClassId: string | null = null;
    let currentPackage: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'package_header': {
          const nameNode = this.findChildByType(node, 'identifier');
          if (nameNode) {
            currentPackage = nameNode.text;
            const entity = this.createEntity({
              type: 'package',
              name: currentPackage,
              filePath,
              startLine: this.getLineNumber(node, 'start'),
              endLine: this.getLineNumber(node, 'end'),
              language: 'kotlin',
            });
            entities.push(entity);
          }
          break;
        }

        case 'class_declaration': {
          const entity = this.extractClass(node, filePath, currentPackage);
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

        case 'object_declaration': {
          const entity = this.extractObject(node, filePath, currentPackage);
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

        case 'interface_declaration': {
          const entity = this.extractInterface(node, filePath, currentPackage);
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

        case 'import_header': {
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

  private extractClass(
    node: SyntaxNode,
    filePath: string,
    packageName: string | null
  ): Entity | null {
    const nameNode = this.findChildByType(node, 'type_identifier') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';
    const fullName = packageName ? `${packageName}.${name}` : name;

    // Check if data class, sealed class, etc. - map to valid EntityType
    const modifiers = this.findChildByType(node, 'modifiers');
    let classKind: EntityType = 'class';
    if (modifiers) {
      if (modifiers.text.includes('data')) classKind = 'class'; // data class -> class
      else if (modifiers.text.includes('sealed')) classKind = 'class'; // sealed class -> class
      else if (modifiers.text.includes('enum')) classKind = 'enum'; // enum class -> enum
    }

    return this.createEntity({
      type: classKind,
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'kotlin',
      docstring: this.extractKDocComment(node),
      metadata: {
        kotlinClassKind: modifiers?.text.includes('data') ? 'data_class' :
          modifiers?.text.includes('sealed') ? 'sealed_class' :
          modifiers?.text.includes('enum') ? 'enum_class' : 'class',
      },
    });
  }

  private extractObject(
    node: SyntaxNode,
    filePath: string,
    packageName: string | null
  ): Entity | null {
    const nameNode = this.findChildByType(node, 'type_identifier') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';
    const fullName = packageName ? `${packageName}.${name}` : name;

    return this.createEntity({
      type: 'object',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'kotlin',
      docstring: this.extractKDocComment(node),
    });
  }

  private extractInterface(
    node: SyntaxNode,
    filePath: string,
    packageName: string | null
  ): Entity | null {
    const nameNode = this.findChildByType(node, 'type_identifier') ||
      this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';
    const fullName = packageName ? `${packageName}.${name}` : name;

    return this.createEntity({
      type: 'interface',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'kotlin',
      docstring: this.extractKDocComment(node),
    });
  }

  private extractFunction(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.findChildByType(node, 'simple_identifier');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'function',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'kotlin',
      docstring: this.extractKDocComment(node),
    });
  }

  private extractProperty(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.findChildByType(node, 'variable_declaration');
    const identNode = nameNode ? this.findChildByType(nameNode, 'simple_identifier') : null;
    const name = identNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'property',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'kotlin',
    });
  }

  private extractHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];
    const delegationSpecifiers = this.findChildByType(node, 'delegation_specifiers');

    if (delegationSpecifiers) {
      let isFirst = true;
      for (const child of delegationSpecifiers.namedChildren) {
        const typeName = this.findChildByType(child, 'type_identifier')?.text ||
          this.findChildByType(child, 'user_type')?.text;
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
    const identNode = this.findChildByType(node, 'identifier');

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

  private extractKDocComment(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'multiline_comment' && sibling.text.startsWith('/**')) {
        return this.cleanDocstring(sibling.text);
      } else if (sibling.type !== 'multiline_comment' && sibling.type !== 'line_comment') {
        break;
      }
    }

    return undefined;
  }
}
