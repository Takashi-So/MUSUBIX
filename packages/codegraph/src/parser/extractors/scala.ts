/**
 * @nahisaho/musubix-codegraph - Scala Extractor
 *
 * AST extractor for Scala source files
 *
 * @see REQ-CG-MULTILANG-012
 * @see DES-CG-SCALA
 * @see TSK-CG-033
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Scala language extractor
 */
export class ScalaExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'scala',
    extensions: ['.scala', '.sc'],
    treeSitterName: 'scala',
    functionNodes: ['function_definition', 'function_declaration'],
    classNodes: ['class_definition', 'object_definition', 'case_class_definition'],
    importNodes: ['import_declaration'],
    interfaceNodes: ['trait_definition'],
    moduleNodes: ['package_clause'],
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
        case 'package_clause': {
          const nameNode = this.findChildByType(node, 'package_identifier') ||
            this.findChildByType(node, 'identifier');
          if (nameNode) {
            currentPackage = nameNode.text;
            const entity = this.createEntity({
              type: 'package',
              name: currentPackage,
              filePath,
              startLine: this.getLineNumber(node, 'start'),
              endLine: this.getLineNumber(node, 'end'),
              language: 'scala',
            });
            entities.push(entity);
          }
          break;
        }

        case 'class_definition':
        case 'case_class_definition': {
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

        case 'object_definition': {
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

        case 'trait_definition': {
          const entity = this.extractTrait(node, filePath, currentPackage);
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

        case 'function_definition':
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

        case 'val_definition':
        case 'var_definition': {
          const entity = this.extractVal(node, filePath);
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

  private extractClass(
    node: SyntaxNode,
    filePath: string,
    packageName: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'identifier');
    const name = nameNode?.text || '<anonymous>';
    const fullName = packageName ? `${packageName}.${name}` : name;

    const isCaseClass = node.type === 'case_class_definition';

    return this.createEntity({
      type: isCaseClass ? 'case_class' : 'class',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'scala',
      docstring: this.extractScalaDocComment(node),
    });
  }

  private extractObject(
    node: SyntaxNode,
    filePath: string,
    packageName: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'identifier');
    const name = nameNode?.text || '<anonymous>';
    const fullName = packageName ? `${packageName}.${name}` : name;

    return this.createEntity({
      type: 'object',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'scala',
      docstring: this.extractScalaDocComment(node),
    });
  }

  private extractTrait(
    node: SyntaxNode,
    filePath: string,
    packageName: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'identifier');
    const name = nameNode?.text || '<anonymous>';
    const fullName = packageName ? `${packageName}.${name}` : name;

    return this.createEntity({
      type: 'trait',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'scala',
      docstring: this.extractScalaDocComment(node),
    });
  }

  private extractFunction(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name') ||
      this.findChildByType(node, 'identifier');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'function',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'scala',
      docstring: this.extractScalaDocComment(node),
    });
  }

  private extractVal(node: SyntaxNode, filePath: string): Entity | null {
    const patternNode = this.findChildByType(node, 'identifier');
    const name = patternNode?.text || '<anonymous>';
    const isVar = node.type === 'var_definition';

    return this.createEntity({
      type: isVar ? 'var' : 'val',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'scala',
    });
  }

  private extractHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];
    const extendsClause = this.findChildByType(node, 'extends_clause');

    if (extendsClause) {
      // First type is extends, rest are with (mixins)
      let isFirst = true;
      for (const child of extendsClause.namedChildren) {
        if (child.type === 'type_identifier' || child.type === 'generic_type') {
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
    }

    return relations;
  }

  private extractImport(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];
    const importExpr = this.findChildByType(node, 'import_expression') ||
      this.findChildByType(node, 'stable_identifier');

    if (importExpr) {
      relations.push(
        this.createRelation({
          type: 'imports',
          sourceId: fileEntityId,
          targetId: `module:${importExpr.text}`,
        })
      );
    }

    return relations;
  }

  private extractScalaDocComment(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment' || sibling.type === 'block_comment') {
        if (sibling.text.startsWith('/**')) {
          return this.cleanDocstring(sibling.text);
        }
      } else if (sibling.type !== 'annotation') {
        break;
      }
    }

    return undefined;
  }
}
