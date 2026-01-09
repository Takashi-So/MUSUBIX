/**
 * @nahisaho/musubix-codegraph - PHP Extractor
 *
 * AST extractor for PHP source files
 *
 * @see REQ-CG-MULTILANG-004
 * @see DES-CG-PHP
 * @see TSK-CG-020
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * PHP language extractor
 */
export class PhpExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'php',
    extensions: ['.php', '.phtml'],
    treeSitterName: 'php',
    functionNodes: ['function_definition', 'method_declaration'],
    classNodes: ['class_declaration'],
    importNodes: ['use_declaration', 'namespace_use_declaration'],
    interfaceNodes: ['interface_declaration'],
    moduleNodes: ['namespace_definition'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    // Add file entity
    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentClassId: string | null = null;
    let currentNamespace: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'namespace_definition': {
          const nameNode = this.getChildByField(node, 'name');
          if (nameNode) {
            currentNamespace = nameNode.text;
            const entity = this.createEntity({
              type: 'namespace',
              name: currentNamespace,
              filePath,
              startLine: this.getLineNumber(node, 'start'),
              endLine: this.getLineNumber(node, 'end'),
              language: 'php',
            });
            entities.push(entity);
          }
          break;
        }

        case 'class_declaration': {
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
            // Extract inheritance
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

        case 'trait_declaration': {
          const entity = this.extractTrait(node, filePath, currentNamespace);
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

        case 'function_definition': {
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

        case 'use_declaration':
        case 'namespace_use_declaration': {
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

  private extractClass(
    node: SyntaxNode,
    filePath: string,
    namespace: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const fullName = namespace ? `${namespace}\\${name}` : name;

    return this.createEntity({
      type: 'class',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'php',
      docstring: this.extractPhpDocComment(node),
    });
  }

  private extractInterface(
    node: SyntaxNode,
    filePath: string,
    namespace: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const fullName = namespace ? `${namespace}\\${name}` : name;

    return this.createEntity({
      type: 'interface',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'php',
      docstring: this.extractPhpDocComment(node),
    });
  }

  private extractTrait(
    node: SyntaxNode,
    filePath: string,
    namespace: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const fullName = namespace ? `${namespace}\\${name}` : name;

    return this.createEntity({
      type: 'trait',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'php',
      docstring: this.extractPhpDocComment(node),
    });
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
      language: 'php',
      docstring: this.extractPhpDocComment(node),
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
      language: 'php',
      docstring: this.extractPhpDocComment(node),
    });
  }

  private extractHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];

    // Check extends
    const baseClauseNode = this.findChildByType(node, 'base_clause');
    if (baseClauseNode) {
      const typeName = this.findChildByType(baseClauseNode, 'name')?.text ||
        this.findChildByType(baseClauseNode, 'qualified_name')?.text;
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

    // Check implements
    const classInterfaceClause = this.findChildByType(node, 'class_interface_clause');
    if (classInterfaceClause) {
      for (const child of classInterfaceClause.namedChildren) {
        const typeName = child.type === 'name' ? child.text :
          this.findChildByType(child, 'name')?.text ||
          child.text;
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

  private extractUse(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];

    const useClause = this.findChildByType(node, 'namespace_use_clause') ||
      this.findChildByType(node, 'use_clause');
    
    if (useClause) {
      const nameNode = this.findChildByType(useClause, 'qualified_name') ||
        this.findChildByType(useClause, 'name');
      if (nameNode) {
        relations.push(
          this.createRelation({
            type: 'imports',
            sourceId: fileEntityId,
            targetId: `module:${nameNode.text}`,
          })
        );
      }
    }

    return relations;
  }

  private extractPhpDocComment(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment' && sibling.text.startsWith('/**')) {
        return this.cleanDocstring(sibling.text);
      } else if (sibling.type !== 'comment') {
        break;
      }
    }

    return undefined;
  }
}
