/**
 * @nahisaho/musubix-codegraph - Python Extractor
 *
 * AST extractor for Python source files
 *
 * @see REQ-CG-AST-001
 * @see DES-CG-PYTHON
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * Python language extractor
 */
export class PythonExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'python',
    extensions: ['.py', '.pyw'],
    treeSitterName: 'python',
    functionNodes: ['function_definition'],
    classNodes: ['class_definition'],
    importNodes: ['import_statement', 'import_from_statement'],
    interfaceNodes: [],
    moduleNodes: [],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];
    const startTime = Date.now();

    // Add file entity
    entities.push(this.createFileEntity(filePath, sourceCode));
    const fileEntityId = entities[0].id;

    let currentClassId: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'function_definition': {
          const entity = this.extractFunction(node, filePath);
          if (entity) {
            entities.push(entity);
            relations.push(
              this.createRelation({
                type: currentClassId ? 'member_of' : 'contains',
                sourceId: entity.id,
                targetId: currentClassId || fileEntityId,
              })
            );
          }
          break;
        }

        case 'class_definition': {
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
            const heritage = this.extractInheritance(node, entity.id);
            relations.push(...heritage);
          }
          break;
        }

        case 'import_statement':
        case 'import_from_statement': {
          const importRelations = this.extractImport(node, fileEntityId);
          relations.push(...importRelations);
          break;
        }

        case 'decorated_definition': {
          // Handle decorated functions/classes
          const definition = this.findChildByType(node, 'function_definition') ||
            this.findChildByType(node, 'class_definition');
          if (definition) {
            // Will be processed in next iteration
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

  private extractFunction(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    // Extract docstring (first string in body)
    const body = this.getChildByField(node, 'body');
    let docstring: string | undefined;
    if (body?.namedChildren[0]?.type === 'expression_statement') {
      const expr = body.namedChildren[0].namedChildren[0];
      if (expr?.type === 'string') {
        docstring = this.cleanDocstring(expr.text);
      }
    }

    return this.createEntity({
      type: 'function',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'python',
      docstring,
    });
  }

  private extractClass(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    // Extract docstring
    const body = this.getChildByField(node, 'body');
    let docstring: string | undefined;
    if (body?.namedChildren[0]?.type === 'expression_statement') {
      const expr = body.namedChildren[0].namedChildren[0];
      if (expr?.type === 'string') {
        docstring = this.cleanDocstring(expr.text);
      }
    }

    return this.createEntity({
      type: 'class',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'python',
      docstring,
    });
  }

  private extractInheritance(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];
    const argumentList = this.getChildByField(node, 'superclasses');

    if (argumentList) {
      for (const arg of argumentList.namedChildren) {
        const baseName = arg.type === 'identifier' ? arg.text : arg.text;
        if (baseName) {
          relations.push(
            this.createRelation({
              type: 'extends',
              sourceId: classId,
              targetId: `external:${baseName}`,
            })
          );
        }
      }
    }

    return relations;
  }

  private extractImport(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];

    if (node.type === 'import_statement') {
      // import x, y, z
      for (const child of node.namedChildren) {
        if (child.type === 'dotted_name' || child.type === 'aliased_import') {
          const moduleName =
            child.type === 'aliased_import'
              ? this.findChildByType(child, 'dotted_name')?.text
              : child.text;
          if (moduleName) {
            relations.push(
              this.createRelation({
                type: 'imports',
                sourceId: fileEntityId,
                targetId: `module:${moduleName}`,
              })
            );
          }
        }
      }
    } else {
      // from x import y
      const moduleNode = this.getChildByField(node, 'module_name');
      const moduleName = moduleNode?.text;
      if (moduleName) {
        relations.push(
          this.createRelation({
            type: 'imports',
            sourceId: fileEntityId,
            targetId: `module:${moduleName}`,
          })
        );
      }
    }

    return relations;
  }
}
