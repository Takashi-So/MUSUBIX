/**
 * @nahisaho/musubix-codegraph - C/C++ Extractor
 *
 * AST extractor for C and C++ source files
 *
 * @see REQ-CG-MULTILANG-006, REQ-CG-MULTILANG-007
 * @see DES-CG-C, DES-CG-CPP
 * @see TSK-CG-022, TSK-CG-023
 */

import type { ParseResult, Entity, Relation } from '../../types.js';
import {
  BaseExtractor,
  type LanguageConfig,
  type SyntaxTree,
  type SyntaxNode,
} from './base-extractor.js';

/**
 * C language extractor
 */
export class CExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'c',
    extensions: ['.c', '.h'],
    treeSitterName: 'c',
    functionNodes: ['function_definition'],
    classNodes: ['struct_specifier', 'union_specifier'],
    importNodes: ['preproc_include'],
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
      switch (node.type) {
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

        case 'struct_specifier': {
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

        case 'union_specifier': {
          const entity = this.extractUnion(node, filePath);
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

        case 'enum_specifier': {
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

        case 'type_definition': {
          const entity = this.extractTypedef(node, filePath);
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

        case 'preproc_include': {
          const importRelations = this.extractInclude(node, fileEntityId);
          relations.push(...importRelations);
          break;
        }

        case 'preproc_def':
        case 'preproc_function_def': {
          const entity = this.extractMacro(node, filePath);
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

  protected extractFunction(node: SyntaxNode, filePath: string): Entity | null {
    const declarator = this.getChildByField(node, 'declarator');
    let name = '<anonymous>';

    if (declarator) {
      const nameNode = this.findChildByType(declarator, 'identifier') ||
        this.getChildByField(declarator, 'declarator');
      if (nameNode?.type === 'identifier') {
        name = nameNode.text;
      } else if (nameNode) {
        const innerName = this.findChildByType(nameNode, 'identifier');
        if (innerName) name = innerName.text;
      }
    }

    return this.createEntity({
      type: 'function',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: this.config.name,
      docstring: this.extractCDocComment(node),
    });
  }

  protected extractStruct(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    // Only extract if it has a body (not just a forward declaration)
    const body = this.findChildByType(node, 'field_declaration_list');
    if (!body && !nameNode) return null;

    return this.createEntity({
      type: 'struct',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: this.config.name,
      docstring: this.extractCDocComment(node),
    });
  }

  protected extractUnion(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'union',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: this.config.name,
      docstring: this.extractCDocComment(node),
    });
  }

  protected extractEnum(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'enum',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: this.config.name,
      docstring: this.extractCDocComment(node),
    });
  }

  protected extractTypedef(node: SyntaxNode, filePath: string): Entity | null {
    const declarator = this.getChildByField(node, 'declarator');
    const nameNode = declarator ? this.findChildByType(declarator, 'type_identifier') : null;
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'typedef',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: this.config.name,
    });
  }

  protected extractMacro(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'macro',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: this.config.name,
    });
  }

  protected extractInclude(node: SyntaxNode, fileEntityId: string): Relation[] {
    const relations: Relation[] = [];
    const pathNode = this.getChildByField(node, 'path') ||
      this.findChildByType(node, 'string_literal') ||
      this.findChildByType(node, 'system_lib_string');

    if (pathNode) {
      const path = pathNode.text.replace(/[<>"]/g, '');
      relations.push(
        this.createRelation({
          type: 'imports',
          sourceId: fileEntityId,
          targetId: `module:${path}`,
        })
      );
    }

    return relations;
  }

  protected extractCDocComment(node: SyntaxNode): string | undefined {
    const parent = node.parent;
    if (!parent) return undefined;

    const siblings = parent.children;
    const nodeIndex = siblings.indexOf(node);

    for (let i = nodeIndex - 1; i >= 0; i--) {
      const sibling = siblings[i];
      if (sibling.type === 'comment') {
        if (sibling.text.startsWith('/**') || sibling.text.startsWith('/*!')) {
          return this.cleanDocstring(sibling.text);
        }
        if (sibling.text.startsWith('//')) {
          // Collect consecutive line comments
          const lines: string[] = [sibling.text.replace(/^\/\/\s?/, '')];
          for (let j = i - 1; j >= 0; j--) {
            if (siblings[j].type === 'comment' && siblings[j].text.startsWith('//')) {
              lines.unshift(siblings[j].text.replace(/^\/\/\s?/, ''));
            } else {
              break;
            }
          }
          return lines.join('\n');
        }
      } else {
        break;
      }
    }

    return undefined;
  }
}

/**
 * C++ language extractor
 */
export class CppExtractor extends CExtractor {
  override readonly config: LanguageConfig = {
    name: 'cpp',
    extensions: ['.cpp', '.cc', '.cxx', '.hpp', '.hh', '.hxx', '.h++'],
    treeSitterName: 'cpp',
    functionNodes: ['function_definition'],
    classNodes: ['class_specifier', 'struct_specifier'],
    importNodes: ['preproc_include'],
    interfaceNodes: [],
    moduleNodes: ['namespace_definition'],
  };

  override extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const result = super.extract(tree, filePath, sourceCode);
    const entities = [...result.entities];
    const relations = [...result.relations];
    const fileEntityId = entities[0].id;

    // Track current context for future method-class relationships
    void 0; // placeholder for tracking context
    let currentNamespace: string | null = null;

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'namespace_definition': {
          const entity = this.extractNamespace(node, filePath);
          if (entity) {
            entities.push(entity);
            currentNamespace = entity.name;
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

        case 'class_specifier': {
          const entity = this.extractClass(node, filePath, currentNamespace);
          if (entity) {
            entities.push(entity);
            relations.push(
              this.createRelation({
                type: 'contains',
                sourceId: fileEntityId,
                targetId: entity.id,
              })
            );
            const heritage = this.extractCppHeritage(node, entity.id);
            relations.push(...heritage);
          }
          break;
        }

        case 'template_declaration': {
          const entity = this.extractTemplate(node, filePath);
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
      }
    });

    return {
      ...result,
      entities,
      relations,
    };
  }

  private extractNamespace(node: SyntaxNode, filePath: string): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';

    return this.createEntity({
      type: 'namespace',
      name,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'cpp',
    });
  }

  private extractClass(
    node: SyntaxNode,
    filePath: string,
    namespace: string | null
  ): Entity | null {
    const nameNode = this.getChildByField(node, 'name');
    const name = nameNode?.text || '<anonymous>';
    const fullName = namespace ? `${namespace}::${name}` : name;

    const body = this.findChildByType(node, 'field_declaration_list');
    if (!body && !nameNode) return null;

    return this.createEntity({
      type: 'class',
      name: fullName,
      filePath,
      startLine: this.getLineNumber(node, 'start'),
      endLine: this.getLineNumber(node, 'end'),
      language: 'cpp',
      docstring: this.extractCDocComment(node),
    });
  }

  private extractTemplate(node: SyntaxNode, filePath: string): Entity | null {
    // Find the templated entity (class or function)
    const classNode = this.findChildByType(node, 'class_specifier');
    const funcNode = this.findChildByType(node, 'function_definition');

    if (classNode) {
      const nameNode = this.getChildByField(classNode, 'name');
      const name = nameNode?.text || '<anonymous>';
      return this.createEntity({
        type: 'template_class',
        name,
        filePath,
        startLine: this.getLineNumber(node, 'start'),
        endLine: this.getLineNumber(node, 'end'),
        language: 'cpp',
        docstring: this.extractCDocComment(node),
      });
    }

    if (funcNode) {
      const entity = this.extractFunction(funcNode, filePath);
      if (entity) {
        entity.type = 'template_function';
      }
      return entity;
    }

    return null;
  }

  private extractCppHeritage(node: SyntaxNode, classId: string): Relation[] {
    const relations: Relation[] = [];
    const baseClause = this.findChildByType(node, 'base_class_clause');

    if (baseClause) {
      for (const child of baseClause.namedChildren) {
        if (child.type === 'base_class_specifier') {
          const typeName = this.findChildByType(child, 'type_identifier')?.text ||
            this.findChildByType(child, 'qualified_identifier')?.text;
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
      }
    }

    return relations;
  }
}
