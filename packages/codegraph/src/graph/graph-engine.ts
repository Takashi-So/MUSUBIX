/**
 * @nahisaho/musubix-codegraph - Graph Engine
 *
 * Core graph engine for code entity relationship management
 *
 * @see REQ-CG-GRF-001 - Graph construction
 * @see REQ-CG-GRF-002 - Relation inference
 * @see REQ-CG-GRF-003 - Query operations
 * @see DES-CG-003
 * @see TSK-CG-020
 */

import type {
  Entity,
  Relation,
  StorageAdapter,
  GraphOptions,
  GraphQuery,
  QueryResult,
  CallPath,
  ModuleAnalysis,
  CallSite,
} from '../types.js';
import { generateRelationId } from '../types.js';

/**
 * Graph Engine for code entities
 *
 * Manages the code graph, performs queries, and provides
 * traversal algorithms for dependency and call analysis.
 */
export class GraphEngine {
  private storage: StorageAdapter;
  private _options: Required<GraphOptions>;
  private enableInferRelations: boolean;

  constructor(storage: StorageAdapter, options: Partial<GraphOptions> = {}) {
    this.storage = storage;
    this._options = {
      maxDepth: options.maxDepth ?? 10,
      enableCaching: options.enableCaching ?? true,
    };
    this.enableInferRelations = true;
  }

  /**
   * Get max traversal depth
   */
  getMaxDepth(): number {
    return this._options.maxDepth;
  }

  // =========================================================================
  // Entity Operations
  // =========================================================================

  /**
   * Add entity to graph
   */
  async addEntity(entity: Entity): Promise<void> {
    await this.storage.saveEntity(entity);
  }

  /**
   * Add multiple entities
   */
  async addEntities(entities: Entity[]): Promise<void> {
    for (const entity of entities) {
      await this.storage.saveEntity(entity);
    }
  }

  /**
   * Get entity by ID
   */
  async getEntity(id: string): Promise<Entity | null> {
    return this.storage.getEntity(id);
  }

  /**
   * Find entity by name
   */
  async findByName(name: string): Promise<Entity | null> {
    const results = await this.storage.queryEntities({ textSearch: name, limit: 1 });
    return results.find(e => e.name === name) ?? null;
  }

  // =========================================================================
  // Relation Operations
  // =========================================================================

  /**
   * Add relation to graph
   */
  async addRelation(relation: Relation): Promise<void> {
    await this.storage.saveRelation(relation);
  }

  /**
   * Add multiple relations
   */
  async addRelations(relations: Relation[]): Promise<void> {
    for (const relation of relations) {
      await this.storage.saveRelation(relation);
    }
  }

  /**
   * Infer relations from entities
   */
  async inferRelations(entities: Entity[]): Promise<Relation[]> {
    if (!this.enableInferRelations) {
      return [];
    }

    const inferred: Relation[] = [];
    const entityMap = new Map(entities.map(e => [e.name, e]));

    for (const entity of entities) {
      // Infer contains relations (file -> entities)
      if (entity.filePath && entity.type !== 'file') {
        const fileEntity = entities.find(
          e => e.type === 'file' && e.filePath === entity.filePath
        );
        if (fileEntity) {
          inferred.push({
            id: generateRelationId(fileEntity.id, entity.id, 'contains'),
            sourceId: fileEntity.id,
            targetId: entity.id,
            type: 'contains',
            weight: 1.0,
            metadata: {},
          });
        }
      }

      // Infer calls relations from source code analysis
      if (entity.sourceCode && (entity.type === 'function' || entity.type === 'method')) {
        const calls = this.extractCallsFromSource(entity.sourceCode, entityMap);
        for (const callee of calls) {
          inferred.push({
            id: generateRelationId(entity.id, callee.id, 'calls'),
            sourceId: entity.id,
            targetId: callee.id,
            type: 'calls',
            weight: 1.0,
            metadata: {},
          });
        }
      }
    }

    return inferred;
  }

  /**
   * Extract function calls from source code
   */
  private extractCallsFromSource(
    sourceCode: string,
    entityMap: Map<string, Entity>
  ): Entity[] {
    const calls: Entity[] = [];

    // Simple regex to find function calls
    const callRegex = /\b(\w+)\s*\(/g;
    let match;
    while ((match = callRegex.exec(sourceCode)) !== null) {
      const name = match[1];
      // Skip common keywords
      if (['if', 'while', 'for', 'switch', 'catch', 'function', 'class'].includes(name)) {
        continue;
      }
      const entity = entityMap.get(name);
      if (entity && (entity.type === 'function' || entity.type === 'method')) {
        if (!calls.includes(entity)) {
          calls.push(entity);
        }
      }
    }

    return calls;
  }

  // =========================================================================
  // Query Operations
  // =========================================================================

  /**
   * Query the graph
   */
  async query(query: GraphQuery): Promise<QueryResult> {
    const startTime = Date.now();
    const entities = await this.storage.queryEntities(query);

    // Get related relations
    const relationSet = new Set<string>();
    const relations: Relation[] = [];

    for (const entity of entities) {
      const entityRelations = await this.storage.getRelations(entity.id);
      for (const rel of entityRelations) {
        if (!relationSet.has(rel.id)) {
          relationSet.add(rel.id);
          relations.push(rel);
        }
      }
    }

    return {
      entities,
      relations,
      totalCount: entities.length,
      hasMore: false,
      queryTimeMs: Date.now() - startTime,
    };
  }

  /**
   * Find dependencies of an entity
   */
  async findDependencies(entityName: string, depth = 3): Promise<Entity[]> {
    const entity = await this.findByName(entityName);
    if (!entity) return [];

    const visited = new Set<string>();
    const dependencies: Entity[] = [];

    await this.traverseDependencies(entity.id, depth, visited, dependencies);

    return dependencies;
  }

  /**
   * Traverse dependencies recursively
   */
  private async traverseDependencies(
    entityId: string,
    depth: number,
    visited: Set<string>,
    results: Entity[]
  ): Promise<void> {
    if (depth <= 0 || visited.has(entityId)) return;
    visited.add(entityId);

    // Get outgoing relations (things this entity depends on)
    const relations = await this.storage.getRelations(entityId, 'out');

    for (const relation of relations) {
      // Only follow dependency-like relations
      if (['imports', 'uses', 'calls', 'extends', 'implements'].includes(relation.type)) {
        const target = await this.storage.getEntity(relation.targetId);
        if (target && !visited.has(target.id)) {
          results.push(target);
          await this.traverseDependencies(target.id, depth - 1, visited, results);
        }
      }
    }
  }

  /**
   * Find callers of an entity
   */
  async findCallers(entityName: string): Promise<CallPath[]> {
    const entity = await this.findByName(entityName);
    if (!entity) return [];

    const callers: CallPath[] = [];

    // Get incoming 'calls' relations
    const relations = await this.storage.getRelations(entity.id, 'in');

    for (const relation of relations) {
      if (relation.type === 'calls') {
        const caller = await this.storage.getEntity(relation.sourceId);
        if (caller) {
          callers.push({
            from: caller,
            to: entity,
            path: [caller, entity],
            callSites: (relation.metadata?.callSites as CallSite[]) ?? [],
          });
        }
      }
    }

    return callers;
  }

  /**
   * Find callees of an entity
   */
  async findCallees(entityName: string): Promise<CallPath[]> {
    const entity = await this.findByName(entityName);
    if (!entity) return [];

    const callees: CallPath[] = [];

    // Get outgoing 'calls' relations
    const relations = await this.storage.getRelations(entity.id, 'out');

    for (const relation of relations) {
      if (relation.type === 'calls') {
        const callee = await this.storage.getEntity(relation.targetId);
        if (callee) {
          callees.push({
            from: entity,
            to: callee,
            path: [entity, callee],
            callSites: (relation.metadata?.callSites as CallSite[]) ?? [],
          });
        }
      }
    }

    return callees;
  }

  /**
   * Find implementations of an interface
   */
  async findImplementations(interfaceName: string): Promise<Entity[]> {
    const entity = await this.findByName(interfaceName);
    if (!entity) return [];

    const implementations: Entity[] = [];

    // Get incoming 'implements' relations
    const relations = await this.storage.getRelations(entity.id, 'in');

    for (const relation of relations) {
      if (relation.type === 'implements') {
        const impl = await this.storage.getEntity(relation.sourceId);
        if (impl) {
          implementations.push(impl);
        }
      }
    }

    return implementations;
  }

  /**
   * Analyze module structure
   */
  async analyzeModule(filePath: string): Promise<ModuleAnalysis> {
    const entities = await this.storage.queryEntities({ filePath });
    const fileEntity = entities.find(e => e.type === 'file');

    const imports = entities.filter(e => e.type === 'import');
    const exports = entities.filter(e => e.type === 'export');

    // Get dependencies and dependents from relations
    const dependencies = new Set<string>();
    const dependents = new Set<string>();

    for (const entity of entities) {
      const outRels = await this.storage.getRelations(entity.id, 'out');
      for (const rel of outRels) {
        if (['imports', 'uses'].includes(rel.type)) {
          const target = await this.storage.getEntity(rel.targetId);
          if (target?.filePath && target.filePath !== filePath) {
            dependencies.add(target.filePath);
          }
        }
      }

      const inRels = await this.storage.getRelations(entity.id, 'in');
      for (const rel of inRels) {
        if (['imports', 'uses'].includes(rel.type)) {
          const source = await this.storage.getEntity(rel.sourceId);
          if (source?.filePath && source.filePath !== filePath) {
            dependents.add(source.filePath);
          }
        }
      }
    }

    return {
      filePath,
      moduleName: fileEntity?.name ?? filePath.split('/').pop() ?? 'unknown',
      entities,
      imports,
      exports,
      dependencies: Array.from(dependencies),
      dependents: Array.from(dependents),
    };
  }

  // =========================================================================
  // Bulk Operations
  // =========================================================================

  /**
   * Add entities and relations from parse results
   */
  async addParseResults(entities: Entity[], relations: Relation[]): Promise<void> {
    // Add entities first
    await this.addEntities(entities);

    // Infer additional relations
    const inferred = await this.inferRelations(entities);

    // Add all relations
    await this.addRelations([...relations, ...inferred]);
  }

  /**
   * Clear the graph
   */
  async clear(): Promise<void> {
    await this.storage.clear();
  }
}
