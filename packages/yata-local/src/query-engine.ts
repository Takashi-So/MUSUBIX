/**
 * YATA Local - Query Engine
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/query-engine
 *
 * @see REQ-YL-QUERY-001 ~ REQ-YL-QUERY-005
 */

import type {
  Entity,
  EntityType,
  Relationship,
  RelationType,
  GraphQuery,
  QueryResult,
  Path,
  Subgraph,
  GraphPattern,
  PatternMatch,
  QueryOptions,
} from './types.js';
import type { YataDatabase } from './database.js';

/**
 * Query engine for traversing and querying the knowledge graph
 */
export class QueryEngine {
  constructor(private db: YataDatabase) {}

  /**
   * Execute graph query
   * @see REQ-YL-QUERY-001
   */
  query(query: GraphQuery, options: Partial<QueryOptions> = {}): QueryResult {
    const startTime = Date.now();
    const limit = options.limit ?? 100;
    const offset = options.offset ?? 0;

    let entities: Entity[] = [];
    let relationships: Relationship[] = [];
    let totalCount = 0;

    // Execute entity query
    if (query.entityFilters) {
      const result = this.db.queryEntities(
        {
          type: query.entityFilters.types,
          namePattern: query.entityFilters.namePattern,
          namespace: query.entityFilters.namespace,
        },
        limit,
        offset
      );
      entities = result.entities;
      totalCount = result.totalCount;
    }

    // Execute text search
    if (query.textSearch) {
      const searchResults = this.db.searchEntities(query.textSearch, limit);
      entities = [...entities, ...searchResults];
      totalCount = entities.length;
    }

    // Get relationships for result entities
    if (query.includeRelationships !== false && entities.length > 0) {
      const entityIds = new Set(entities.map(e => e.id));
      const relSet = new Map<string, Relationship>();

      for (const entity of entities) {
        const rels = this.db.getRelationships(entity.id);
        for (const rel of rels) {
          // Filter by relationship type if specified
          if (query.relationshipFilters?.types) {
            if (!query.relationshipFilters.types.includes(rel.type)) {
              continue;
            }
          }
          // Only include if source or target is in result
          if (entityIds.has(rel.sourceId) || entityIds.has(rel.targetId)) {
            relSet.set(rel.id, rel);
          }
        }
      }
      relationships = Array.from(relSet.values());
    }

    const executionTime = Date.now() - startTime;

    return {
      entities,
      relationships,
      totalCount,
      hasMore: offset + entities.length < totalCount,
      executionTime,
    };
  }

  /**
   * Find shortest path between two entities
   * @see REQ-YL-QUERY-002
   */
  findPath(
    startId: string,
    endId: string,
    options: {
      maxDepth?: number;
      relationshipTypes?: RelationType[];
      direction?: 'forward' | 'backward' | 'both';
    } = {}
  ): Path | null {
    const maxDepth = options.maxDepth ?? 10;
    const direction = options.direction ?? 'both';

    // BFS for shortest path
    const visited = new Set<string>();
    const queue: Array<{
      entityId: string;
      path: string[];
      relationships: Relationship[];
    }> = [{ entityId: startId, path: [startId], relationships: [] }];

    visited.add(startId);

    while (queue.length > 0) {
      const current = queue.shift()!;

      if (current.entityId === endId) {
        // Found path
        const pathEntities = current.path.map(id => this.db.getEntity(id)!).filter(Boolean);
        return {
          entities: pathEntities,
          relationships: current.relationships,
          length: current.relationships.length,
        };
      }

      if (current.path.length > maxDepth) {
        continue;
      }

      // Get neighbors
      const relDirection = direction === 'forward' ? 'out' : direction === 'backward' ? 'in' : 'both';
      const rels = this.db.getRelationships(current.entityId, relDirection);

      for (const rel of rels) {
        // Filter by relationship type
        if (options.relationshipTypes && !options.relationshipTypes.includes(rel.type)) {
          continue;
        }

        const nextId = rel.sourceId === current.entityId ? rel.targetId : rel.sourceId;

        if (!visited.has(nextId)) {
          visited.add(nextId);
          queue.push({
            entityId: nextId,
            path: [...current.path, nextId],
            relationships: [...current.relationships, rel],
          });
        }
      }
    }

    return null; // No path found
  }

  /**
   * Extract subgraph around entity
   * @see REQ-YL-QUERY-003
   */
  extractSubgraph(
    rootId: string,
    options: {
      depth?: number;
      entityTypes?: EntityType[];
      relationshipTypes?: RelationType[];
      direction?: 'in' | 'out' | 'both';
    } = {}
  ): Subgraph {
    const depth = options.depth ?? 2;
    const direction = options.direction ?? 'both';
    const entityTypes = options.entityTypes ? new Set(options.entityTypes) : null;
    const relTypes = options.relationshipTypes ? new Set(options.relationshipTypes) : null;

    const entities = new Map<string, Entity>();
    const relationships = new Map<string, Relationship>();

    // BFS to collect subgraph
    const visited = new Set<string>();
    let currentLevel = [rootId];
    let currentDepth = 0;

    while (currentLevel.length > 0 && currentDepth <= depth) {
      const nextLevel: string[] = [];

      for (const entityId of currentLevel) {
        if (visited.has(entityId)) continue;
        visited.add(entityId);

        const entity = this.db.getEntity(entityId);
        if (!entity) continue;

        // Filter by entity type
        if (entityTypes && !entityTypes.has(entity.type)) {
          continue;
        }

        entities.set(entity.id, entity);

        // Get relationships
        const rels = this.db.getRelationships(entityId, direction);

        for (const rel of rels) {
          // Filter by relationship type
          if (relTypes && !relTypes.has(rel.type)) {
            continue;
          }

          relationships.set(rel.id, rel);

          // Add to next level
          const nextId = rel.sourceId === entityId ? rel.targetId : rel.sourceId;
          if (!visited.has(nextId)) {
            nextLevel.push(nextId);
          }
        }
      }

      currentLevel = nextLevel;
      currentDepth++;
    }

    return {
      entities: Array.from(entities.values()),
      relationships: Array.from(relationships.values()),
      rootId,
    };
  }

  /**
   * Pattern matching on graph
   * @see REQ-YL-QUERY-004
   */
  matchPattern(pattern: GraphPattern): PatternMatch[] {
    const matches: PatternMatch[] = [];

    // Get candidate entities for first pattern node
    const firstPattern = pattern.nodes[0];
    if (!firstPattern) return matches;

    const { entities: candidates } = this.db.queryEntities(
      {
        type: firstPattern.type,
        namePattern: firstPattern.namePattern,
      },
      1000 // Limit candidates
    );

    // Try to match pattern starting from each candidate
    for (const startEntity of candidates) {
      const bindings = new Map<string, string>();
      bindings.set(firstPattern.variable, startEntity.id);

      const result = this.tryMatchPattern(pattern, 1, bindings);
      if (result) {
        matches.push({
          bindings: Object.fromEntries(result),
          confidence: 1.0,
        });
      }
    }

    return matches;
  }

  /**
   * Recursive pattern matching helper
   */
  private tryMatchPattern(
    pattern: GraphPattern,
    nodeIndex: number,
    bindings: Map<string, string>
  ): Map<string, string> | null {
    if (nodeIndex >= pattern.nodes.length) {
      // All nodes matched, now check edges
      for (const edge of pattern.edges) {
        const sourceId = bindings.get(edge.sourceVar);
        const targetId = bindings.get(edge.targetVar);

        if (!sourceId || !targetId) return null;

        // Check if relationship exists
        const rels = this.db.getRelationships(sourceId, 'out');
        const hasEdge = rels.some(
          r => r.targetId === targetId && (edge.type === undefined || r.type === edge.type)
        );

        if (!hasEdge) return null;
      }

      return bindings;
    }

    const nodePattern = pattern.nodes[nodeIndex];

    // Find edges connecting to already bound nodes
    const connectingEdges = pattern.edges.filter(
      e => bindings.has(e.sourceVar) && e.targetVar === nodePattern.variable
    );

    if (connectingEdges.length > 0) {
      // Follow edges to find candidates
      const edge = connectingEdges[0];
      const sourceId = bindings.get(edge.sourceVar)!;
      const rels = this.db.getRelationships(sourceId, 'out').filter(
        r => edge.type === undefined || r.type === edge.type
      );

      for (const rel of rels) {
        const targetEntity = this.db.getEntity(rel.targetId);
        if (!targetEntity) continue;

        // Check if target matches pattern
        if (nodePattern.type && targetEntity.type !== nodePattern.type) continue;
        if (
          nodePattern.namePattern &&
          !this.matchNamePattern(targetEntity.name, nodePattern.namePattern)
        )
          continue;

        // Try binding this entity
        const newBindings = new Map(bindings);
        newBindings.set(nodePattern.variable, targetEntity.id);

        const result = this.tryMatchPattern(pattern, nodeIndex + 1, newBindings);
        if (result) return result;
      }
    } else {
      // No connecting edges, search all matching entities
      const { entities } = this.db.queryEntities(
        {
          type: nodePattern.type,
          namePattern: nodePattern.namePattern,
        },
        100
      );

      for (const entity of entities) {
        const newBindings = new Map(bindings);
        newBindings.set(nodePattern.variable, entity.id);

        const result = this.tryMatchPattern(pattern, nodeIndex + 1, newBindings);
        if (result) return result;
      }
    }

    return null;
  }

  /**
   * Check if name matches pattern
   */
  private matchNamePattern(name: string, pattern: string): boolean {
    const regex = new RegExp('^' + pattern.replace(/\*/g, '.*') + '$');
    return regex.test(name);
  }

  /**
   * Find entities by traversing relationships
   */
  traverse(
    startId: string,
    relationshipTypes: RelationType[],
    direction: 'forward' | 'backward',
    maxHops = 5
  ): Entity[] {
    const result: Entity[] = [];
    const visited = new Set<string>();
    let current = [startId];

    for (let hop = 0; hop < maxHops && current.length > 0; hop++) {
      const next: string[] = [];

      for (const entityId of current) {
        if (visited.has(entityId)) continue;
        visited.add(entityId);

        const rels = this.db.getRelationships(
          entityId,
          direction === 'forward' ? 'out' : 'in'
        );

        for (const rel of rels) {
          if (!relationshipTypes.includes(rel.type)) continue;

          const nextId = direction === 'forward' ? rel.targetId : rel.sourceId;
          if (!visited.has(nextId)) {
            const entity = this.db.getEntity(nextId);
            if (entity) {
              result.push(entity);
              next.push(nextId);
            }
          }
        }
      }

      current = next;
    }

    return result;
  }

  /**
   * Get entity neighbors
   */
  getNeighbors(
    entityId: string,
    options: {
      direction?: 'in' | 'out' | 'both';
      relationshipTypes?: RelationType[];
      entityTypes?: EntityType[];
    } = {}
  ): Array<{ entity: Entity; relationship: Relationship }> {
    const direction = options.direction ?? 'both';
    const rels = this.db.getRelationships(entityId, direction);

    const results: Array<{ entity: Entity; relationship: Relationship }> = [];

    for (const rel of rels) {
      // Filter by relationship type
      if (options.relationshipTypes && !options.relationshipTypes.includes(rel.type)) {
        continue;
      }

      const neighborId = rel.sourceId === entityId ? rel.targetId : rel.sourceId;
      const neighbor = this.db.getEntity(neighborId);

      if (!neighbor) continue;

      // Filter by entity type
      if (options.entityTypes && !options.entityTypes.includes(neighbor.type)) {
        continue;
      }

      results.push({ entity: neighbor, relationship: rel });
    }

    return results;
  }

  /**
   * Find all paths between two entities (up to limit)
   */
  findAllPaths(
    startId: string,
    endId: string,
    options: {
      maxDepth?: number;
      maxPaths?: number;
      relationshipTypes?: RelationType[];
    } = {}
  ): Path[] {
    const maxDepth = options.maxDepth ?? 5;
    const maxPaths = options.maxPaths ?? 10;
    const paths: Path[] = [];

    const dfs = (
      currentId: string,
      visited: Set<string>,
      path: string[],
      relationships: Relationship[]
    ): void => {
      if (paths.length >= maxPaths) return;
      if (path.length > maxDepth) return;

      if (currentId === endId) {
        const entities = path.map(id => this.db.getEntity(id)!).filter(Boolean);
        paths.push({
          entities,
          relationships: [...relationships],
          length: relationships.length,
        });
        return;
      }

      const rels = this.db.getRelationships(currentId, 'out');

      for (const rel of rels) {
        if (options.relationshipTypes && !options.relationshipTypes.includes(rel.type)) {
          continue;
        }

        const nextId = rel.targetId;
        if (visited.has(nextId)) continue;

        visited.add(nextId);
        path.push(nextId);
        relationships.push(rel);

        dfs(nextId, visited, path, relationships);

        visited.delete(nextId);
        path.pop();
        relationships.pop();
      }
    };

    const visited = new Set<string>([startId]);
    dfs(startId, visited, [startId], []);

    return paths;
  }
}
