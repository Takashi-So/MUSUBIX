/**
 * @nahisaho/musubix-codegraph - GraphRAG Search
 *
 * Graph-based retrieval augmented generation search
 *
 * @see REQ-CG-RAG-001 - Community detection
 * @see REQ-CG-RAG-002 - Global search
 * @see REQ-CG-RAG-003 - Local search
 * @see DES-CG-005
 * @see TSK-CG-040
 */

import type {
  Entity,
  SearchResult,
  Community,
  GraphRAGOptions,
  GlobalSearchOptions,
  LocalSearchOptions,
} from '../types.js';
import type { GraphEngine } from '../graph/index.js';

/**
 * GraphRAG Search Engine
 *
 * Implements Microsoft's GraphRAG approach for code understanding:
 * - Community detection via Leiden algorithm
 * - Hierarchical summaries for global queries
 * - Local context retrieval for specific queries
 */
export class GraphRAGSearch {
  private graph: GraphEngine;
  private _options: Required<GraphRAGOptions>;
  private communities: Community[] = [];
  private entityCommunityMap = new Map<string, string>();

  constructor(graph: GraphEngine, options: Partial<GraphRAGOptions> = {}) {
    this.graph = graph;
    this._options = {
      communityAlgorithm: options.communityAlgorithm ?? 'louvain',
      minCommunitySize: options.minCommunitySize ?? 3,
    };
  }

  /**
   * Get current options
   */
  getOptions(): Required<GraphRAGOptions> {
    return this._options;
  }

  // =========================================================================
  // Community Detection
  // =========================================================================

  /**
   * Detect communities in the code graph
   *
   * Uses a simplified Leiden-inspired algorithm for code communities
   */
  async detectCommunities(): Promise<Community[]> {
    const result = await this.graph.query({});
    const entities = result.entities;
    const relations = result.relations;

    // Build adjacency map
    const adjacency = new Map<string, Set<string>>();
    for (const entity of entities) {
      adjacency.set(entity.id, new Set());
    }
    for (const relation of relations) {
      adjacency.get(relation.sourceId)?.add(relation.targetId);
      adjacency.get(relation.targetId)?.add(relation.sourceId);
    }

    // Simple community detection: group by file/module
    const fileGroups = new Map<string, Entity[]>();
    for (const entity of entities) {
      if (entity.type === 'file') continue;
      const filePath = entity.filePath ?? 'unknown';
      if (!fileGroups.has(filePath)) {
        fileGroups.set(filePath, []);
      }
      fileGroups.get(filePath)!.push(entity);
    }

    // Create communities from file groups
    this.communities = [];
    let communityId = 0;

    for (const [filePath, members] of fileGroups) {
      if (members.length === 0) continue;

      const community: Community = {
        id: `community-${communityId++}`,
        name: filePath.split('/').pop() ?? filePath,
        memberCount: members.length,
        keyEntities: members.slice(0, 5).map(e => e.id),
      };

      this.communities.push(community);

      // Map entities to communities
      for (const member of members) {
        this.entityCommunityMap.set(member.id, community.id);
      }
    }

    // Create hierarchical communities (level 2: by directory)
    const dirGroups = new Map<string, Community[]>();
    for (const community of this.communities) {
      const parts = community.name.split('/');
      const dir = parts.slice(0, -1).join('/') || 'root';
      if (!dirGroups.has(dir)) {
        dirGroups.set(dir, []);
      }
      dirGroups.get(dir)!.push(community);
    }

    // Create parent communities
    for (const [dir, children] of dirGroups) {
      if (children.length <= 1) continue;

      const parentCommunity: Community = {
        id: `community-${communityId++}`,
        name: dir,
        memberCount: children.reduce((sum, c) => sum + c.memberCount, 0),
        keyEntities: children.flatMap(c => c.keyEntities).slice(0, 10),
      };

      this.communities.push(parentCommunity);

      // Update children to reference parent
      for (const child of children) {
        child.parentId = parentCommunity.id;
      }
    }

    return this.communities;
  }

  /**
   * Generate community summary
   */
  async generateCommunitySummary(communityId: string): Promise<string> {
    const community = this.communities.find(c => c.id === communityId);
    if (!community) {
      return 'Community not found';
    }

    // Get entities in this community
    const entityIds = Array.from(this.entityCommunityMap.entries())
      .filter(([_, cid]) => cid === communityId)
      .map(([eid, _]) => eid);

    // Build summary from entity names and types
    const entityDetails: string[] = [];
    for (const entityId of entityIds.slice(0, 20)) {
      const entity = await this.graph.getEntity(entityId);
      if (entity) {
        entityDetails.push(`${entity.type}: ${entity.name}`);
      }
    }

    const summary = `Community "${community.name}" contains ${community.memberCount} entities:\n${entityDetails.join('\n')}`;

    // Cache summary
    community.summary = summary;

    return summary;
  }

  // =========================================================================
  // Search Operations
  // =========================================================================

  /**
   * Global search across all communities
   *
   * Searches community summaries for high-level understanding
   */
  async globalSearch(
    query: string,
    options?: GlobalSearchOptions
  ): Promise<SearchResult[]> {
    const limit = options?.limit ?? 10;
    const minScore = options?.minScore ?? 0.1;
    const results: SearchResult[] = [];

    // Ensure communities are detected
    if (this.communities.length === 0) {
      await this.detectCommunities();
    }

    // Search in community summaries
    const queryLower = query.toLowerCase();
    const queryTerms = queryLower.split(/\s+/);

    for (const community of this.communities) {
      // Generate summary if not cached
      if (!community.summary && options?.includeSummaries) {
        await this.generateCommunitySummary(community.id);
      }

      // Calculate relevance score
      let score = 0;
      const searchText = `${community.name} ${community.summary ?? ''}`.toLowerCase();

      for (const term of queryTerms) {
        if (searchText.includes(term)) {
          score += 0.3;
        }
      }

      // Boost score based on community size
      score += Math.min(community.memberCount / 100, 0.2);

      if (score >= minScore) {
        // Get representative entity from community
        const entityId = community.keyEntities[0];
        if (entityId) {
          const entity = await this.graph.getEntity(entityId);
          if (entity) {
            results.push({
              entity,
              score: Math.min(score, 1),
              context: community.summary ?? community.name,
              community,
            });
          }
        }
      }
    }

    // Sort by score and limit
    results.sort((a, b) => b.score - a.score);
    return results.slice(0, limit);
  }

  /**
   * Local search in entity neighborhood
   *
   * Searches within a specific entity's local context
   */
  async localSearch(
    entityName: string,
    options?: LocalSearchOptions
  ): Promise<SearchResult[]> {
    const radius = options?.radius ?? 2;
    const limit = options?.limit ?? 10;
    const results: SearchResult[] = [];

    // Find the starting entity
    const startEntity = await this.graph.findByName(entityName);
    if (!startEntity) {
      return [];
    }

    // Get neighbors within radius
    const visited = new Set<string>();
    const neighbors: Entity[] = [];

    await this.collectNeighbors(startEntity.id, radius, visited, neighbors);

    // Score neighbors based on proximity and relation type
    const entityDepthMap = new Map<string, number>();
    entityDepthMap.set(startEntity.id, 0);

    // BFS to determine depths
    const queue: [string, number][] = [[startEntity.id, 0]];
    const bfsVisited = new Set<string>();

    while (queue.length > 0) {
      const [entityId, depth] = queue.shift()!;
      if (bfsVisited.has(entityId) || depth > radius) continue;
      bfsVisited.add(entityId);

      const entity = neighbors.find(e => e.id === entityId);
      if (entity) {
        entityDepthMap.set(entityId, depth);
      }

      // Get connected entities
      const deps = await this.graph.findDependencies(entityId, 1);
      for (const dep of deps) {
        if (!bfsVisited.has(dep.id)) {
          queue.push([dep.id, depth + 1]);
        }
      }
    }

    // Build results
    for (const entity of neighbors) {
      if (entity.id === startEntity.id) continue;

      const depth = entityDepthMap.get(entity.id) ?? radius;
      const score = 1 - (depth / (radius + 1));

      // Get community context if requested
      let community: Community | undefined;
      if (options?.includeCommunity) {
        const communityId = this.entityCommunityMap.get(entity.id);
        if (communityId) {
          community = this.communities.find(c => c.id === communityId);
        }
      }

      results.push({
        entity,
        score,
        context: `${entity.type}: ${entity.name}`,
        community,
      });
    }

    // Sort by score and limit
    results.sort((a, b) => b.score - a.score);
    return results.slice(0, limit);
  }

  /**
   * Collect neighbors within radius
   */
  private async collectNeighbors(
    entityId: string,
    radius: number,
    visited: Set<string>,
    neighbors: Entity[]
  ): Promise<void> {
    if (radius < 0 || visited.has(entityId)) return;
    visited.add(entityId);

    const entity = await this.graph.getEntity(entityId);
    if (entity) {
      neighbors.push(entity);
    }

    // Get connected entities
    const deps = await this.graph.findDependencies(entityId, 1);
    for (const dep of deps) {
      await this.collectNeighbors(dep.id, radius - 1, visited, neighbors);
    }
  }

  // =========================================================================
  // Getters
  // =========================================================================

  /**
   * Get all communities
   */
  getCommunities(): Community[] {
    return [...this.communities];
  }

  /**
   * Get community for entity
   */
  getCommunityForEntity(entityId: string): Community | undefined {
    const communityId = this.entityCommunityMap.get(entityId);
    if (!communityId) return undefined;
    return this.communities.find(c => c.id === communityId);
  }
}
