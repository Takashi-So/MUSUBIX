/**
 * @nahisaho/yata-scale - Query Coordinator
 * 
 * Coordinates query execution across shards
 */

import { ok, err, type Result } from 'neverthrow';
import type { GraphQuery, QueryResult, QueryPlan, QueryStep, Entity, Relationship } from './types.js';
import { QueryError, QueryTimeoutError } from './errors.js';

/**
 * Query planner
 */
export class QueryPlanner {
  plan(query: GraphQuery, shards: string[]): QueryPlan {
    const steps: QueryStep[] = [];
    let estimatedCost = 0;

    if (query.type === 'lookup' && query.entityIds) {
      steps.push({
        type: 'index',
        target: 'entity',
        cost: query.entityIds.length * 10,
        details: { ids: query.entityIds },
      });
      estimatedCost += query.entityIds.length * 10;
    }

    if (query.type === 'traverse' && query.startEntityIds) {
      steps.push({
        type: 'scan',
        target: 'graph',
        cost: query.startEntityIds.length * (query.maxDepth ?? 1) * 50,
        details: { startIds: query.startEntityIds, depth: query.maxDepth },
      });
      estimatedCost += query.startEntityIds.length * (query.maxDepth ?? 1) * 50;
    }

    if (query.type === 'pattern' && query.pattern) {
      steps.push({
        type: 'scan',
        target: 'pattern',
        cost: 500,
        details: { pattern: query.pattern },
      });
      estimatedCost += 500;
    }

    if (query.filters && query.filters.length > 0) {
      steps.push({
        type: 'filter',
        target: 'result',
        cost: query.filters.length * 20,
        details: { filters: query.filters },
      });
      estimatedCost += query.filters.length * 20;
    }

    if (query.orderBy && query.orderBy.length > 0) {
      steps.push({
        type: 'sort',
        target: 'result',
        cost: 100,
        details: { orderBy: query.orderBy },
      });
      estimatedCost += 100;
    }

    if (query.limit !== undefined) {
      steps.push({
        type: 'limit',
        target: 'result',
        cost: 10,
        details: { limit: query.limit, offset: query.offset },
      });
      estimatedCost += 10;
    }

    return {
      query,
      steps,
      estimatedCost,
      targetShards: shards,
      parallelizable: shards.length > 1,
      cacheKey: this.generateCacheKey(query),
      timeout: query.timeout,
    };
  }

  optimize(plan: QueryPlan): QueryPlan {
    const optimizations: string[] = [];

    // Push filters before sorts
    const filterIdx = plan.steps.findIndex((s) => s.type === 'filter');
    const sortIdx = plan.steps.findIndex((s) => s.type === 'sort');
    if (sortIdx !== -1 && filterIdx > sortIdx) {
      optimizations.push('filter-pushdown');
    }

    return { ...plan, optimizations };
  }

  private generateCacheKey(query: GraphQuery): string {
    return `query:${JSON.stringify(query)}`.substring(0, 100);
  }
}

/**
 * Worker pool for parallel execution
 */
export class WorkerPool {
  private concurrency: number;
  private active = 0;
  private pending: Array<() => Promise<void>> = [];

  constructor(concurrency: number) {
    this.concurrency = concurrency;
  }

  async map<T, R>(items: T[], fn: (item: T) => R | Promise<R>): Promise<R[]> {
    const results: R[] = [];

    for (const item of items) {
      while (this.active >= this.concurrency) {
        await new Promise((r) => setTimeout(r, 1));
      }

      this.active++;
      try {
        results.push(await fn(item));
      } finally {
        this.active--;
      }
    }

    return results;
  }

  async filter<T>(items: T[], predicate: (item: T) => boolean | Promise<boolean>): Promise<T[]> {
    const results: T[] = [];

    for (const item of items) {
      if (await predicate(item)) {
        results.push(item);
      }
    }

    return results;
  }

  async reduce<T, R>(items: T[], fn: (acc: R, item: T) => R | Promise<R>, initial: R): Promise<R> {
    let result = initial;
    for (const item of items) {
      result = await fn(result, item);
    }
    return result;
  }

  get activeCount(): number {
    return this.active;
  }

  get pendingCount(): number {
    return this.pending.length;
  }

  async shutdown(): Promise<void> {
    while (this.active > 0) {
      await new Promise((r) => setTimeout(r, 10));
    }
  }
}

/**
 * Distributed query executor
 */
export class DistributedExecutor {
  private pool: WorkerPool;
  private timeout: number;
  private stats = { totalQueries: 0, totalTime: 0 };

  constructor(concurrency: number, timeout: number) {
    this.pool = new WorkerPool(concurrency);
    this.timeout = timeout;
  }

  async execute(
    query: GraphQuery,
    shards: string[],
    executor: (shardId: string, query: GraphQuery) => Promise<{ entities: Entity[]; relationships: Relationship[] }>
  ): Promise<Result<QueryResult, QueryError>> {
    const startTime = Date.now();

    try {
      const results = await Promise.race([
        this.executeOnShards(query, shards, executor),
        this.timeoutPromise(query.timeout ?? this.timeout),
      ]);

      if (results === 'timeout') {
        return err(new QueryTimeoutError(query.timeout ?? this.timeout));
      }

      const merged = this.mergeResults(results as Array<{ entities: Entity[]; relationships: Relationship[] }>);
      
      this.stats.totalQueries++;
      this.stats.totalTime += Date.now() - startTime;

      return ok({
        entities: merged.entities,
        relationships: merged.relationships,
        totalCount: merged.entities.length + merged.relationships.length,
        hasMore: false,
        executionTimeMs: Date.now() - startTime,
        shardsQueried: shards,
      });
    } catch (error) {
      return err(new QueryError(error instanceof Error ? error.message : String(error)));
    }
  }

  private async executeOnShards(
    query: GraphQuery,
    shards: string[],
    executor: (shardId: string, query: GraphQuery) => Promise<{ entities: Entity[]; relationships: Relationship[] }>
  ): Promise<Array<{ entities: Entity[]; relationships: Relationship[] }>> {
    const results: Array<{ entities: Entity[]; relationships: Relationship[] }> = [];

    for (const shard of shards) {
      try {
        const result = await executor(shard, query);
        results.push(result);
      } catch {
        // Continue with other shards
      }
    }

    return results;
  }

  private timeoutPromise(ms: number): Promise<'timeout'> {
    return new Promise((resolve) => setTimeout(() => resolve('timeout'), ms));
  }

  private mergeResults(
    results: Array<{ entities: Entity[]; relationships: Relationship[] }>
  ): { entities: Entity[]; relationships: Relationship[] } {
    const entityMap = new Map<string, Entity>();
    const relMap = new Map<string, Relationship>();

    for (const result of results) {
      for (const entity of result.entities) {
        entityMap.set(entity.id, entity);
      }
      for (const rel of result.relationships) {
        relMap.set(rel.id, rel);
      }
    }

    return {
      entities: Array.from(entityMap.values()),
      relationships: Array.from(relMap.values()),
    };
  }

  getStats(): { totalQueries: number; averageLatency: number } {
    return {
      totalQueries: this.stats.totalQueries,
      averageLatency: this.stats.totalQueries > 0 ? this.stats.totalTime / this.stats.totalQueries : 0,
    };
  }

  async shutdown(): Promise<void> {
    await this.pool.shutdown();
  }
}

/**
 * Query coordinator
 */
export class QueryCoordinator {
  private planner: QueryPlanner;
  private executor: DistributedExecutor;
  private cache: Map<string, { result: QueryResult; expiry: number }> = new Map();
  private cacheTtl: number;
  private stats = { cacheHits: 0, cacheMisses: 0 };

  constructor(concurrency: number, cacheTtl: number, timeout: number) {
    this.planner = new QueryPlanner();
    this.executor = new DistributedExecutor(concurrency, timeout);
    this.cacheTtl = cacheTtl;
  }

  async query(
    query: GraphQuery,
    shards: string[],
    executor: (shardId: string, query: GraphQuery) => Promise<{ entities: Entity[]; relationships: Relationship[] }>
  ): Promise<Result<QueryResult, QueryError>> {
    const plan = this.planner.plan(query, shards);

    // Check cache
    if (plan.cacheKey && query.options?.useCache !== false) {
      const cached = this.cache.get(plan.cacheKey);
      if (cached && cached.expiry > Date.now()) {
        this.stats.cacheHits++;
        return ok(cached.result);
      }
    }

    this.stats.cacheMisses++;

    const result = await this.executor.execute(query, shards, executor);

    // Cache result
    if (result.isOk() && plan.cacheKey) {
      this.cache.set(plan.cacheKey, {
        result: result.value,
        expiry: Date.now() + (query.options?.cacheTtl ?? this.cacheTtl),
      });
    }

    return result;
  }

  validate(query: GraphQuery): Result<void, QueryError> {
    if (!['lookup', 'traverse', 'pattern', 'aggregate'].includes(query.type)) {
      return err(new QueryError(`Invalid query type: ${query.type}`));
    }

    if (query.type === 'lookup' && (!query.entityIds || query.entityIds.length === 0)) {
      return err(new QueryError('lookup query requires entityIds'));
    }

    if (query.type === 'traverse' && (!query.startEntityIds || query.startEntityIds.length === 0)) {
      return err(new QueryError('traverse query requires startEntityIds'));
    }

    return ok(undefined);
  }

  explain(query: GraphQuery, shards: string[]): string {
    const plan = this.planner.plan(query, shards);
    const lines = [
      `Query Type: ${query.type}`,
      `Estimated Cost: ${plan.estimatedCost}`,
      `Target Shards: ${plan.targetShards.join(', ')}`,
      `Parallelizable: ${plan.parallelizable}`,
      '',
      'Execution Steps:',
    ];

    for (const step of plan.steps) {
      lines.push(`  - ${step.type} on ${step.target} (cost: ${step.cost})`);
    }

    return lines.join('\n');
  }

  getStats(): { cacheHits: number; cacheMisses: number } {
    return { ...this.stats };
  }

  clearCache(): void {
    this.cache.clear();
  }

  async shutdown(): Promise<void> {
    await this.executor.shutdown();
  }
}
