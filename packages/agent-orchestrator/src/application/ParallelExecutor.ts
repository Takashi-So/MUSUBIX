/**
 * ParallelExecutor Application Service
 * 
 * Executes independent tasks in parallel
 * 
 * @see REQ-PAD-002 - Parallel Execution
 * @see DES-PAD-002 - ParallelExecutor
 */

import type { SubagentSpec, SubagentResult } from '../domain/entities/SubagentSpec.js';
import { createSubagentResult } from '../domain/entities/SubagentSpec.js';
import type { DependencyGraph } from '../domain/services/DependencyAnalyzer.js';

/**
 * Executor function type
 */
export type SubagentExecutor = (spec: SubagentSpec) => Promise<SubagentResult>;

/**
 * Parallel executor interface
 */
export interface IParallelExecutor {
  /**
   * Execute specs in parallel respecting dependencies
   * @param specs - Subagent specifications
   * @param graph - Dependency graph
   * @param executor - Executor function
   * @returns All results
   */
  execute(
    specs: SubagentSpec[],
    graph: DependencyGraph,
    executor: SubagentExecutor
  ): Promise<SubagentResult[]>;

  /**
   * Execute specs in a single level (all parallel)
   * @param specs - Subagent specifications
   * @param executor - Executor function
   * @returns Results
   */
  executeLevel(
    specs: SubagentSpec[],
    executor: SubagentExecutor
  ): Promise<SubagentResult[]>;
}

/**
 * Executor configuration
 */
export interface ParallelExecutorConfig {
  /** Maximum concurrent executions (default: 5) */
  maxConcurrency?: number;
  /** Continue on error (default: true) */
  continueOnError?: boolean;
  /** Global timeout (ms) */
  globalTimeoutMs?: number;
}

/**
 * Create a parallel executor
 * 
 * @param config - Optional configuration
 * @returns IParallelExecutor implementation
 */
export function createParallelExecutor(
  config: ParallelExecutorConfig = {}
): IParallelExecutor {
  const maxConcurrency = config.maxConcurrency ?? 5;
  const continueOnError = config.continueOnError ?? true;
  const globalTimeoutMs = config.globalTimeoutMs ?? 600000; // 10 minutes

  /**
   * Execute with concurrency limit
   */
  async function executeWithLimit<T>(
    items: T[],
    fn: (item: T) => Promise<SubagentResult>,
    limit: number
  ): Promise<SubagentResult[]> {
    const results: SubagentResult[] = [];
    const executing: Promise<void>[] = [];

    for (const item of items) {
      const promise = fn(item).then((result) => {
        results.push(result);
      });

      executing.push(promise);

      if (executing.length >= limit) {
        await Promise.race(executing);
        // Remove completed promises
        const completed = executing.filter(
          (p) => (p as Promise<void> & { settled?: boolean }).settled
        );
        for (const c of completed) {
          const index = executing.indexOf(c);
          if (index > -1) executing.splice(index, 1);
        }
      }
    }

    await Promise.all(executing);
    return results;
  }

  /**
   * Execute single spec with timeout
   */
  async function executeWithTimeout(
    spec: SubagentSpec,
    executor: SubagentExecutor
  ): Promise<SubagentResult> {
    const startTime = Date.now();

    const timeoutPromise = new Promise<SubagentResult>((_, reject) => {
      setTimeout(() => {
        reject(new Error(`Timeout after ${spec.timeoutMs}ms`));
      }, spec.timeoutMs);
    });

    try {
      const result = await Promise.race([executor(spec), timeoutPromise]);
      return result;
    } catch (error) {
      const durationMs = Date.now() - startTime;
      return createSubagentResult(
        spec.id,
        false,
        '',
        durationMs,
        [],
        error instanceof Error ? error.message : String(error)
      );
    }
  }

  return {
    async execute(
      specs: SubagentSpec[],
      graph: DependencyGraph,
      executor: SubagentExecutor
    ): Promise<SubagentResult[]> {
      if (graph.hasCircular) {
        throw new Error(
          `Cannot execute: circular dependency detected: ${graph.circularPath?.join(' → ')}`
        );
      }

      const allResults: SubagentResult[] = [];
      const specMap = new Map(specs.map((s) => [s.id, s]));
      const completedIds = new Set<string>();

      // Global timeout
      const globalStart = Date.now();

      // Execute level by level
      for (const level of graph.levels) {
        // Check global timeout
        if (Date.now() - globalStart > globalTimeoutMs) {
          // Create timeout results for remaining specs
          for (const id of level) {
            if (!completedIds.has(id)) {
              allResults.push(
                createSubagentResult(
                  id,
                  false,
                  '',
                  0,
                  [],
                  `Global timeout exceeded (${globalTimeoutMs}ms)`
                )
              );
            }
          }
          break;
        }

        // Get specs for this level
        const levelSpecs = level
          .map((id) => specMap.get(id))
          .filter((s): s is SubagentSpec => s !== undefined);

        // Execute level in parallel
        const levelResults = await this.executeLevel(levelSpecs, executor);

        // Track results
        for (const result of levelResults) {
          allResults.push(result);
          completedIds.add(result.specId);

          // Check if we should stop on error
          if (!result.success && !continueOnError) {
            return allResults;
          }
        }
      }

      return allResults;
    },

    async executeLevel(
      specs: SubagentSpec[],
      executor: SubagentExecutor
    ): Promise<SubagentResult[]> {
      if (specs.length === 0) {
        return [];
      }

      // Execute all specs in parallel with concurrency limit
      const results = await executeWithLimit(
        specs,
        (spec) => executeWithTimeout(spec, executor),
        maxConcurrency
      );

      return results;
    },
  };
}

/**
 * Execution progress callback
 */
export type ProgressCallback = (
  completed: number,
  total: number,
  current: SubagentResult
) => void;

/**
 * Create executor with progress tracking
 * 
 * @param config - Configuration
 * @param onProgress - Progress callback
 * @returns Executor with progress
 */
export function createProgressExecutor(
  config: ParallelExecutorConfig = {},
  onProgress?: ProgressCallback
): IParallelExecutor {
  const baseExecutor = createParallelExecutor(config);
  let completed = 0;

  return {
    async execute(specs, graph, executor) {
      completed = 0;
      const total = specs.length;

      const wrappedExecutor: SubagentExecutor = async (spec) => {
        const result = await executor(spec);
        completed++;
        onProgress?.(completed, total, result);
        return result;
      };

      return baseExecutor.execute(specs, graph, wrappedExecutor);
    },

    async executeLevel(specs, executor) {
      const total = specs.length;
      let levelCompleted = 0;

      const wrappedExecutor: SubagentExecutor = async (spec) => {
        const result = await executor(spec);
        levelCompleted++;
        onProgress?.(levelCompleted, total, result);
        return result;
      };

      return baseExecutor.executeLevel(specs, wrappedExecutor);
    },
  };
}
