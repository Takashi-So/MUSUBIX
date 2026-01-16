/**
 * @fileoverview ParallelExecutor - Parallel search execution with concurrency control
 * @module @nahisaho/musubix-deep-research/performance
 * @version 1.0.0
 * 
 * REQ: REQ-DR-NFR-004 (Performance Requirements)
 * TSK: TSK-DR-016 (ParallelExecutor Implementation)
 * ADR: ADR-v3.4.0-001 (Security and Performance Practices)
 */

/**
 * Task to be executed in parallel
 */
export interface ParallelTask<T> {
  /** Unique task identifier */
  id: string;
  /** Task execution function */
  execute: () => Promise<T>;
  /** Task priority (higher = more important) */
  priority?: number;
  /** Maximum retry attempts */
  maxRetries?: number;
}

/**
 * Progress callback for parallel execution
 */
export interface ProgressCallback<T> {
  /** Called when a task starts */
  onStart?: (taskId: string) => void;
  /** Called when a task completes successfully */
  onComplete?: (taskId: string, result: T) => void;
  /** Called when a task fails */
  onError?: (taskId: string, error: Error) => void;
  /** Called when a task is retried */
  onRetry?: (taskId: string, attempt: number) => void;
}

/**
 * Options for parallel execution
 */
export interface ParallelExecutorOptions {
  /** Maximum number of concurrent tasks (default: 3) */
  maxConcurrency?: number;
  /** Default retry attempts for tasks (default: 2) */
  defaultRetries?: number;
  /** Delay between retries in ms (default: 1000) */
  retryDelay?: number;
  /** Timeout for individual tasks in ms (default: 30000) */
  taskTimeout?: number;
}

/**
 * Result of parallel execution
 */
export interface ParallelResult<T> {
  /** Successfully completed tasks */
  successful: Array<{ taskId: string; result: T }>;
  /** Failed tasks */
  failed: Array<{ taskId: string; error: Error }>;
  /** Total execution time in ms */
  totalTime: number;
}

/**
 * ParallelExecutor - Manages parallel task execution with concurrency control
 * 
 * Design Pattern: Queue-based concurrency control with Promise.race
 * 
 * @example
 * ```typescript
 * const executor = new ParallelExecutor({ maxConcurrency: 3 });
 * 
 * const tasks: ParallelTask<string>[] = [
 *   { id: 'task1', execute: async () => await searchAPI('query1') },
 *   { id: 'task2', execute: async () => await searchAPI('query2') },
 *   { id: 'task3', execute: async () => await searchAPI('query3') },
 * ];
 * 
 * const result = await executor.execute(tasks, {
 *   onComplete: (id, result) => console.log(`${id} completed:`, result),
 *   onError: (id, error) => console.error(`${id} failed:`, error),
 * });
 * ```
 */
export class ParallelExecutor<T = unknown> {
  private readonly maxConcurrency: number;
  private readonly defaultRetries: number;
  private readonly retryDelay: number;
  private readonly taskTimeout: number;
  private activeCount = 0;

  constructor(options: ParallelExecutorOptions = {}) {
    this.maxConcurrency = options.maxConcurrency ?? 3;
    this.defaultRetries = options.defaultRetries ?? 2;
    this.retryDelay = options.retryDelay ?? 1000;
    this.taskTimeout = options.taskTimeout ?? 30000;

    if (this.maxConcurrency < 1) {
      throw new Error('maxConcurrency must be at least 1');
    }
  }

  /**
   * Execute tasks in parallel with concurrency control
   */
  async execute(
    tasks: ParallelTask<T>[],
    callbacks?: ProgressCallback<T>
  ): Promise<ParallelResult<T>> {
    const startTime = Date.now();
    const successful: Array<{ taskId: string; result: T }> = [];
    const failed: Array<{ taskId: string; error: Error }> = [];

    // Sort by priority (higher priority first)
    const sortedTasks = [...tasks].sort((a, b) => (b.priority ?? 0) - (a.priority ?? 0));

    // Queue for pending tasks
    const queue = [...sortedTasks];
    const running = new Map<string, Promise<void>>();

    while (queue.length > 0 || running.size > 0) {
      // Start new tasks up to maxConcurrency
      while (queue.length > 0 && running.size < this.maxConcurrency) {
        const task = queue.shift()!;
        const promise = this.executeTask(task, callbacks, successful, failed);
        running.set(task.id, promise);
      }

      // Wait for at least one task to complete
      if (running.size > 0) {
        await Promise.race(running.values());
        // Remove completed tasks
        for (const [id, promise] of running.entries()) {
          const isSettled = await this.isPromiseSettled(promise);
          if (isSettled) {
            running.delete(id);
          }
        }
      }
    }

    const totalTime = Date.now() - startTime;
    return { successful, failed, totalTime };
  }

  /**
   * Execute a single task with retry logic
   */
  private async executeTask(
    task: ParallelTask<T>,
    callbacks: ProgressCallback<T> | undefined,
    successful: Array<{ taskId: string; result: T }>,
    failed: Array<{ taskId: string; error: Error }>
  ): Promise<void> {
    const maxRetries = task.maxRetries ?? this.defaultRetries;
    let attempt = 0;

    callbacks?.onStart?.(task.id);

    while (attempt <= maxRetries) {
      try {
        this.activeCount++;
        const result = await this.executeWithTimeout(task.execute, this.taskTimeout);
        this.activeCount--;

        successful.push({ taskId: task.id, result });
        callbacks?.onComplete?.(task.id, result);
        return;
      } catch (error) {
        this.activeCount--;
        attempt++;

        if (attempt <= maxRetries) {
          callbacks?.onRetry?.(task.id, attempt);
          await this.delay(this.retryDelay);
        } else {
          const err = error instanceof Error ? error : new Error(String(error));
          failed.push({ taskId: task.id, error: err });
          callbacks?.onError?.(task.id, err);
        }
      }
    }
  }

  /**
   * Execute a function with timeout
   */
  private async executeWithTimeout<R>(
    fn: () => Promise<R>,
    timeoutMs: number
  ): Promise<R> {
    return Promise.race([
      fn(),
      new Promise<R>((_, reject) =>
        setTimeout(() => reject(new Error('Task timeout')), timeoutMs)
      ),
    ]);
  }

  /**
   * Check if a promise is settled (resolved or rejected)
   */
  private async isPromiseSettled(promise: Promise<void>): Promise<boolean> {
    try {
      await Promise.race([
        promise,
        new Promise<void>((resolve) => setTimeout(resolve, 0)),
      ]);
      return true;
    } catch {
      return true;
    }
  }

  /**
   * Delay execution for specified milliseconds
   */
  private delay(ms: number): Promise<void> {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }

  /**
   * Get current number of active tasks
   */
  getActiveCount(): number {
    return this.activeCount;
  }

  /**
   * Get maximum concurrency setting
   */
  getMaxConcurrency(): number {
    return this.maxConcurrency;
  }
}

/**
 * Create a ParallelExecutor instance
 */
export function createParallelExecutor<T = unknown>(
  options?: ParallelExecutorOptions
): ParallelExecutor<T> {
  return new ParallelExecutor<T>(options);
}
