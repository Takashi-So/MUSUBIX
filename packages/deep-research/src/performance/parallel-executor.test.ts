/**
 * @fileoverview Tests for ParallelExecutor
 * @module @nahisaho/musubix-deep-research/performance
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ParallelExecutor,
  createParallelExecutor,
  type ParallelTask,
  type ProgressCallback,
} from './parallel-executor.js';

describe('ParallelExecutor', () => {
  describe('constructor', () => {
    it('should create executor with default options', () => {
      const executor = new ParallelExecutor();
      expect(executor.getMaxConcurrency()).toBe(3);
    });

    it('should create executor with custom maxConcurrency', () => {
      const executor = new ParallelExecutor({ maxConcurrency: 5 });
      expect(executor.getMaxConcurrency()).toBe(5);
    });

    it('should throw error if maxConcurrency < 1', () => {
      expect(() => new ParallelExecutor({ maxConcurrency: 0 })).toThrow(
        'maxConcurrency must be at least 1'
      );
    });
  });

  describe('execute', () => {
    it('should execute tasks sequentially when maxConcurrency = 1', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 1 });
      const executionOrder: number[] = [];

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => {
            await delay(50);
            executionOrder.push(1);
            return 1;
          },
        },
        {
          id: 'task2',
          execute: async () => {
            await delay(30);
            executionOrder.push(2);
            return 2;
          },
        },
        {
          id: 'task3',
          execute: async () => {
            await delay(20);
            executionOrder.push(3);
            return 3;
          },
        },
      ];

      const result = await executor.execute(tasks);

      expect(result.successful.length).toBe(3);
      expect(result.failed.length).toBe(0);
      expect(executionOrder).toEqual([1, 2, 3]);
    });

    it('should execute tasks in parallel', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 3 });
      const startTimes: Record<string, number> = {};

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => {
            startTimes['task1'] = Date.now();
            await delay(50);
            return 1;
          },
        },
        {
          id: 'task2',
          execute: async () => {
            startTimes['task2'] = Date.now();
            await delay(50);
            return 2;
          },
        },
        {
          id: 'task3',
          execute: async () => {
            startTimes['task3'] = Date.now();
            await delay(50);
            return 3;
          },
        },
      ];

      const result = await executor.execute(tasks);

      expect(result.successful.length).toBe(3);
      expect(result.failed.length).toBe(0);

      // All tasks should start within 100ms of each other (parallel execution)
      const times = Object.values(startTimes);
      const maxDiff = Math.max(...times) - Math.min(...times);
      expect(maxDiff).toBeLessThan(100);
    });

    it('should respect maxConcurrency limit', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 2 });
      let concurrentCount = 0;
      let maxConcurrent = 0;

      const tasks: ParallelTask<number>[] = Array.from({ length: 5 }, (_, i) => ({
        id: `task${i + 1}`,
        execute: async () => {
          concurrentCount++;
          maxConcurrent = Math.max(maxConcurrent, concurrentCount);
          await delay(50);
          concurrentCount--;
          return i + 1;
        },
      }));

      const result = await executor.execute(tasks);

      expect(result.successful.length).toBe(5);
      expect(maxConcurrent).toBeLessThanOrEqual(2);
    }, 10000); // 10 second timeout

    it('should handle task failures', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 2, defaultRetries: 0 });

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => 1,
        },
        {
          id: 'task2',
          execute: async () => {
            throw new Error('Task 2 failed');
          },
        },
        {
          id: 'task3',
          execute: async () => 3,
        },
      ];

      const result = await executor.execute(tasks);

      expect(result.successful.length).toBe(2);
      expect(result.failed.length).toBe(1);
      expect(result.failed[0].taskId).toBe('task2');
      expect(result.failed[0].error.message).toBe('Task 2 failed');
    });

    it('should retry failed tasks', async () => {
      const executor = new ParallelExecutor({
        maxConcurrency: 1,
        defaultRetries: 2,
        retryDelay: 10,
      });

      let attemptCount = 0;

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => {
            attemptCount++;
            if (attemptCount < 3) {
              throw new Error('Temporary failure');
            }
            return 1;
          },
        },
      ];

      const result = await executor.execute(tasks);

      expect(result.successful.length).toBe(1);
      expect(result.failed.length).toBe(0);
      expect(attemptCount).toBe(3); // Initial attempt + 2 retries
    });

    it('should respect task-specific maxRetries', async () => {
      const executor = new ParallelExecutor({
        maxConcurrency: 1,
        defaultRetries: 2,
        retryDelay: 10,
      });

      let attemptCount = 0;

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          maxRetries: 1, // Override default
          execute: async () => {
            attemptCount++;
            throw new Error('Always fails');
          },
        },
      ];

      const result = await executor.execute(tasks);

      expect(result.successful.length).toBe(0);
      expect(result.failed.length).toBe(1);
      expect(attemptCount).toBe(2); // Initial attempt + 1 retry
    });

    it('should handle task timeout', async () => {
      const executor = new ParallelExecutor({
        maxConcurrency: 1,
        taskTimeout: 100,
        defaultRetries: 0,
      });

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => {
            await delay(200); // Exceeds timeout
            return 1;
          },
        },
      ];

      const result = await executor.execute(tasks);

      expect(result.successful.length).toBe(0);
      expect(result.failed.length).toBe(1);
      expect(result.failed[0].error.message).toBe('Task timeout');
    });

    it('should execute tasks by priority', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 1 });
      const executionOrder: string[] = [];

      const tasks: ParallelTask<number>[] = [
        {
          id: 'low',
          priority: 1,
          execute: async () => {
            executionOrder.push('low');
            return 1;
          },
        },
        {
          id: 'high',
          priority: 10,
          execute: async () => {
            executionOrder.push('high');
            return 2;
          },
        },
        {
          id: 'medium',
          priority: 5,
          execute: async () => {
            executionOrder.push('medium');
            return 3;
          },
        },
      ];

      await executor.execute(tasks);

      expect(executionOrder).toEqual(['high', 'medium', 'low']);
    });

    it('should report total execution time', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 2 });

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => {
            await delay(100);
            return 1;
          },
        },
      ];

      const result = await executor.execute(tasks);

      expect(result.totalTime).toBeGreaterThanOrEqual(100);
      expect(result.totalTime).toBeLessThan(200); // Should not be 2x delay
    });
  });

  describe('progress callbacks', () => {
    it('should call onStart callback', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 2 });
      const startedTasks: string[] = [];

      const callbacks: ProgressCallback<number> = {
        onStart: (taskId) => startedTasks.push(taskId),
      };

      const tasks: ParallelTask<number>[] = [
        { id: 'task1', execute: async () => 1 },
        { id: 'task2', execute: async () => 2 },
      ];

      await executor.execute(tasks, callbacks);

      expect(startedTasks).toContain('task1');
      expect(startedTasks).toContain('task2');
    });

    it('should call onComplete callback', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 2 });
      const completedTasks: Array<{ id: string; result: number }> = [];

      const callbacks: ProgressCallback<number> = {
        onComplete: (taskId, result) => completedTasks.push({ id: taskId, result }),
      };

      const tasks: ParallelTask<number>[] = [
        { id: 'task1', execute: async () => 10 },
        { id: 'task2', execute: async () => 20 },
      ];

      await executor.execute(tasks, callbacks);

      expect(completedTasks).toContainEqual({ id: 'task1', result: 10 });
      expect(completedTasks).toContainEqual({ id: 'task2', result: 20 });
    });

    it('should call onError callback', async () => {
      const executor = new ParallelExecutor({ maxConcurrency: 1, defaultRetries: 0 });
      const errors: Array<{ id: string; error: Error }> = [];

      const callbacks: ProgressCallback<number> = {
        onError: (taskId, error) => errors.push({ id: taskId, error }),
      };

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => {
            throw new Error('Failed');
          },
        },
      ];

      await executor.execute(tasks, callbacks);

      expect(errors.length).toBe(1);
      expect(errors[0].id).toBe('task1');
      expect(errors[0].error.message).toBe('Failed');
    });

    it('should call onRetry callback', async () => {
      const executor = new ParallelExecutor({
        maxConcurrency: 1,
        defaultRetries: 2,
        retryDelay: 10,
      });
      const retries: Array<{ id: string; attempt: number }> = [];

      let attemptCount = 0;

      const callbacks: ProgressCallback<number> = {
        onRetry: (taskId, attempt) => retries.push({ id: taskId, attempt }),
      };

      const tasks: ParallelTask<number>[] = [
        {
          id: 'task1',
          execute: async () => {
            attemptCount++;
            if (attemptCount < 3) {
              throw new Error('Retry me');
            }
            return 1;
          },
        },
      ];

      await executor.execute(tasks, callbacks);

      expect(retries.length).toBe(2);
      expect(retries[0]).toEqual({ id: 'task1', attempt: 1 });
      expect(retries[1]).toEqual({ id: 'task1', attempt: 2 });
    });
  });

  describe('createParallelExecutor', () => {
    it('should create ParallelExecutor instance', () => {
      const executor = createParallelExecutor({ maxConcurrency: 4 });
      expect(executor).toBeInstanceOf(ParallelExecutor);
      expect(executor.getMaxConcurrency()).toBe(4);
    });
  });

  describe('getActiveCount', () => {
    it('should return 0 when no tasks are running', async () => {
      const executor = new ParallelExecutor();
      expect(executor.getActiveCount()).toBe(0);

      const tasks: ParallelTask<number>[] = [
        { id: 'task1', execute: async () => 1 },
      ];

      await executor.execute(tasks);
      expect(executor.getActiveCount()).toBe(0);
    });
  });
});

/**
 * Helper function to delay execution
 */
function delay(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}
