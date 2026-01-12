/**
 * TaskScheduler - Debounced task scheduling and execution
 * 
 * Implements: TSK-WATCH-002, DES-WATCH-007, REQ-WATCH-007
 */

import { randomUUID } from 'node:crypto';
import { EventEmitter } from 'node:events';
import type { TaskRunner, Issue } from './types.js';

/**
 * Task type
 */
export type TaskType = 'lint' | 'test' | 'security' | 'ears';

/**
 * Scheduled task
 */
export interface ScheduledTask {
  /** Unique task ID */
  id: string;
  /** Task type */
  type: TaskType;
  /** Files to process */
  files: string[];
  /** When the task was scheduled */
  scheduledAt: Date;
  /** Current status */
  status: 'pending' | 'running' | 'completed' | 'failed' | 'cancelled';
}

/**
 * Task result
 */
export interface TaskResult {
  /** Task ID */
  taskId: string;
  /** Task type */
  type: TaskType;
  /** Whether task succeeded */
  success: boolean;
  /** Execution duration in ms */
  duration: number;
  /** Issues found */
  issues: Issue[];
  /** Error message if failed */
  error?: string;
  /** Timestamp */
  timestamp: Date;
}

/**
 * TaskScheduler class
 * Manages task scheduling with debounce and sequential execution
 */
export class TaskScheduler extends EventEmitter {
  private queue: Map<string, ScheduledTask> = new Map();
  private debounceTimers: Map<string, NodeJS.Timeout> = new Map();
  private runners: Map<TaskType, TaskRunner> = new Map();
  private debounceMs: number;
  private isProcessing = false;
  private currentTask: ScheduledTask | null = null;

  constructor(debounceMs = 300) {
    super();
    this.debounceMs = debounceMs;
  }

  /**
   * Register a task runner
   */
  registerRunner(type: TaskType, runner: TaskRunner): void {
    this.runners.set(type, runner);
  }

  /**
   * Unregister a task runner
   */
  unregisterRunner(type: TaskType): void {
    this.runners.delete(type);
  }

  /**
   * Get registered runners
   */
  getRunners(): Map<TaskType, TaskRunner> {
    return new Map(this.runners);
  }

  /**
   * Schedule a task (debounced)
   */
  schedule(type: TaskType, files: string[]): string {
    // Create unique key for this task type + files combination
    const key = `${type}:${files.sort().join(',')}`;
    
    // Clear existing debounce timer
    const existingTimer = this.debounceTimers.get(key);
    if (existingTimer) {
      clearTimeout(existingTimer);
    }

    // Create task
    const task: ScheduledTask = {
      id: randomUUID(),
      type,
      files: [...files],
      scheduledAt: new Date(),
      status: 'pending',
    };

    // Set debounce timer
    const timer = setTimeout(() => {
      this.debounceTimers.delete(key);
      this.queue.set(task.id, task);
      this.emit('scheduled', task);
      this.processQueue();
    }, this.debounceMs);

    this.debounceTimers.set(key, timer);
    
    return task.id;
  }

  /**
   * Schedule a task immediately (no debounce)
   */
  scheduleImmediate(type: TaskType, files: string[]): string {
    const task: ScheduledTask = {
      id: randomUUID(),
      type,
      files: [...files],
      scheduledAt: new Date(),
      status: 'pending',
    };

    this.queue.set(task.id, task);
    this.emit('scheduled', task);
    this.processQueue();
    
    return task.id;
  }

  /**
   * Cancel a scheduled task
   */
  cancel(taskId: string): boolean {
    const task = this.queue.get(taskId);
    if (!task || task.status !== 'pending') {
      return false;
    }

    task.status = 'cancelled';
    this.queue.delete(taskId);
    this.emit('cancelled', task);
    return true;
  }

  /**
   * Cancel all pending tasks
   */
  cancelAll(): number {
    let count = 0;
    for (const [taskId, task] of this.queue) {
      if (task.status === 'pending') {
        task.status = 'cancelled';
        this.queue.delete(taskId);
        this.emit('cancelled', task);
        count++;
      }
    }

    // Clear all debounce timers
    for (const timer of this.debounceTimers.values()) {
      clearTimeout(timer);
    }
    this.debounceTimers.clear();

    return count;
  }

  /**
   * Process the task queue
   */
  private async processQueue(): Promise<void> {
    if (this.isProcessing) return;

    const pendingTask = this.getNextPendingTask();
    if (!pendingTask) return;

    this.isProcessing = true;
    this.currentTask = pendingTask;

    try {
      const result = await this.executeTask(pendingTask);
      this.emit('complete', result);
    } catch (error) {
      const result: TaskResult = {
        taskId: pendingTask.id,
        type: pendingTask.type,
        success: false,
        duration: 0,
        issues: [],
        error: error instanceof Error ? error.message : String(error),
        timestamp: new Date(),
      };
      this.emit('complete', result);
    } finally {
      this.queue.delete(pendingTask.id);
      this.currentTask = null;
      this.isProcessing = false;
      
      // Process next task
      setImmediate(() => this.processQueue());
    }
  }

  /**
   * Get next pending task
   */
  private getNextPendingTask(): ScheduledTask | null {
    for (const task of this.queue.values()) {
      if (task.status === 'pending') {
        return task;
      }
    }
    return null;
  }

  /**
   * Execute a task
   */
  private async executeTask(task: ScheduledTask): Promise<TaskResult> {
    const runner = this.runners.get(task.type);
    if (!runner) {
      return {
        taskId: task.id,
        type: task.type,
        success: false,
        duration: 0,
        issues: [],
        error: `No runner registered for task type: ${task.type}`,
        timestamp: new Date(),
      };
    }

    task.status = 'running';
    this.emit('start', task);

    const startTime = Date.now();
    
    try {
      // Filter files that the runner supports
      const supportedFiles = task.files.filter(f => runner.supports(f));
      
      if (supportedFiles.length === 0) {
        return {
          taskId: task.id,
          type: task.type,
          success: true,
          duration: Date.now() - startTime,
          issues: [],
          timestamp: new Date(),
        };
      }

      const issues = await runner.run(supportedFiles);
      const duration = Date.now() - startTime;

      task.status = 'completed';

      return {
        taskId: task.id,
        type: task.type,
        success: issues.filter(i => i.severity === 'error').length === 0,
        duration,
        issues,
        timestamp: new Date(),
      };
    } catch (error) {
      task.status = 'failed';
      return {
        taskId: task.id,
        type: task.type,
        success: false,
        duration: Date.now() - startTime,
        issues: [],
        error: error instanceof Error ? error.message : String(error),
        timestamp: new Date(),
      };
    }
  }

  /**
   * Get queue status
   */
  getStatus(): {
    pending: number;
    running: boolean;
    currentTask: ScheduledTask | null;
  } {
    let pending = 0;
    for (const task of this.queue.values()) {
      if (task.status === 'pending') pending++;
    }

    return {
      pending,
      running: this.isProcessing,
      currentTask: this.currentTask,
    };
  }

  /**
   * Wait for all tasks to complete
   */
  async drain(): Promise<void> {
    return new Promise<void>((resolve) => {
      const check = () => {
        if (!this.isProcessing && this.getNextPendingTask() === null) {
          resolve();
        } else {
          setTimeout(check, 50);
        }
      };
      check();
    });
  }
}

/**
 * Create a TaskScheduler instance
 */
export function createTaskScheduler(debounceMs = 300): TaskScheduler {
  return new TaskScheduler(debounceMs);
}
