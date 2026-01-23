/**
 * TriageEngine Entity
 *
 * Manages task triage and priority blocking for the SDD workflow.
 * Prevents new work from starting when high-priority tasks are unresolved.
 *
 * @see TSK-FR-023〜027 - TriageEngine
 * @see REQ-FR-040〜041 - TriageEngine
 * @trace DES-MUSUBIX-FR-001 DES-WORKFLOW-001
 */

import {
  type PriorityLevel,
  type TriageResult,
  type TriageCheckResult,
  type TriageTask,
  type TriageConfig,
  comparePriority,
  createTriageResult,
  createTriageCheckResult,
  DEFAULT_TRIAGE_CONFIG,
} from '../value-objects/PriorityLevel.js';

/**
 * TriageEngine Interface
 */
export interface ITriageEngine {
  /** Check if there are blocking tasks that prevent new work */
  checkPriorityBlocking(): Promise<TriageCheckResult>;

  /** Triage a task and assign priority */
  triageTask(task: TriageTask): Promise<TriageResult>;

  /** Get all blocking tasks sorted by priority */
  getBlockingTasks(): Promise<readonly TriageResult[]>;

  /** Add a task to the engine */
  addTask(task: TriageTask): void;

  /** Remove a task from the engine */
  removeTask(taskId: string): void;

  /** Update a task */
  updateTask(taskId: string, updates: Partial<TriageTask>): void;

  /** Get all tasks */
  getTasks(): readonly TriageTask[];

  /** Clear all tasks */
  clear(): void;
}

/**
 * TriageEngine Implementation
 *
 * Implements task triage logic to manage work prioritization
 * and prevent starting new features when critical issues exist.
 *
 * @example
 * ```typescript
 * const engine = createTriageEngine();
 *
 * // Add tasks
 * engine.addTask({ id: 'TSK-001', title: 'Critical Bug', priority: 'P0', status: 'open', type: 'bug', createdAt: new Date() });
 *
 * // Check if new work can be started
 * const result = await engine.checkPriorityBlocking();
 * if (!result.passed) {
 *   console.log('Cannot start new work:', result.message);
 * }
 * ```
 */
export class TriageEngine implements ITriageEngine {
  private readonly config: TriageConfig;
  private tasks: Map<string, TriageTask> = new Map();

  constructor(config?: TriageConfig) {
    this.config = config ?? DEFAULT_TRIAGE_CONFIG;
  }

  /**
   * Check if there are blocking tasks that prevent new work
   */
  async checkPriorityBlocking(): Promise<TriageCheckResult> {
    const blockingTasks = await this.getBlockingTasks();

    if (blockingTasks.length === 0) {
      return createTriageCheckResult({
        passed: true,
        message: 'No blocking tasks found. New work can proceed.',
        severity: 'info',
        blockingTasks: [],
      });
    }

    // Determine severity based on highest priority
    const highestPriority = blockingTasks[0].priority;
    const severity = highestPriority === 'P0' ? 'error' : 'warning';

    const taskList = blockingTasks
      .map(t => `${t.taskId} (${t.priority}): ${t.reason}`)
      .join('; ');

    return createTriageCheckResult({
      passed: false,
      message: `${blockingTasks.length} blocking task(s) found. Resolve before starting new work.`,
      severity,
      blockingTasks,
      details: taskList,
    });
  }

  /**
   * Triage a task and assign priority
   */
  async triageTask(task: TriageTask): Promise<TriageResult> {
    // If task already has priority, preserve it
    if (task.priority) {
      return createTriageResult({
        taskId: task.id,
        priority: task.priority,
        reason: 'Priority already assigned',
        suggestedAction: this.getSuggestedAction(task.priority, task.type),
      });
    }

    // Auto-triage based on task type and characteristics
    const priority = this.autoAssignPriority(task);
    const reason = this.getTriageReason(task, priority);

    return createTriageResult({
      taskId: task.id,
      priority,
      reason,
      suggestedAction: this.getSuggestedAction(priority, task.type),
    });
  }

  /**
   * Get all blocking tasks sorted by priority
   */
  async getBlockingTasks(): Promise<readonly TriageResult[]> {
    const blockingTasks: TriageResult[] = [];

    for (const task of this.tasks.values()) {
      // Check if task is in active status
      if (!this.config.activeStatuses.includes(task.status)) {
        continue;
      }

      // Check if task priority blocks new work
      const priority = task.priority ?? 'P2';
      if (!this.config.blockingPriorities.includes(priority)) {
        continue;
      }

      // Check if in-progress tasks should be included
      if (task.status === 'in-progress' && !this.config.includeInProgress) {
        continue;
      }

      // Check task age
      const ageDays = this.getTaskAgeDays(task);
      if (ageDays > this.config.maxBlockingAgeDays) {
        continue; // Task is too old to block
      }

      blockingTasks.push(
        createTriageResult({
          taskId: task.id,
          priority,
          reason: `${task.title} (${task.status})`,
          suggestedAction: this.getSuggestedAction(priority, task.type),
        })
      );
    }

    // Sort by priority (P0 first)
    blockingTasks.sort((a, b) => comparePriority(a.priority, b.priority));

    return Object.freeze(blockingTasks);
  }

  /**
   * Add a task to the engine
   */
  addTask(task: TriageTask): void {
    this.tasks.set(task.id, task);
  }

  /**
   * Remove a task from the engine
   */
  removeTask(taskId: string): void {
    this.tasks.delete(taskId);
  }

  /**
   * Update a task
   */
  updateTask(taskId: string, updates: Partial<TriageTask>): void {
    const task = this.tasks.get(taskId);
    if (task) {
      this.tasks.set(taskId, { ...task, ...updates, updatedAt: new Date() });
    }
  }

  /**
   * Get all tasks
   */
  getTasks(): readonly TriageTask[] {
    return Object.freeze([...this.tasks.values()]);
  }

  /**
   * Clear all tasks
   */
  clear(): void {
    this.tasks.clear();
  }

  // Private helpers

  private autoAssignPriority(task: TriageTask): PriorityLevel {
    // Bugs are higher priority
    if (task.type === 'bug') {
      // Check for critical keywords
      const title = task.title.toLowerCase();
      const description = task.description?.toLowerCase() ?? '';
      const text = `${title} ${description}`;

      if (
        text.includes('crash') ||
        text.includes('data loss') ||
        text.includes('security') ||
        text.includes('critical')
      ) {
        return 'P0';
      }
      return 'P1';
    }

    // Features and improvements are lower priority
    if (task.type === 'feature') {
      return 'P2';
    }

    if (task.type === 'improvement') {
      return 'P3';
    }

    // Default to P2
    return 'P2';
  }

  private getTriageReason(task: TriageTask, priority: PriorityLevel): string {
    switch (priority) {
      case 'P0':
        return `Critical ${task.type}: Requires immediate attention`;
      case 'P1':
        return `High priority ${task.type}: Should be resolved soon`;
      case 'P2':
        return `Normal priority ${task.type}: Standard workflow`;
      case 'P3':
        return `Low priority ${task.type}: Can be deferred`;
    }
  }

  private getSuggestedAction(priority: PriorityLevel, type: TriageTask['type']): string {
    if (priority === 'P0') {
      return 'Stop current work and address immediately';
    }
    if (priority === 'P1') {
      return 'Add to current sprint and prioritize';
    }
    if (type === 'bug') {
      return 'Schedule for next available slot';
    }
    return 'Add to backlog for planning';
  }

  private getTaskAgeDays(task: TriageTask): number {
    const now = Date.now();
    const created = task.createdAt.getTime();
    return Math.floor((now - created) / (1000 * 60 * 60 * 24));
  }
}

/**
 * Create a TriageEngine instance
 *
 * @param config - Optional configuration
 * @returns ITriageEngine instance
 */
export function createTriageEngine(config?: TriageConfig): ITriageEngine {
  return new TriageEngine(config);
}
