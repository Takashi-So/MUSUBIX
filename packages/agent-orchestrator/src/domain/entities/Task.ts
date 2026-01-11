/**
 * Task Entity
 * 
 * Represents a task to be analyzed and potentially decomposed
 * 
 * @see REQ-SDD-001 - Task Complexity Evaluation
 * @see DES-SDD-001 - ComplexityAnalyzer
 */

import type { TaskPriority } from '../value-objects/TaskPriority.js';

/**
 * Task entity
 */
export interface Task {
  /** Unique task identifier */
  readonly id: string;
  /** Task title */
  readonly title: string;
  /** Task description */
  readonly description: string;
  /** Priority */
  readonly priority: TaskPriority;
  /** Estimated scope (number of components affected) */
  readonly estimatedScope: number;
  /** Number of dependencies */
  readonly dependencyCount: number;
  /** Estimated file count to modify */
  readonly estimatedFileCount: number;
  /** Test coverage requirement */
  readonly testCoverageRequired: number;
  /** Uncertainty level (1-10) */
  readonly uncertaintyLevel: number;
  /** Parent task ID (if subtask) */
  readonly parentTaskId?: string;
  /** Related requirement IDs */
  readonly relatedRequirements: readonly string[];
  /** Related design IDs */
  readonly relatedDesigns: readonly string[];
  /** Created timestamp */
  readonly createdAt: Date;
}

/**
 * Task creation input
 */
export interface CreateTaskInput {
  id: string;
  title: string;
  description: string;
  priority: TaskPriority;
  estimatedScope?: number;
  dependencyCount?: number;
  estimatedFileCount?: number;
  testCoverageRequired?: number;
  uncertaintyLevel?: number;
  parentTaskId?: string;
  relatedRequirements?: string[];
  relatedDesigns?: string[];
}

/**
 * Create a Task entity
 * 
 * @param input - Task creation input
 * @returns Task entity
 */
export function createTask(input: CreateTaskInput): Task {
  return Object.freeze({
    id: input.id,
    title: input.title,
    description: input.description,
    priority: input.priority,
    estimatedScope: input.estimatedScope ?? 1,
    dependencyCount: input.dependencyCount ?? 0,
    estimatedFileCount: input.estimatedFileCount ?? 1,
    testCoverageRequired: input.testCoverageRequired ?? 80,
    uncertaintyLevel: input.uncertaintyLevel ?? 5,
    parentTaskId: input.parentTaskId,
    relatedRequirements: Object.freeze([...(input.relatedRequirements ?? [])]),
    relatedDesigns: Object.freeze([...(input.relatedDesigns ?? [])]),
    createdAt: new Date(),
  });
}

/**
 * Check if task is a subtask
 * 
 * @param task - Task to check
 * @returns true if task has parent
 */
export function isSubtask(task: Task): boolean {
  return task.parentTaskId !== undefined;
}
