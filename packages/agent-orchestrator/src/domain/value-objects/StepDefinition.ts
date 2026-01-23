/**
 * SingleStepEnforcer Types
 *
 * Defines types for enforcing single-step execution in Phase 4.
 * Prevents agents from making multiple changes in a single operation.
 *
 * @see TSK-FR-013 - SingleStepEnforcer型定義
 * @see REQ-FR-090〜092 - SingleStepEnforcer
 * @trace DES-MUSUBIX-FR-001 DES-ORCH-003
 */

/**
 * Step type classification
 */
export type StepType =
  | 'file-create'     // Creating a new file
  | 'file-modify'     // Modifying an existing file
  | 'file-delete'     // Deleting a file
  | 'test-run'        // Running tests
  | 'command-execute' // Executing a command
  | 'review'          // Reviewing code/design
  | 'other';          // Other operations

/**
 * Step status
 */
export type StepStatus =
  | 'pending'     // Not started
  | 'in-progress' // Currently executing
  | 'completed'   // Successfully completed
  | 'failed'      // Failed with error
  | 'blocked';    // Blocked by previous step

/**
 * Step definition
 */
export interface StepDefinition {
  /** Unique step identifier */
  readonly id: string;
  /** Step name */
  readonly name: string;
  /** Step description */
  readonly description: string;
  /** Step type */
  readonly type: StepType;
  /** Target file or resource */
  readonly target?: string;
  /** Dependencies on other steps */
  readonly dependencies?: readonly string[];
  /** Expected duration in ms */
  readonly expectedDurationMs?: number;
}

/**
 * Step execution result
 */
export interface StepExecutionResult {
  /** Step that was executed */
  readonly step: StepDefinition;
  /** Execution status */
  readonly status: StepStatus;
  /** Result message */
  readonly message: string;
  /** Error details if failed */
  readonly error?: string;
  /** Actual duration in ms */
  readonly durationMs: number;
  /** Timestamp */
  readonly completedAt: Date;
  /** Files affected */
  readonly affectedFiles?: readonly string[];
  /** Changes made */
  readonly changes?: readonly StepChange[];
}

/**
 * Individual change within a step
 */
export interface StepChange {
  /** Type of change */
  readonly type: 'add' | 'modify' | 'delete';
  /** File path */
  readonly file: string;
  /** Lines added */
  readonly linesAdded?: number;
  /** Lines removed */
  readonly linesRemoved?: number;
}

/**
 * Step validation result
 */
export interface StepValidationResult {
  /** Whether step is valid */
  readonly valid: boolean;
  /** Validation errors */
  readonly errors: readonly string[];
  /** Validation warnings */
  readonly warnings: readonly string[];
}

/**
 * SingleStepEnforcer configuration
 */
export interface SingleStepConfig {
  /** Maximum files per step */
  readonly maxFilesPerStep: number;
  /** Maximum lines changed per step */
  readonly maxLinesPerStep: number;
  /** Whether to allow multi-file operations */
  readonly allowMultiFile: boolean;
  /** Step timeout in ms */
  readonly stepTimeoutMs: number;
  /** Whether to require confirmation between steps */
  readonly requireConfirmation: boolean;
}

/**
 * Default SingleStepEnforcer configuration
 */
export const DEFAULT_SINGLE_STEP_CONFIG: SingleStepConfig = Object.freeze({
  maxFilesPerStep: 1,
  maxLinesPerStep: 100,
  allowMultiFile: false,
  stepTimeoutMs: 60000, // 1 minute
  requireConfirmation: true,
});

/**
 * Create a step definition
 */
export function createStepDefinition(
  params: Omit<StepDefinition, 'id'> & { id?: string }
): StepDefinition {
  return Object.freeze({
    id: params.id ?? `step-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
    name: params.name,
    description: params.description,
    type: params.type,
    target: params.target,
    dependencies: params.dependencies,
    expectedDurationMs: params.expectedDurationMs,
  });
}

/**
 * Create a step execution result
 */
export function createStepExecutionResult(
  params: Omit<StepExecutionResult, 'completedAt'> & { completedAt?: Date }
): StepExecutionResult {
  return Object.freeze({
    ...params,
    completedAt: params.completedAt ?? new Date(),
  });
}

/**
 * Create SingleStepEnforcer configuration
 */
export function createSingleStepConfig(
  overrides: Partial<SingleStepConfig> = {}
): SingleStepConfig {
  return Object.freeze({
    ...DEFAULT_SINGLE_STEP_CONFIG,
    ...overrides,
  });
}
