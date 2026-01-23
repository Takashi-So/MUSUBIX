/**
 * SingleStepEnforcer Entity
 *
 * Enforces single-step execution in Phase 4 to prevent
 * agents from making multiple changes in a single operation.
 *
 * @see TSK-FR-013〜017 - SingleStepEnforcer
 * @see REQ-FR-090〜092 - SingleStepEnforcer
 * @trace DES-MUSUBIX-FR-001 DES-ORCH-003
 */

import {
  type StepDefinition,
  type StepExecutionResult,
  type StepValidationResult,
  type StepChange,
  type SingleStepConfig,
  createStepExecutionResult,
  DEFAULT_SINGLE_STEP_CONFIG,
} from '../value-objects/StepDefinition.js';

/**
 * Step executor function type
 */
export type StepExecutor = () => Promise<{
  success: boolean;
  affectedFiles: string[];
  linesAdded: number;
  linesRemoved: number;
  error?: string;
}>;

/**
 * Step validation context
 */
export interface StepValidationContext {
  affectedFiles: string[];
  linesChanged: number;
}

/**
 * SingleStepEnforcer Interface
 */
export interface ISingleStepEnforcer {
  /** Validate a step before execution */
  validateStep(step: StepDefinition, context: StepValidationContext): StepValidationResult;

  /** Enforce and execute a step */
  enforceStep(step: StepDefinition, executor: StepExecutor): Promise<StepExecutionResult>;

  /** Get the current step in progress */
  getCurrentStep(): StepDefinition | null;

  /** Get step execution history */
  getStepHistory(): readonly StepExecutionResult[];

  /** Reset enforcer state */
  reset(): void;
}

/**
 * SingleStepEnforcer Implementation
 *
 * Ensures agents execute only one step at a time, preventing
 * runaway operations and maintaining control.
 *
 * @example
 * ```typescript
 * const enforcer = createSingleStepEnforcer();
 *
 * const step = createStepDefinition({
 *   name: 'Modify index.ts',
 *   type: 'file-modify',
 *   target: 'src/index.ts',
 * });
 *
 * const result = await enforcer.enforceStep(step, async () => {
 *   // Perform the actual modification
 *   return { success: true, affectedFiles: ['src/index.ts'], linesAdded: 10, linesRemoved: 5 };
 * });
 * ```
 */
export class SingleStepEnforcer implements ISingleStepEnforcer {
  private readonly config: SingleStepConfig;
  private currentStep: StepDefinition | null = null;
  private history: StepExecutionResult[] = [];

  constructor(config?: SingleStepConfig) {
    this.config = config ?? DEFAULT_SINGLE_STEP_CONFIG;
  }

  /**
   * Validate a step before execution
   */
  validateStep(step: StepDefinition, context: StepValidationContext): StepValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];

    // Check file count
    if (!this.config.allowMultiFile && context.affectedFiles.length > this.config.maxFilesPerStep) {
      errors.push(
        `Step affects ${context.affectedFiles.length} files, but max is ${this.config.maxFilesPerStep}. ` +
        `Single-step enforcement requires one file at a time.`
      );
    }

    // Check line count
    if (context.linesChanged > this.config.maxLinesPerStep) {
      errors.push(
        `Step changes ${context.linesChanged} lines, but max is ${this.config.maxLinesPerStep}. ` +
        `Break down into smaller steps.`
      );
    }

    // Warn if approaching limits (80% threshold)
    const linePercentage = (context.linesChanged / this.config.maxLinesPerStep) * 100;
    if (linePercentage >= 80 && linePercentage < 100) {
      warnings.push(
        `Step changes ${context.linesChanged} lines (${linePercentage.toFixed(0)}% of limit). ` +
        `Consider smaller changes.`
      );
    }

    // Check for concurrent step
    if (this.currentStep !== null) {
      errors.push(
        `Another step "${this.currentStep.name}" is already in progress. ` +
        `Complete it before starting a new step.`
      );
    }

    return Object.freeze({
      valid: errors.length === 0,
      errors: Object.freeze(errors),
      warnings: Object.freeze(warnings),
    });
  }

  /**
   * Enforce and execute a step
   */
  async enforceStep(
    step: StepDefinition,
    executor: StepExecutor
  ): Promise<StepExecutionResult> {
    const startTime = Date.now();

    // Set current step
    this.currentStep = step;

    try {
      // Execute the step
      const executionResult = await this.executeWithTimeout(executor);
      const durationMs = Date.now() - startTime;

      // Clear current step before post-execution validation
      // to avoid false "concurrent step" errors
      this.currentStep = null;

      // Validate post-execution results
      const validation = this.validatePostExecution(step, {
        affectedFiles: executionResult.affectedFiles,
        linesChanged: executionResult.linesAdded + executionResult.linesRemoved,
      });

      // Determine status
      let status: StepExecutionResult['status'];
      let message: string;

      if (!executionResult.success) {
        status = 'failed';
        message = executionResult.error ?? 'Step execution failed';
      } else if (!validation.valid) {
        status = 'blocked';
        message = `Step blocked: ${validation.errors.join('; ')}`;
      } else {
        status = 'completed';
        message = `Step completed successfully in ${durationMs}ms`;
      }

      // Create changes record
      const changes: StepChange[] = executionResult.affectedFiles.map(file => ({
        type: this.determineChangeType(step, file),
        file,
        linesAdded: executionResult.linesAdded,
        linesRemoved: executionResult.linesRemoved,
      }));

      const result = createStepExecutionResult({
        step,
        status,
        message,
        error: executionResult.error,
        durationMs,
        affectedFiles: executionResult.affectedFiles,
        changes,
      });

      // Add to history
      this.history.push(result);
      return result;
    } catch (error) {
      // Clear current step on error
      this.currentStep = null;
      const durationMs = Date.now() - startTime;
      const errorMessage = error instanceof Error ? error.message : String(error);

      const result = createStepExecutionResult({
        step,
        status: 'failed',
        message: `Step execution error: ${errorMessage}`,
        error: errorMessage,
        durationMs,
      });

      this.history.push(result);
      return result;
    }
  }

  /**
   * Validate post-execution results (without concurrent step check)
   */
  private validatePostExecution(step: StepDefinition, context: StepValidationContext): StepValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];

    // Check file count
    if (!this.config.allowMultiFile && context.affectedFiles.length > this.config.maxFilesPerStep) {
      errors.push(
        `Step affects ${context.affectedFiles.length} files, but max is ${this.config.maxFilesPerStep}. ` +
        `Single-step enforcement requires one file at a time.`
      );
    }

    // Check line count
    if (context.linesChanged > this.config.maxLinesPerStep) {
      errors.push(
        `Step changes ${context.linesChanged} lines, but max is ${this.config.maxLinesPerStep}. ` +
        `Break down into smaller steps.`
      );
    }

    return Object.freeze({
      valid: errors.length === 0,
      errors: Object.freeze(errors),
      warnings: Object.freeze(warnings),
    });
  }

  /**
   * Get the current step in progress
   */
  getCurrentStep(): StepDefinition | null {
    return this.currentStep;
  }

  /**
   * Get step execution history
   */
  getStepHistory(): readonly StepExecutionResult[] {
    return Object.freeze([...this.history]);
  }

  /**
   * Reset enforcer state
   */
  reset(): void {
    this.currentStep = null;
    this.history = [];
  }

  // Private helpers

  private async executeWithTimeout(executor: StepExecutor): Promise<{
    success: boolean;
    affectedFiles: string[];
    linesAdded: number;
    linesRemoved: number;
    error?: string;
  }> {
    return new Promise((resolve, reject) => {
      const timeout = setTimeout(() => {
        reject(new Error(`Step execution timed out after ${this.config.stepTimeoutMs}ms`));
      }, this.config.stepTimeoutMs);

      executor()
        .then(result => {
          clearTimeout(timeout);
          resolve(result);
        })
        .catch(error => {
          clearTimeout(timeout);
          reject(error);
        });
    });
  }

  private determineChangeType(
    step: StepDefinition,
    _file: string
  ): 'add' | 'modify' | 'delete' {
    switch (step.type) {
      case 'file-create':
        return 'add';
      case 'file-delete':
        return 'delete';
      default:
        return 'modify';
    }
  }
}

/**
 * Create a SingleStepEnforcer instance
 *
 * @param config - Optional configuration
 * @returns ISingleStepEnforcer instance
 */
export function createSingleStepEnforcer(config?: SingleStepConfig): ISingleStepEnforcer {
  return new SingleStepEnforcer(config);
}
