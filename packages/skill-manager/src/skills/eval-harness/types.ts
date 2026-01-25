/**
 * Eval Harness Types
 *
 * Type definitions for evaluation harness skill
 *
 * @see REQ-EH-001 - Capability Eval Definition
 * @see REQ-EH-002 - Regression Eval Definition
 * @see REQ-EH-003 - pass@k Metrics
 * @see REQ-EH-004 - Grader Types
 * @see REQ-EH-005 - Human Grader Support
 */

/**
 * Evaluation type
 */
export type EvalType = 'capability' | 'regression';

/**
 * Evaluation status
 */
export type EvalStatus = 'pending' | 'running' | 'passed' | 'failed' | 'skipped';

/**
 * Grader type for evaluation
 *
 * @see REQ-EH-004 - Grader Types
 */
export type GraderType = 'code-based' | 'model-based' | 'human';

/**
 * Success criterion for capability eval
 *
 * @see REQ-EH-001 - Capability Eval Definition
 */
export interface SuccessCriterion {
  readonly id: string;
  readonly description: string;
  readonly status: EvalStatus;
  readonly notes?: string;
}

/**
 * Capability evaluation definition
 *
 * @see REQ-EH-001 - Capability Eval Definition
 */
export interface CapabilityEval {
  readonly id: string;
  readonly name: string;
  readonly task: string;
  readonly successCriteria: SuccessCriterion[];
  readonly expectedOutput: string;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

/**
 * Test result for regression eval
 *
 * @see REQ-EH-002 - Regression Eval Definition
 */
export interface TestResult {
  readonly name: string;
  readonly status: 'pass' | 'fail';
  readonly duration?: number;
  readonly error?: string;
}

/**
 * Regression evaluation definition
 *
 * @see REQ-EH-002 - Regression Eval Definition
 */
export interface RegressionEval {
  readonly id: string;
  readonly name: string;
  readonly baseline: string; // SHA or checkpoint name
  readonly tests: TestResult[];
  readonly passedCount: number;
  readonly totalCount: number;
  readonly previousPassedCount: number;
  readonly createdAt: Date;
}

/**
 * pass@k metrics result
 *
 * @see REQ-EH-003 - pass@k Metrics
 */
export interface PassAtKMetrics {
  /** First attempt success rate */
  readonly passAt1: number;
  /** At least one success in k attempts */
  readonly passAt3: number;
  /** All k attempts successful */
  readonly consecutiveAt3: number;
  /** Total attempts made */
  readonly totalAttempts: number;
  /** Successful attempts */
  readonly successfulAttempts: number;
}

/**
 * Code-based grader configuration
 *
 * @see REQ-EH-004 - Grader Types
 */
export interface CodeBasedGraderConfig {
  readonly type: 'code-based';
  readonly command: string;
  readonly expectedExitCode: number;
  readonly timeout: number;
  readonly matchOutput?: string | RegExp;
}

/**
 * Model-based grader configuration
 *
 * @see REQ-EH-004 - Grader Types
 */
export interface ModelBasedGraderConfig {
  readonly type: 'model-based';
  readonly prompt: string;
  readonly model?: string;
  readonly temperature?: number;
}

/**
 * Human grader checklist item
 *
 * @see REQ-EH-005 - Human Grader Support
 */
export interface HumanGraderChecklistItem {
  readonly id: string;
  readonly description: string;
  readonly checked: boolean;
}

/**
 * Human grader configuration
 *
 * @see REQ-EH-005 - Human Grader Support
 */
export interface HumanGraderConfig {
  readonly type: 'human';
  readonly reviewer?: string;
  readonly checklist: HumanGraderChecklistItem[];
  readonly notes?: string;
  readonly verdict?: 'pass' | 'fail';
}

/**
 * Grader configuration union type
 */
export type GraderConfig =
  | CodeBasedGraderConfig
  | ModelBasedGraderConfig
  | HumanGraderConfig;

/**
 * Evaluation run result
 */
export interface EvalRunResult {
  readonly evalId: string;
  readonly evalType: EvalType;
  readonly graderType: GraderType;
  readonly status: EvalStatus;
  readonly startedAt: Date;
  readonly completedAt?: Date;
  readonly duration?: number;
  readonly metrics?: PassAtKMetrics;
  readonly error?: string;
  readonly output?: string;
}

/**
 * Eval harness configuration
 */
export interface EvalHarnessConfig {
  readonly evalsDir: string;
  readonly reportsDir: string;
  readonly defaultTimeout: number;
  readonly maxRetries: number;
}

/**
 * Default eval harness configuration
 */
export const DEFAULT_EVAL_HARNESS_CONFIG: EvalHarnessConfig = {
  evalsDir: '.musubix/evals',
  reportsDir: '.reports/evals',
  defaultTimeout: 30000, // 30 seconds
  maxRetries: 3,
};

/**
 * Eval harness manager interface
 */
export interface EvalHarnessManager {
  /**
   * Create a capability evaluation
   *
   * @param name - Evaluation name
   * @param task - Task description
   * @param criteria - Success criteria
   * @param expectedOutput - Expected output
   * @returns Created capability eval
   */
  createCapabilityEval(
    name: string,
    task: string,
    criteria: string[],
    expectedOutput: string
  ): Promise<CapabilityEval>;

  /**
   * Create a regression evaluation
   *
   * @param name - Evaluation name
   * @param baseline - Baseline SHA or checkpoint
   * @param tests - Test results
   * @param previousPassedCount - Previous pass count
   * @returns Created regression eval
   */
  createRegressionEval(
    name: string,
    baseline: string,
    tests: TestResult[],
    previousPassedCount: number
  ): Promise<RegressionEval>;

  /**
   * Run evaluation with specified grader
   *
   * @param evalId - Evaluation ID
   * @param graderConfig - Grader configuration
   * @returns Evaluation run result
   */
  runEval(evalId: string, graderConfig: GraderConfig): Promise<EvalRunResult>;

  /**
   * Calculate pass@k metrics
   *
   * @param evalId - Evaluation ID
   * @param k - Number of attempts (default: 3)
   * @returns pass@k metrics
   */
  calculatePassAtK(evalId: string, k?: number): Promise<PassAtKMetrics>;

  /**
   * Generate human grader checklist template
   *
   * @param evalId - Evaluation ID
   * @param reviewer - Reviewer username
   * @returns Human grader configuration
   */
  generateHumanGraderTemplate(
    evalId: string,
    reviewer?: string
  ): Promise<HumanGraderConfig>;

  /**
   * Record human grader verdict
   *
   * @param evalId - Evaluation ID
   * @param verdict - Human verdict
   * @param notes - Optional notes
   * @returns Updated eval run result
   */
  recordHumanVerdict(
    evalId: string,
    verdict: 'pass' | 'fail',
    notes?: string
  ): Promise<EvalRunResult>;

  /**
   * Get evaluation by ID
   *
   * @param evalId - Evaluation ID
   * @returns Capability or Regression eval
   */
  getEval(evalId: string): Promise<CapabilityEval | RegressionEval | null>;

  /**
   * List all evaluations
   *
   * @param type - Optional filter by type
   * @returns Array of evaluations
   */
  listEvals(type?: EvalType): Promise<Array<CapabilityEval | RegressionEval>>;

  /**
   * Get configuration
   */
  getConfig(): EvalHarnessConfig;
}
