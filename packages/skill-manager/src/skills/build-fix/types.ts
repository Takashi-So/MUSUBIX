/**
 * Build Fix Types
 *
 * Type definitions for build fix skill
 *
 * @see REQ-BF-001 - Build Error Analysis
 * @see REQ-BF-002 - Iterative Fix Strategy
 * @see REQ-BF-003 - Fix Report
 */

/**
 * Build error category
 *
 * @see REQ-BF-001 - Build Error Analysis
 */
export type BuildErrorCategory =
  | 'type-error'
  | 'import-error'
  | 'syntax-error'
  | 'lint-error'
  | 'config-error'
  | 'dependency-error'
  | 'unknown';

/**
 * Build error priority
 */
export type BuildErrorPriority = 'high' | 'medium' | 'low';

/**
 * Build error
 *
 * @see REQ-BF-001 - Build Error Analysis
 */
export interface BuildError {
  readonly id: string;
  readonly category: BuildErrorCategory;
  readonly priority: BuildErrorPriority;
  readonly code?: string;
  readonly message: string;
  readonly file?: string;
  readonly line?: number;
  readonly column?: number;
  readonly suggestion?: string;
}

/**
 * Fix attempt result
 *
 * @see REQ-BF-002 - Iterative Fix Strategy
 */
export interface FixAttempt {
  readonly iteration: number;
  readonly error: BuildError;
  readonly fix: string;
  readonly success: boolean;
  readonly newErrorsIntroduced: number;
  readonly timestamp: Date;
}

/**
 * Fix strategy
 */
export interface FixStrategy {
  readonly errorId: string;
  readonly steps: string[];
  readonly estimatedImpact: 'high' | 'medium' | 'low';
  readonly requiresUserApproval: boolean;
}

/**
 * Fix report
 *
 * @see REQ-BF-003 - Fix Report
 */
export interface FixReport {
  readonly id: string;
  readonly startedAt: Date;
  readonly completedAt: Date;
  readonly totalIterations: number;
  readonly errorsFixed: number;
  readonly errorsRemaining: number;
  readonly filesModified: string[];
  readonly warnings: string[];
  readonly attempts: FixAttempt[];
}

/**
 * Build output
 */
export interface BuildOutput {
  readonly success: boolean;
  readonly stdout: string;
  readonly stderr: string;
  readonly errors: BuildError[];
  readonly duration: number;
}

/**
 * Build fix configuration
 */
export interface BuildFixConfig {
  readonly projectRoot: string;
  readonly buildCommand: string;
  readonly typeCheckCommand: string;
  readonly maxIterations: number;
  readonly autoFix: boolean;
  readonly skipLintErrors: boolean;
}

/**
 * Default build fix configuration
 */
export const DEFAULT_BUILD_FIX_CONFIG: BuildFixConfig = {
  projectRoot: '.',
  buildCommand: 'npm run build',
  typeCheckCommand: 'npx tsc --noEmit',
  maxIterations: 10,
  autoFix: false,
  skipLintErrors: false,
};

/**
 * Build fix manager interface
 */
export interface BuildFixManager {
  /**
   * Analyze build output for errors
   *
   * @param output - Raw build output
   * @returns Array of categorized build errors
   */
  analyzeErrors(output: string): BuildError[];

  /**
   * Run build and analyze errors
   *
   * @returns Build output with parsed errors
   */
  runBuild(): Promise<BuildOutput>;

  /**
   * Generate fix strategy for an error
   *
   * @param error - Build error to fix
   * @returns Fix strategy
   */
  generateFixStrategy(error: BuildError): FixStrategy;

  /**
   * Apply a fix
   *
   * @param strategy - Fix strategy to apply
   * @returns Success status
   */
  applyFix(strategy: FixStrategy): Promise<boolean>;

  /**
   * Run iterative fix loop
   *
   * @returns Fix report
   */
  runIterativeFix(): Promise<FixReport>;

  /**
   * Get most impactful errors
   *
   * @param errors - Array of errors
   * @param limit - Maximum number to return
   * @returns Sorted errors by impact
   */
  getMostImpactfulErrors(errors: BuildError[], limit?: number): BuildError[];

  /**
   * Get configuration
   */
  getConfig(): BuildFixConfig;
}
