/**
 * Verification Loop Types
 *
 * Type definitions for verification loop skill
 *
 * @see REQ-VL-001 - Multi-Phase Verification
 * @see REQ-VL-002 - Verification Report
 * @see REQ-VL-003 - Continuous Verification
 * @see REQ-VL-004 - Verification Modes (quick/full)
 * @see REQ-VL-005 - Stop Hook監査
 */

/**
 * Verification phase
 */
export type VerificationPhase =
  | 'build'
  | 'type-check'
  | 'lint'
  | 'test'
  | 'security'
  | 'diff';

/**
 * Verification mode
 *
 * @see REQ-VL-004 - Verification Modes
 */
export type VerificationMode = 'quick' | 'full';

/**
 * Phase result status
 */
export type PhaseStatus = 'pass' | 'fail' | 'warning' | 'skipped';

/**
 * Phase result
 *
 * @see REQ-VL-001 - Multi-Phase Verification
 */
export interface PhaseResult {
  readonly phase: VerificationPhase;
  readonly status: PhaseStatus;
  readonly duration: number;
  readonly errors?: number;
  readonly warnings?: number;
  readonly details?: string;
}

/**
 * Test phase result
 */
export interface TestPhaseResult extends PhaseResult {
  readonly phase: 'test';
  readonly passed: number;
  readonly total: number;
  readonly coverage?: number;
}

/**
 * Diff phase result
 */
export interface DiffPhaseResult extends PhaseResult {
  readonly phase: 'diff';
  readonly filesChanged: number;
  readonly additions: number;
  readonly deletions: number;
}

/**
 * Verification report
 *
 * @see REQ-VL-002 - Verification Report
 */
export interface VerificationReport {
  readonly id: string;
  readonly mode: VerificationMode;
  readonly startedAt: Date;
  readonly completedAt: Date;
  readonly totalDuration: number;
  readonly phases: PhaseResult[];
  readonly overall: 'ready' | 'not-ready';
  readonly issues: VerificationIssue[];
}

/**
 * Verification issue
 */
export interface VerificationIssue {
  readonly id: string;
  readonly phase: VerificationPhase;
  readonly severity: 'error' | 'warning' | 'info';
  readonly message: string;
  readonly file?: string;
  readonly line?: number;
}

/**
 * Stop Hook audit item
 *
 * @see REQ-VL-005 - Stop Hook監査
 */
export type AuditItemType =
  | 'console-log'
  | 'debugger'
  | 'todo-fixme'
  | 'uncommitted';

/**
 * Stop Hook audit result
 *
 * @see REQ-VL-005 - Stop Hook監査
 */
export interface StopHookAuditItem {
  readonly type: AuditItemType;
  readonly file: string;
  readonly line?: number;
  readonly content: string;
}

/**
 * Stop Hook audit report
 */
export interface StopHookAuditReport {
  readonly timestamp: Date;
  readonly editedFiles: string[];
  readonly items: StopHookAuditItem[];
  readonly hasIssues: boolean;
}

/**
 * Continuous verification suggestion
 *
 * @see REQ-VL-003 - Continuous Verification
 */
export interface ContinuousVerificationSuggestion {
  readonly reason: 'time-based' | 'change-based';
  readonly elapsedMinutes?: number;
  readonly changedFiles?: number;
  readonly recommendation: string;
}

/**
 * Verification loop configuration
 */
export interface VerificationLoopConfig {
  readonly projectRoot: string;
  readonly reportsDir: string;
  readonly buildCommand: string;
  readonly typeCheckCommand: string;
  readonly lintCommand: string;
  readonly testCommand: string;
  readonly securityCommand?: string;
  readonly continuousIntervalMinutes: number;
  readonly continuousChangeThreshold: number;
}

/**
 * Default verification loop configuration
 */
export const DEFAULT_VERIFICATION_LOOP_CONFIG: VerificationLoopConfig = {
  projectRoot: '.',
  reportsDir: '.reports',
  buildCommand: 'npm run build',
  typeCheckCommand: 'npx tsc --noEmit',
  lintCommand: 'npm run lint',
  testCommand: 'npm test',
  securityCommand: undefined,
  continuousIntervalMinutes: 15,
  continuousChangeThreshold: 10,
};

/**
 * Verification loop manager interface
 */
export interface VerificationLoopManager {
  /**
   * Run verification
   *
   * @param mode - Verification mode (quick/full)
   * @returns Verification report
   */
  runVerification(mode?: VerificationMode): Promise<VerificationReport>;

  /**
   * Run single phase
   *
   * @param phase - Phase to run
   * @returns Phase result
   */
  runPhase(phase: VerificationPhase): Promise<PhaseResult>;

  /**
   * Run stop hook audit
   *
   * @param editedFiles - Files edited during session
   * @returns Audit report
   */
  runStopHookAudit(editedFiles: string[]): Promise<StopHookAuditReport>;

  /**
   * Check if continuous verification should run
   *
   * @param sessionStartTime - Session start time
   * @param changedFileCount - Number of changed files
   * @returns Suggestion or null
   */
  checkContinuousVerification(
    sessionStartTime: Date,
    changedFileCount: number
  ): ContinuousVerificationSuggestion | null;

  /**
   * Format report as markdown
   *
   * @param report - Verification report
   * @returns Markdown string
   */
  formatReportMarkdown(report: VerificationReport): string;

  /**
   * Get configuration
   */
  getConfig(): VerificationLoopConfig;
}
