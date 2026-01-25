/**
 * @fileoverview Quality Gate Integration Types
 * Integrates verification-loop skill with workflow-engine QualityGate
 * 
 * @traceability TSK-INT-005, DES-v3.7.0 Section 9.4
 */

import type { PhaseType } from '../domain/value-objects/PhaseType.js';

/**
 * Verification phases (from verification-loop skill)
 */
export type VerificationPhase = 
  | 'build'
  | 'type-check'
  | 'lint'
  | 'test'
  | 'security'
  | 'diff-review';

/**
 * Verification result for a single phase
 */
export interface VerificationPhaseResult {
  /** Phase that was verified */
  phase: VerificationPhase;
  /** Whether phase passed */
  passed: boolean;
  /** Duration in milliseconds */
  durationMs: number;
  /** Output from verification */
  output?: string;
  /** Errors found */
  errors?: VerificationError[];
  /** Warnings found */
  warnings?: VerificationWarning[];
  /** Files examined */
  filesExamined?: number;
}

/**
 * Verification error
 */
export interface VerificationError {
  /** Error message */
  message: string;
  /** File path */
  file?: string;
  /** Line number */
  line?: number;
  /** Column number */
  column?: number;
  /** Error code */
  code?: string;
  /** Error severity */
  severity: 'error' | 'fatal';
}

/**
 * Verification warning
 */
export interface VerificationWarning {
  /** Warning message */
  message: string;
  /** File path */
  file?: string;
  /** Line number */
  line?: number;
  /** Warning code */
  code?: string;
}

/**
 * Complete verification result
 */
export interface VerificationResult {
  /** Unique verification ID */
  id: string;
  /** Timestamp of verification */
  timestamp: string;
  /** Overall pass/fail */
  passed: boolean;
  /** Verification mode */
  mode: 'quick' | 'full';
  /** Results by phase */
  phases: VerificationPhaseResult[];
  /** Total duration in milliseconds */
  totalDurationMs: number;
  /** Summary statistics */
  summary: VerificationSummary;
}

/**
 * Verification summary
 */
export interface VerificationSummary {
  /** Phases passed */
  phasesPassed: number;
  /** Phases failed */
  phasesFailed: number;
  /** Total errors */
  totalErrors: number;
  /** Total warnings */
  totalWarnings: number;
  /** Files examined */
  filesExamined: number;
}

/**
 * Quality gate criteria for workflow phases
 */
export interface QualityGateCriteria {
  /** Workflow phase this criteria applies to */
  workflowPhase: PhaseType;
  /** Required verification phases to pass */
  requiredVerificationPhases: VerificationPhase[];
  /** Maximum allowed errors (0 = none allowed) */
  maxErrors: number;
  /** Maximum allowed warnings (-1 = unlimited) */
  maxWarnings: number;
  /** Minimum test coverage percentage (-1 = no requirement) */
  minTestCoverage: number;
  /** Minimum lint score (-1 = no requirement) */
  minLintScore: number;
  /** Require security scan pass */
  requireSecurityPass: boolean;
  /** Require diff review */
  requireDiffReview: boolean;
}

/**
 * Default quality gate criteria per workflow phase
 */
export const DEFAULT_QUALITY_GATE_CRITERIA: ReadonlyMap<PhaseType, QualityGateCriteria> = new Map([
  ['requirements', {
    workflowPhase: 'requirements',
    requiredVerificationPhases: [],
    maxErrors: 0,
    maxWarnings: -1,
    minTestCoverage: -1,
    minLintScore: -1,
    requireSecurityPass: false,
    requireDiffReview: false,
  }],
  ['design', {
    workflowPhase: 'design',
    requiredVerificationPhases: [],
    maxErrors: 0,
    maxWarnings: -1,
    minTestCoverage: -1,
    minLintScore: -1,
    requireSecurityPass: false,
    requireDiffReview: false,
  }],
  ['task-breakdown', {
    workflowPhase: 'task-breakdown',
    requiredVerificationPhases: [],
    maxErrors: 0,
    maxWarnings: -1,
    minTestCoverage: -1,
    minLintScore: -1,
    requireSecurityPass: false,
    requireDiffReview: false,
  }],
  ['implementation', {
    workflowPhase: 'implementation',
    requiredVerificationPhases: ['build', 'type-check', 'lint', 'test'],
    maxErrors: 0,
    maxWarnings: 20,
    minTestCoverage: 80,
    minLintScore: -1,
    requireSecurityPass: true,
    requireDiffReview: true,
  }],
  ['completion', {
    workflowPhase: 'completion',
    requiredVerificationPhases: ['build', 'type-check', 'lint', 'test', 'security', 'diff-review'],
    maxErrors: 0,
    maxWarnings: 10,
    minTestCoverage: 85,
    minLintScore: -1,
    requireSecurityPass: true,
    requireDiffReview: true,
  }],
]);

/**
 * Quality gate check result
 */
export interface QualityGateCheckResult {
  /** Whether gate passed */
  passed: boolean;
  /** Workflow phase checked */
  workflowPhase: PhaseType;
  /** Criteria used for check */
  criteria: QualityGateCriteria;
  /** Verification result used */
  verificationResult?: VerificationResult;
  /** Failures (if any) */
  failures: QualityGateFailure[];
  /** Checked at timestamp */
  checkedAt: string;
}

/**
 * Quality gate failure detail
 */
export interface QualityGateFailure {
  /** Failure type */
  type: 'verification_phase' | 'error_count' | 'warning_count' | 'coverage' | 'security' | 'diff_review';
  /** Failure message */
  message: string;
  /** Expected value */
  expected: string;
  /** Actual value */
  actual: string;
}

/**
 * Configuration for QualityGate Integration
 */
export interface QualityGateIntegrationConfig {
  /** Custom criteria overrides */
  criteriaOverrides?: Partial<Record<PhaseType, Partial<QualityGateCriteria>>>;
  /** Enable strict mode (all phases must pass) */
  strictMode: boolean;
  /** Verification script path */
  verificationScriptPath: string;
  /** Timeout for verification in milliseconds */
  verificationTimeoutMs: number;
}

/**
 * Default configuration
 */
export const DEFAULT_QUALITY_GATE_INTEGRATION_CONFIG: QualityGateIntegrationConfig = {
  strictMode: true,
  verificationScriptPath: '.github/skills/verification-loop/scripts/verify.sh',
  verificationTimeoutMs: 600000, // 10 minutes
};

/**
 * Interface for QualityGate Integration
 */
export interface QualityGateIntegration {
  /**
   * Run verification for a workflow phase
   */
  runVerification(
    workflowPhase: PhaseType,
    mode?: 'quick' | 'full'
  ): Promise<VerificationResult>;
  
  /**
   * Check quality gate for a workflow phase
   */
  checkQualityGate(
    workflowPhase: PhaseType,
    verificationResult?: VerificationResult
  ): Promise<QualityGateCheckResult>;
  
  /**
   * Get quality gate criteria for a phase
   */
  getCriteria(workflowPhase: PhaseType): QualityGateCriteria;
  
  /**
   * Update criteria for a phase
   */
  updateCriteria(
    workflowPhase: PhaseType,
    updates: Partial<QualityGateCriteria>
  ): void;
  
  /**
   * Get verification history
   */
  getVerificationHistory(
    limit?: number
  ): VerificationResult[];
  
  /**
   * Get last verification result
   */
  getLastVerification(): VerificationResult | undefined;
  
  /**
   * Format verification result as markdown
   */
  formatResultAsMarkdown(result: VerificationResult): string;
  
  /**
   * Format quality gate check as markdown
   */
  formatQualityGateCheckAsMarkdown(check: QualityGateCheckResult): string;
}
