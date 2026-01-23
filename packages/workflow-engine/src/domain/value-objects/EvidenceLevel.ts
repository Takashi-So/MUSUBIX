/**
 * EvidenceLevel Value Objects
 *
 * Defines evidence levels required for Phase 5 completion validation.
 *
 * @see TSK-FR-018 - EvidenceLevel型定義
 * @see REQ-FR-120〜125 - EvidenceLevelValidator
 * @trace DES-MUSUBIX-FR-001 DES-WF-003
 */

/**
 * Evidence level tier
 * - mandatory: Required for phase completion
 * - recommended: Should be provided but not blocking
 * - optional: Nice to have
 */
export type EvidenceTier = 'mandatory' | 'recommended' | 'optional';

/**
 * Evidence type categories
 */
export type EvidenceType =
  | 'test-result'        // Test execution results
  | 'coverage-report'    // Code coverage metrics
  | 'lint-result'        // Linting results
  | 'security-scan'      // Security scan results
  | 'review-approval'    // Code review approval
  | 'performance-test'   // Performance test results
  | 'documentation'      // Documentation artifacts
  | 'traceability'       // Traceability matrix
  | 'adr'                // Architecture Decision Record
  | 'changelog';         // Changelog entry

/**
 * Evidence record
 */
export interface EvidenceRecord {
  readonly id: string;
  readonly type: EvidenceType;
  readonly tier: EvidenceTier;
  readonly description: string;
  readonly artifact?: string;          // Path or reference to artifact
  readonly timestamp?: number;         // When evidence was collected
  readonly validator?: string;         // Who/what validated
  readonly metadata?: Record<string, unknown>;
}

/**
 * Evidence requirement definition
 */
export interface EvidenceRequirement {
  readonly type: EvidenceType;
  readonly tier: EvidenceTier;
  readonly description: string;
  readonly validationRule?: string;    // Optional validation expression
}

/**
 * Evidence validation result
 */
export interface EvidenceValidationResult {
  readonly valid: boolean;
  readonly errors: readonly string[];
  readonly warnings: readonly string[];
  readonly missingMandatory: readonly EvidenceRequirement[];
  readonly missingRecommended: readonly EvidenceRequirement[];
  readonly completeness: {
    readonly mandatory: number;        // 0-100%
    readonly recommended: number;      // 0-100%
    readonly overall: number;          // 0-100%
  };
}

/**
 * Evidence configuration per phase
 */
export interface PhaseEvidenceConfig {
  readonly phase: number;
  readonly requirements: readonly EvidenceRequirement[];
}

/**
 * Default evidence requirements for Phase 5 (Completion)
 */
export const PHASE5_EVIDENCE_REQUIREMENTS: readonly EvidenceRequirement[] = Object.freeze([
  // Mandatory evidence
  {
    type: 'test-result',
    tier: 'mandatory',
    description: 'All tests must pass',
    validationRule: 'passRate === 100',
  },
  {
    type: 'lint-result',
    tier: 'mandatory',
    description: 'No linting errors',
    validationRule: 'errorCount === 0',
  },
  {
    type: 'traceability',
    tier: 'mandatory',
    description: 'Requirements traceability verified',
  },
  {
    type: 'changelog',
    tier: 'mandatory',
    description: 'CHANGELOG.md updated',
  },
  // Recommended evidence
  {
    type: 'coverage-report',
    tier: 'recommended',
    description: 'Code coverage above threshold (80%)',
    validationRule: 'coverage >= 80',
  },
  {
    type: 'security-scan',
    tier: 'recommended',
    description: 'No high/critical security vulnerabilities',
    validationRule: 'highSeverityCount === 0 && criticalCount === 0',
  },
  {
    type: 'review-approval',
    tier: 'recommended',
    description: 'Code review approved by at least one reviewer',
  },
  // Optional evidence
  {
    type: 'performance-test',
    tier: 'optional',
    description: 'Performance tests within acceptable range',
  },
  {
    type: 'documentation',
    tier: 'optional',
    description: 'API documentation updated',
  },
  {
    type: 'adr',
    tier: 'optional',
    description: 'Architecture decision recorded if applicable',
  },
]);

/**
 * Default evidence requirements for all phases
 */
export const DEFAULT_PHASE_EVIDENCE: readonly PhaseEvidenceConfig[] = Object.freeze([
  {
    phase: 1, // Requirements
    requirements: [
      { type: 'documentation', tier: 'mandatory', description: 'Requirements document in EARS format' },
      { type: 'review-approval', tier: 'recommended', description: 'Requirements reviewed' },
    ],
  },
  {
    phase: 2, // Design
    requirements: [
      { type: 'documentation', tier: 'mandatory', description: 'Design document in C4 format' },
      { type: 'traceability', tier: 'mandatory', description: 'REQ to DES traceability' },
      { type: 'adr', tier: 'recommended', description: 'Key design decisions documented' },
    ],
  },
  {
    phase: 3, // Task Breakdown
    requirements: [
      { type: 'documentation', tier: 'mandatory', description: 'Task breakdown document' },
      { type: 'traceability', tier: 'mandatory', description: 'DES to TSK traceability' },
    ],
  },
  {
    phase: 4, // Implementation
    requirements: [
      { type: 'test-result', tier: 'mandatory', description: 'Unit tests pass' },
      { type: 'lint-result', tier: 'mandatory', description: 'No linting errors' },
    ],
  },
  {
    phase: 5, // Completion
    requirements: PHASE5_EVIDENCE_REQUIREMENTS,
  },
]);

// Auto-increment for evidence IDs
let evidenceCounter = 0;

/**
 * Create an evidence record
 */
export function createEvidenceRecord(params: {
  id?: string;
  type: EvidenceType;
  tier: EvidenceTier;
  description: string;
  artifact?: string;
  timestamp?: number;
  validator?: string;
  metadata?: Record<string, unknown>;
}): EvidenceRecord {
  const id = params.id ?? `EVD-${String(++evidenceCounter).padStart(3, '0')}`;

  return Object.freeze({
    id,
    type: params.type,
    tier: params.tier,
    description: params.description,
    artifact: params.artifact,
    timestamp: params.timestamp ?? Date.now(),
    validator: params.validator,
    metadata: params.metadata ? Object.freeze({ ...params.metadata }) : undefined,
  });
}

/**
 * Reset evidence counter (for testing)
 */
export function resetEvidenceCounter(): void {
  evidenceCounter = 0;
}

/**
 * Get evidence requirements for a specific phase
 */
export function getPhaseRequirements(
  phase: number,
  config: readonly PhaseEvidenceConfig[] = DEFAULT_PHASE_EVIDENCE
): readonly EvidenceRequirement[] {
  const phaseConfig = config.find(c => c.phase === phase);
  return phaseConfig?.requirements ?? [];
}

/**
 * Check if an evidence record satisfies a requirement
 */
export function satisfiesRequirement(
  record: EvidenceRecord,
  requirement: EvidenceRequirement
): boolean {
  // Type must match
  if (record.type !== requirement.type) {
    return false;
  }

  // Tier must be same or higher
  const tierOrder: Record<EvidenceTier, number> = {
    mandatory: 3,
    recommended: 2,
    optional: 1,
  };

  return tierOrder[record.tier] >= tierOrder[requirement.tier];
}
