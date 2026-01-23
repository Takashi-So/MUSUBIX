/**
 * EvidenceLevelValidator Entity
 *
 * Validates evidence levels for phase completion in the SDD workflow.
 * Ensures all mandatory evidence is present before allowing phase transition.
 *
 * @see TSK-FR-019〜022 - EvidenceLevelValidator
 * @see REQ-FR-120〜125 - EvidenceLevelValidator
 * @trace DES-MUSUBIX-FR-001 DES-WF-003
 */

import {
  type EvidenceRecord,
  type EvidenceRequirement,
  type EvidenceValidationResult,
  type EvidenceTier,
  type PhaseEvidenceConfig,
  DEFAULT_PHASE_EVIDENCE,
  satisfiesRequirement,
} from '../value-objects/EvidenceLevel.js';

/**
 * EvidenceLevelValidator Interface
 */
export interface IEvidenceLevelValidator {
  /** Validate evidence for a phase */
  validateEvidence(phase: number, evidence: readonly EvidenceRecord[]): EvidenceValidationResult;

  /** Get required evidence for a phase */
  getRequiredEvidence(phase: number, tier?: EvidenceTier): readonly EvidenceRequirement[];

  /** Check completeness percentage */
  checkCompleteness(phase: number, evidence: readonly EvidenceRecord[]): {
    readonly mandatory: number;
    readonly recommended: number;
    readonly overall: number;
  };

  /** Add custom requirement to a phase */
  addCustomRequirement(phase: number, requirement: EvidenceRequirement): void;
}

/**
 * EvidenceLevelValidator Implementation
 *
 * Manages and validates evidence requirements for SDD workflow phases.
 *
 * @example
 * ```typescript
 * const validator = createEvidenceLevelValidator();
 *
 * const evidence = [
 *   createEvidenceRecord({ type: 'test-result', tier: 'mandatory', description: 'All tests pass' }),
 *   createEvidenceRecord({ type: 'lint-result', tier: 'mandatory', description: 'No lint errors' }),
 * ];
 *
 * const result = validator.validateEvidence(5, evidence);
 * if (!result.valid) {
 *   console.log('Missing evidence:', result.missingMandatory);
 * }
 * ```
 */
export class EvidenceLevelValidator implements IEvidenceLevelValidator {
  private readonly phaseConfig: Map<number, EvidenceRequirement[]>;

  constructor(config?: readonly PhaseEvidenceConfig[]) {
    this.phaseConfig = new Map();

    // Initialize from config
    const initialConfig = config ?? DEFAULT_PHASE_EVIDENCE;
    for (const pc of initialConfig) {
      this.phaseConfig.set(pc.phase, [...pc.requirements]);
    }
  }

  /**
   * Validate evidence for a phase
   */
  validateEvidence(phase: number, evidence: readonly EvidenceRecord[]): EvidenceValidationResult {
    const requirements = this.phaseConfig.get(phase) ?? [];
    const errors: string[] = [];
    const warnings: string[] = [];
    const missingMandatory: EvidenceRequirement[] = [];
    const missingRecommended: EvidenceRequirement[] = [];

    // Check each requirement
    for (const requirement of requirements) {
      const satisfied = evidence.some(e => satisfiesRequirement(e, requirement));

      if (!satisfied) {
        if (requirement.tier === 'mandatory') {
          missingMandatory.push(requirement);
          errors.push(
            `Missing mandatory evidence: ${requirement.type} - ${requirement.description}`
          );
        } else if (requirement.tier === 'recommended') {
          missingRecommended.push(requirement);
          warnings.push(
            `Missing recommended evidence: ${requirement.type} - ${requirement.description}`
          );
        }
      }
    }

    // Calculate completeness
    const completeness = this.calculateCompleteness(requirements, evidence);

    return Object.freeze({
      valid: missingMandatory.length === 0,
      errors: Object.freeze(errors),
      warnings: Object.freeze(warnings),
      missingMandatory: Object.freeze(missingMandatory),
      missingRecommended: Object.freeze(missingRecommended),
      completeness: Object.freeze(completeness),
    });
  }

  /**
   * Get required evidence for a phase
   */
  getRequiredEvidence(phase: number, tier?: EvidenceTier): readonly EvidenceRequirement[] {
    const requirements = this.phaseConfig.get(phase) ?? [];

    if (tier) {
      return Object.freeze(requirements.filter(r => r.tier === tier));
    }

    return Object.freeze([...requirements]);
  }

  /**
   * Check completeness percentage
   */
  checkCompleteness(phase: number, evidence: readonly EvidenceRecord[]): {
    readonly mandatory: number;
    readonly recommended: number;
    readonly overall: number;
  } {
    const requirements = this.phaseConfig.get(phase) ?? [];
    return Object.freeze(this.calculateCompleteness(requirements, evidence));
  }

  /**
   * Add custom requirement to a phase
   */
  addCustomRequirement(phase: number, requirement: EvidenceRequirement): void {
    const existing = this.phaseConfig.get(phase) ?? [];
    existing.push(requirement);
    this.phaseConfig.set(phase, existing);
  }

  // Private helpers

  private calculateCompleteness(
    requirements: readonly EvidenceRequirement[],
    evidence: readonly EvidenceRecord[]
  ): {
    mandatory: number;
    recommended: number;
    overall: number;
  } {
    const mandatory = requirements.filter(r => r.tier === 'mandatory');
    const recommended = requirements.filter(r => r.tier === 'recommended');
    const all = requirements.filter(r => r.tier !== 'optional');

    const mandatorySatisfied = mandatory.filter(req =>
      evidence.some(e => satisfiesRequirement(e, req))
    ).length;

    const recommendedSatisfied = recommended.filter(req =>
      evidence.some(e => satisfiesRequirement(e, req))
    ).length;

    const allSatisfied = all.filter(req =>
      evidence.some(e => satisfiesRequirement(e, req))
    ).length;

    return {
      mandatory: mandatory.length > 0 ? Math.round((mandatorySatisfied / mandatory.length) * 100) : 100,
      recommended: recommended.length > 0 ? Math.round((recommendedSatisfied / recommended.length) * 100) : 100,
      overall: all.length > 0 ? Math.round((allSatisfied / all.length) * 100) : 100,
    };
  }
}

/**
 * Create an EvidenceLevelValidator instance
 *
 * @param config - Optional custom phase evidence configuration
 * @returns IEvidenceLevelValidator instance
 */
export function createEvidenceLevelValidator(
  config?: readonly PhaseEvidenceConfig[]
): IEvidenceLevelValidator {
  return new EvidenceLevelValidator(config);
}
