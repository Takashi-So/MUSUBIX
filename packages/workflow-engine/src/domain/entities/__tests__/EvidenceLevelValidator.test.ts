/**
 * EvidenceLevelValidator Tests
 *
 * @see TSK-FR-019〜022 - EvidenceLevelValidator
 */
import { describe, it, expect, beforeEach, vi } from 'vitest';

import {
  type EvidenceRecord,
  type EvidenceRequirement,
  type EvidenceTier,
  type EvidenceType,
  type PhaseEvidenceConfig,
  createEvidenceRecord,
  resetEvidenceCounter,
  getPhaseRequirements,
  satisfiesRequirement,
  PHASE5_EVIDENCE_REQUIREMENTS,
  DEFAULT_PHASE_EVIDENCE,
} from '../../value-objects/EvidenceLevel.js';

import {
  type IEvidenceLevelValidator,
  EvidenceLevelValidator,
  createEvidenceLevelValidator,
} from '../EvidenceLevelValidator.js';

describe('EvidenceLevelValidator', () => {
  beforeEach(() => {
    resetEvidenceCounter();
  });

  // ============================================================
  // Type definitions tests
  // ============================================================
  describe('createEvidenceRecord', () => {
    it('should create an evidence record with auto-generated ID', () => {
      const record = createEvidenceRecord({
        type: 'test-result',
        tier: 'mandatory',
        description: 'All tests pass',
      });

      expect(record.id).toBe('EVD-001');
      expect(record.type).toBe('test-result');
      expect(record.tier).toBe('mandatory');
      expect(record.description).toBe('All tests pass');
      expect(record.timestamp).toBeDefined();
    });

    it('should allow custom ID', () => {
      const record = createEvidenceRecord({
        id: 'CUSTOM-EVD-001',
        type: 'coverage-report',
        tier: 'recommended',
        description: 'Coverage report',
      });

      expect(record.id).toBe('CUSTOM-EVD-001');
    });

    it('should be immutable', () => {
      const record = createEvidenceRecord({
        type: 'lint-result',
        tier: 'mandatory',
        description: 'No linting errors',
      });

      expect(() => {
        (record as any).type = 'security-scan';
      }).toThrow();
    });

    it('should include artifact and metadata', () => {
      const record = createEvidenceRecord({
        type: 'security-scan',
        tier: 'recommended',
        description: 'Security scan results',
        artifact: 'reports/security-scan.json',
        validator: 'snyk',
        metadata: { vulnerabilities: 0 },
      });

      expect(record.artifact).toBe('reports/security-scan.json');
      expect(record.validator).toBe('snyk');
      expect(record.metadata?.vulnerabilities).toBe(0);
    });
  });

  describe('PHASE5_EVIDENCE_REQUIREMENTS', () => {
    it('should have mandatory evidence requirements', () => {
      const mandatory = PHASE5_EVIDENCE_REQUIREMENTS.filter(r => r.tier === 'mandatory');
      expect(mandatory.length).toBeGreaterThanOrEqual(3);
      expect(mandatory.map(r => r.type)).toContain('test-result');
      expect(mandatory.map(r => r.type)).toContain('lint-result');
      expect(mandatory.map(r => r.type)).toContain('traceability');
    });

    it('should have recommended evidence requirements', () => {
      const recommended = PHASE5_EVIDENCE_REQUIREMENTS.filter(r => r.tier === 'recommended');
      expect(recommended.length).toBeGreaterThanOrEqual(2);
      expect(recommended.map(r => r.type)).toContain('coverage-report');
      expect(recommended.map(r => r.type)).toContain('security-scan');
    });
  });

  describe('getPhaseRequirements', () => {
    it('should return requirements for phase 5', () => {
      const requirements = getPhaseRequirements(5);
      expect(requirements).toBe(PHASE5_EVIDENCE_REQUIREMENTS);
    });

    it('should return requirements for phase 1', () => {
      const requirements = getPhaseRequirements(1);
      expect(requirements.some(r => r.type === 'documentation')).toBe(true);
    });

    it('should return empty array for unknown phase', () => {
      const requirements = getPhaseRequirements(99);
      expect(requirements).toEqual([]);
    });
  });

  describe('satisfiesRequirement', () => {
    it('should return true for matching type and tier', () => {
      const record = createEvidenceRecord({
        type: 'test-result',
        tier: 'mandatory',
        description: 'Tests pass',
      });
      const requirement: EvidenceRequirement = {
        type: 'test-result',
        tier: 'mandatory',
        description: 'All tests must pass',
      };

      expect(satisfiesRequirement(record, requirement)).toBe(true);
    });

    it('should return false for mismatching type', () => {
      const record = createEvidenceRecord({
        type: 'lint-result',
        tier: 'mandatory',
        description: 'Lint pass',
      });
      const requirement: EvidenceRequirement = {
        type: 'test-result',
        tier: 'mandatory',
        description: 'Tests must pass',
      };

      expect(satisfiesRequirement(record, requirement)).toBe(false);
    });

    it('should return true for higher tier record', () => {
      const record = createEvidenceRecord({
        type: 'coverage-report',
        tier: 'mandatory',  // Higher than required
        description: 'Coverage',
      });
      const requirement: EvidenceRequirement = {
        type: 'coverage-report',
        tier: 'recommended',
        description: 'Coverage report',
      };

      expect(satisfiesRequirement(record, requirement)).toBe(true);
    });
  });

  // ============================================================
  // EvidenceLevelValidator tests
  // ============================================================
  describe('validateEvidence', () => {
    it('should validate when all mandatory evidence is present', () => {
      const validator = createEvidenceLevelValidator();

      const evidence: EvidenceRecord[] = [
        createEvidenceRecord({ type: 'test-result', tier: 'mandatory', description: 'Tests pass' }),
        createEvidenceRecord({ type: 'lint-result', tier: 'mandatory', description: 'Lint pass' }),
        createEvidenceRecord({ type: 'traceability', tier: 'mandatory', description: 'Traced' }),
        createEvidenceRecord({ type: 'changelog', tier: 'mandatory', description: 'Changelog updated' }),
      ];

      const result = validator.validateEvidence(5, evidence);

      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
      expect(result.missingMandatory).toHaveLength(0);
      expect(result.completeness.mandatory).toBe(100);
    });

    it('should fail when mandatory evidence is missing', () => {
      const validator = createEvidenceLevelValidator();

      const evidence: EvidenceRecord[] = [
        createEvidenceRecord({ type: 'test-result', tier: 'mandatory', description: 'Tests pass' }),
        // Missing: lint-result, traceability, changelog
      ];

      const result = validator.validateEvidence(5, evidence);

      expect(result.valid).toBe(false);
      expect(result.errors.length).toBeGreaterThan(0);
      expect(result.missingMandatory.length).toBeGreaterThan(0);
      expect(result.completeness.mandatory).toBeLessThan(100);
    });

    it('should warn when recommended evidence is missing', () => {
      const validator = createEvidenceLevelValidator();

      const evidence: EvidenceRecord[] = [
        createEvidenceRecord({ type: 'test-result', tier: 'mandatory', description: 'Tests pass' }),
        createEvidenceRecord({ type: 'lint-result', tier: 'mandatory', description: 'Lint pass' }),
        createEvidenceRecord({ type: 'traceability', tier: 'mandatory', description: 'Traced' }),
        createEvidenceRecord({ type: 'changelog', tier: 'mandatory', description: 'Changelog updated' }),
        // Missing: coverage-report, security-scan, review-approval
      ];

      const result = validator.validateEvidence(5, evidence);

      expect(result.valid).toBe(true);  // Still valid (mandatory met)
      expect(result.warnings.length).toBeGreaterThan(0);
      expect(result.missingRecommended.length).toBeGreaterThan(0);
      expect(result.completeness.recommended).toBeLessThan(100);
    });

    it('should calculate overall completeness', () => {
      const validator = createEvidenceLevelValidator();

      const evidence: EvidenceRecord[] = [
        createEvidenceRecord({ type: 'test-result', tier: 'mandatory', description: 'Tests pass' }),
        createEvidenceRecord({ type: 'lint-result', tier: 'mandatory', description: 'Lint pass' }),
        createEvidenceRecord({ type: 'traceability', tier: 'mandatory', description: 'Traced' }),
        createEvidenceRecord({ type: 'changelog', tier: 'mandatory', description: 'Changelog updated' }),
        createEvidenceRecord({ type: 'coverage-report', tier: 'recommended', description: 'Coverage' }),
      ];

      const result = validator.validateEvidence(5, evidence);

      expect(result.completeness.mandatory).toBe(100);
      expect(result.completeness.recommended).toBeGreaterThan(0);
      expect(result.completeness.overall).toBeGreaterThan(0);
    });
  });

  describe('getRequiredEvidence', () => {
    it('should return requirements for a phase', () => {
      const validator = createEvidenceLevelValidator();

      const requirements = validator.getRequiredEvidence(5);

      expect(requirements.length).toBeGreaterThan(0);
      expect(requirements.some(r => r.type === 'test-result')).toBe(true);
    });

    it('should filter by tier', () => {
      const validator = createEvidenceLevelValidator();

      const mandatory = validator.getRequiredEvidence(5, 'mandatory');
      const recommended = validator.getRequiredEvidence(5, 'recommended');

      expect(mandatory.every(r => r.tier === 'mandatory')).toBe(true);
      expect(recommended.every(r => r.tier === 'recommended')).toBe(true);
    });
  });

  describe('checkCompleteness', () => {
    it('should return 100% when all requirements met', () => {
      const validator = createEvidenceLevelValidator();

      const evidence: EvidenceRecord[] = [
        createEvidenceRecord({ type: 'test-result', tier: 'mandatory', description: 'Tests pass' }),
        createEvidenceRecord({ type: 'lint-result', tier: 'mandatory', description: 'Lint pass' }),
        createEvidenceRecord({ type: 'traceability', tier: 'mandatory', description: 'Traced' }),
        createEvidenceRecord({ type: 'changelog', tier: 'mandatory', description: 'Changelog updated' }),
        createEvidenceRecord({ type: 'coverage-report', tier: 'recommended', description: 'Coverage' }),
        createEvidenceRecord({ type: 'security-scan', tier: 'recommended', description: 'Security' }),
        createEvidenceRecord({ type: 'review-approval', tier: 'recommended', description: 'Approved' }),
      ];

      const completeness = validator.checkCompleteness(5, evidence);

      expect(completeness.mandatory).toBe(100);
      expect(completeness.recommended).toBe(100);
    });

    it('should return 0% when no evidence provided', () => {
      const validator = createEvidenceLevelValidator();

      const completeness = validator.checkCompleteness(5, []);

      expect(completeness.mandatory).toBe(0);
      expect(completeness.recommended).toBe(0);
      expect(completeness.overall).toBe(0);
    });

    it('should calculate partial completeness', () => {
      const validator = createEvidenceLevelValidator();

      const evidence: EvidenceRecord[] = [
        createEvidenceRecord({ type: 'test-result', tier: 'mandatory', description: 'Tests pass' }),
        createEvidenceRecord({ type: 'lint-result', tier: 'mandatory', description: 'Lint pass' }),
        // Missing: traceability, changelog (2 of 4 mandatory)
      ];

      const completeness = validator.checkCompleteness(5, evidence);

      expect(completeness.mandatory).toBe(50);  // 2/4 = 50%
    });
  });

  describe('addCustomRequirement', () => {
    it('should add custom requirement to a phase', () => {
      const validator = createEvidenceLevelValidator();

      validator.addCustomRequirement(5, {
        type: 'adr',
        tier: 'mandatory',
        description: 'ADR for this feature',
      });

      const requirements = validator.getRequiredEvidence(5, 'mandatory');
      expect(requirements.some(r => r.type === 'adr' && r.tier === 'mandatory')).toBe(true);
    });
  });

  describe('custom configuration', () => {
    it('should accept custom phase evidence config', () => {
      const customConfig: PhaseEvidenceConfig[] = [
        {
          phase: 5,
          requirements: [
            { type: 'test-result', tier: 'mandatory', description: 'Tests pass' },
            { type: 'documentation', tier: 'mandatory', description: 'Docs updated' },
          ],
        },
      ];

      const validator = createEvidenceLevelValidator(customConfig);

      const requirements = validator.getRequiredEvidence(5);
      expect(requirements).toHaveLength(2);
      expect(requirements.some(r => r.type === 'documentation')).toBe(true);
    });
  });
});
