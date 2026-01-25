/**
 * @fileoverview Tests for Quality Gate Integration
 * @traceability TSK-INT-005
 */

import { describe, it, expect } from 'vitest';
import {
  createQualityGateIntegration,
  createQualityGateCheckFromSkillOutput,
} from '../quality-gate-integration.js';
import type {
  VerificationResult,
  VerificationPhase,
} from '../quality-gate-types.js';

/**
 * Create a mock verification result for testing
 */
function createMockVerificationResult(
  mode: 'quick' | 'full',
  passed: boolean = true
): VerificationResult {
  const phases: VerificationPhase[] = mode === 'quick'
    ? ['build', 'type-check', 'lint']
    : ['build', 'type-check', 'lint', 'test', 'security', 'diff-review'];

  return {
    id: `VER-test-${Date.now()}`,
    timestamp: new Date().toISOString(),
    passed,
    mode,
    phases: phases.map(phase => ({
      phase,
      passed,
      durationMs: 1000,
      filesExamined: 10,
    })),
    totalDurationMs: phases.length * 1000,
    summary: {
      phasesPassed: passed ? phases.length : 0,
      phasesFailed: passed ? 0 : phases.length,
      totalErrors: passed ? 0 : 5,
      totalWarnings: 2,
      filesExamined: phases.length * 10,
    },
  };
}

describe('QualityGateIntegration', () => {
  describe('getCriteria', () => {
    it('should return default criteria for implementation phase', () => {
      const integration = createQualityGateIntegration();
      const criteria = integration.getCriteria('implementation');

      expect(criteria.workflowPhase).toBe('implementation');
      expect(criteria.requiredVerificationPhases).toContain('build');
      expect(criteria.requiredVerificationPhases).toContain('test');
      expect(criteria.maxErrors).toBe(0);
      expect(criteria.requireSecurityPass).toBe(true);
    });

    it('should return default criteria for requirements phase', () => {
      const integration = createQualityGateIntegration();
      const criteria = integration.getCriteria('requirements');

      expect(criteria.requiredVerificationPhases.length).toBe(0);
      expect(criteria.requireSecurityPass).toBe(false);
    });
  });

  describe('updateCriteria', () => {
    it('should update criteria for a phase', () => {
      const integration = createQualityGateIntegration();
      integration.updateCriteria('design', {
        maxWarnings: 5,
        requireDiffReview: true,
      });

      const criteria = integration.getCriteria('design');

      expect(criteria.maxWarnings).toBe(5);
      expect(criteria.requireDiffReview).toBe(true);
    });
  });

  describe('checkQualityGate', () => {
    it('should check quality gate with custom verification result', async () => {
      const integration = createQualityGateIntegration();
      const mockVerification = createMockVerificationResult('full', true);

      const result = await integration.checkQualityGate('implementation', mockVerification);

      expect(result.passed).toBe(true);
      expect(result.workflowPhase).toBe('implementation');
    });

    it('should fail quality gate with too many errors', async () => {
      const integration = createQualityGateIntegration();
      const mockVerification: VerificationResult = {
        id: 'VER-mock',
        timestamp: new Date().toISOString(),
        passed: false,
        mode: 'full',
        phases: [
          { phase: 'build', passed: false, durationMs: 1000, errors: [
            { message: 'Build error 1', severity: 'error' },
            { message: 'Build error 2', severity: 'error' },
          ]},
          { phase: 'type-check', passed: true, durationMs: 500 },
          { phase: 'lint', passed: true, durationMs: 300 },
          { phase: 'test', passed: true, durationMs: 5000 },
          { phase: 'security', passed: true, durationMs: 1000 },
          { phase: 'diff-review', passed: true, durationMs: 100 },
        ],
        totalDurationMs: 6800,
        summary: {
          phasesPassed: 5,
          phasesFailed: 1,
          totalErrors: 2,
          totalWarnings: 0,
          filesExamined: 30,
        },
      };

      const result = await integration.checkQualityGate('implementation', mockVerification);

      expect(result.passed).toBe(false);
      expect(result.failures.some(f => f.type === 'verification_phase')).toBe(true);
      expect(result.failures.some(f => f.type === 'error_count')).toBe(true);
    });

    it('should fail quality gate with missing security phase', async () => {
      const integration = createQualityGateIntegration();
      const mockVerification: VerificationResult = {
        id: 'VER-mock',
        timestamp: new Date().toISOString(),
        passed: true,
        mode: 'quick',
        phases: [
          { phase: 'build', passed: true, durationMs: 1000 },
          { phase: 'type-check', passed: true, durationMs: 500 },
          { phase: 'lint', passed: true, durationMs: 300 },
          { phase: 'test', passed: true, durationMs: 5000 },
          // No security phase
        ],
        totalDurationMs: 6800,
        summary: {
          phasesPassed: 4,
          phasesFailed: 0,
          totalErrors: 0,
          totalWarnings: 0,
          filesExamined: 30,
        },
      };

      const result = await integration.checkQualityGate('implementation', mockVerification);

      expect(result.passed).toBe(false);
      expect(result.failures.some(f => f.type === 'security')).toBe(true);
    });
  });

  describe('getVerificationHistory / getLastVerification', () => {
    it('should return empty history initially', () => {
      const integration = createQualityGateIntegration();
      expect(integration.getVerificationHistory().length).toBe(0);
      expect(integration.getLastVerification()).toBeUndefined();
    });
  });

  describe('formatResultAsMarkdown', () => {
    it('should format passing verification result', () => {
      const integration = createQualityGateIntegration();
      const result = createMockVerificationResult('quick', true);
      const markdown = integration.formatResultAsMarkdown(result);

      expect(markdown).toContain('Verification Result');
      expect(markdown).toContain('**Mode**: quick');
      expect(markdown).toContain('Summary');
      expect(markdown).toContain('Phase Results');
    });

    it('should format failing verification result', () => {
      const integration = createQualityGateIntegration();
      const failingResult: VerificationResult = {
        id: 'VER-fail',
        timestamp: new Date().toISOString(),
        passed: false,
        mode: 'full',
        phases: [
          { 
            phase: 'build', 
            passed: false, 
            durationMs: 1000,
            errors: [
              { message: 'Compilation failed', severity: 'error' },
            ],
          },
        ],
        totalDurationMs: 1000,
        summary: {
          phasesPassed: 0,
          phasesFailed: 1,
          totalErrors: 1,
          totalWarnings: 0,
          filesExamined: 10,
        },
      };

      const markdown = integration.formatResultAsMarkdown(failingResult);

      expect(markdown).toContain('❌');
      expect(markdown).toContain('FAILED');
      expect(markdown).toContain('Compilation failed');
    });
  });

  describe('formatQualityGateCheckAsMarkdown', () => {
    it('should format passing gate check', async () => {
      const integration = createQualityGateIntegration();
      const mockVerification = createMockVerificationResult('full', true);
      const check = await integration.checkQualityGate('requirements', mockVerification);
      const markdown = integration.formatQualityGateCheckAsMarkdown(check);

      expect(markdown).toContain('Quality Gate Check');
      expect(markdown).toContain('**Phase**: requirements');
      expect(markdown).toContain('PASSED');
      expect(markdown).toContain('All Checks Passed');
    });

    it('should format failing gate check', () => {
      const integration = createQualityGateIntegration();
      const check = {
        passed: false,
        workflowPhase: 'implementation' as const,
        criteria: {
          workflowPhase: 'implementation' as const,
          requiredVerificationPhases: ['build', 'test'] as VerificationPhase[],
          maxErrors: 0,
          maxWarnings: 10,
          minTestCoverage: -1,
          minLintScore: -1,
          requireSecurityPass: true,
          requireDiffReview: true,
        },
        failures: [
          {
            type: 'error_count' as const,
            message: 'Too many errors',
            expected: '0',
            actual: '5',
          },
        ],
        checkedAt: new Date().toISOString(),
      };

      const markdown = integration.formatQualityGateCheckAsMarkdown(check);

      expect(markdown).toContain('FAILED');
      expect(markdown).toContain('Failures');
      expect(markdown).toContain('Too many errors');
    });
  });
});

describe('createQualityGateCheckFromSkillOutput', () => {
  it('should create passing check from success output', () => {
    const output = '✅ All phases passed\n✅ Build successful\n✅ Tests passed';
    const check = createQualityGateCheckFromSkillOutput('implementation', output);

    expect(check.passed).toBe(true);
    expect(check.workflowPhase).toBe('implementation');
    expect(check.failures.length).toBe(0);
  });

  it('should create failing check from error output', () => {
    const output = '✅ Build successful\n❌ Tests failed\n3 errors found';
    const check = createQualityGateCheckFromSkillOutput('implementation', output);

    expect(check.passed).toBe(false);
    expect(check.failures.length).toBeGreaterThan(0);
  });
});
