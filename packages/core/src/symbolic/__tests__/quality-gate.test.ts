/**
 * Quality Gate Validator Tests
 *
 * Tests for TSK-SYMB-019: Quality Gate validation
 *
 * @module quality-gate.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  QualityGateValidator,
  createComponentValidation,
  type TraceabilityCoverage,
  type ComponentValidation,
  type QualityGateConfig,
} from '../quality-gate.js';

describe('QualityGateValidator', () => {
  let validator: QualityGateValidator;
  let fullTraceability: TraceabilityCoverage[];
  let fullComponents: ComponentValidation;

  beforeEach(() => {
    validator = new QualityGateValidator();

    // Create full traceability for 27 requirements
    fullTraceability = [
      // Semantic Filter requirements
      { requirementId: 'REQ-SF-001', designIds: ['DES-001'], taskIds: ['TSK-001'], testIds: ['TEST-001'], coveragePercent: 100 },
      { requirementId: 'REQ-SF-002', designIds: ['DES-001'], taskIds: ['TSK-001'], testIds: ['TEST-002'], coveragePercent: 100 },
      { requirementId: 'REQ-SF-003', designIds: ['DES-001'], taskIds: ['TSK-002'], testIds: ['TEST-003'], coveragePercent: 100 },
      // Formal Verification requirements
      { requirementId: 'REQ-FV-001', designIds: ['DES-002'], taskIds: ['TSK-003'], testIds: ['TEST-004'], coveragePercent: 100 },
      { requirementId: 'REQ-FV-002', designIds: ['DES-002'], taskIds: ['TSK-003'], testIds: ['TEST-005'], coveragePercent: 100 },
      { requirementId: 'REQ-FV-003', designIds: ['DES-002'], taskIds: ['TSK-004'], testIds: ['TEST-006'], coveragePercent: 100 },
      { requirementId: 'REQ-FV-004', designIds: ['DES-002'], taskIds: ['TSK-004'], testIds: ['TEST-007'], coveragePercent: 100 },
      { requirementId: 'REQ-FV-005', designIds: ['DES-002'], taskIds: ['TSK-005'], testIds: ['TEST-008'], coveragePercent: 100 },
      // Constitution requirements
      { requirementId: 'REQ-CONST-001', designIds: ['DES-003'], taskIds: ['TSK-006'], testIds: ['TEST-009'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-002', designIds: ['DES-003'], taskIds: ['TSK-006'], testIds: ['TEST-010'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-003', designIds: ['DES-003'], taskIds: ['TSK-007'], testIds: ['TEST-011'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-004', designIds: ['DES-003'], taskIds: ['TSK-007'], testIds: ['TEST-012'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-005', designIds: ['DES-003'], taskIds: ['TSK-008'], testIds: ['TEST-013'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-006', designIds: ['DES-003'], taskIds: ['TSK-008'], testIds: ['TEST-014'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-007', designIds: ['DES-003'], taskIds: ['TSK-009'], testIds: ['TEST-015'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-008', designIds: ['DES-003'], taskIds: ['TSK-009'], testIds: ['TEST-016'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-009', designIds: ['DES-003'], taskIds: ['TSK-010'], testIds: ['TEST-017'], coveragePercent: 100 },
      { requirementId: 'REQ-CONST-010', designIds: ['DES-003'], taskIds: ['TSK-010'], testIds: ['TEST-018'], coveragePercent: 100 },
      // Routing requirements
      { requirementId: 'REQ-ROUTE-001', designIds: ['DES-004'], taskIds: ['TSK-011'], testIds: ['TEST-019'], coveragePercent: 100 },
      { requirementId: 'REQ-ROUTE-002', designIds: ['DES-004'], taskIds: ['TSK-011'], testIds: ['TEST-020'], coveragePercent: 100 },
      { requirementId: 'REQ-ROUTE-003', designIds: ['DES-004'], taskIds: ['TSK-012'], testIds: ['TEST-021'], coveragePercent: 100 },
      // Non-functional requirements
      { requirementId: 'REQ-NFR-001', designIds: ['DES-005'], taskIds: ['TSK-013'], testIds: ['TEST-022'], coveragePercent: 100 },
      { requirementId: 'REQ-NFR-002', designIds: ['DES-005'], taskIds: ['TSK-013'], testIds: ['TEST-023'], coveragePercent: 100 },
      { requirementId: 'REQ-NFR-003', designIds: ['DES-005'], taskIds: ['TSK-014'], testIds: ['TEST-024'], coveragePercent: 100 },
      { requirementId: 'REQ-NFR-004', designIds: ['DES-005'], taskIds: ['TSK-014'], testIds: ['TEST-025'], coveragePercent: 100 },
      { requirementId: 'REQ-NFR-005', designIds: ['DES-005'], taskIds: ['TSK-015'], testIds: ['TEST-026'], coveragePercent: 100 },
      { requirementId: 'REQ-NFR-006', designIds: ['DES-005'], taskIds: ['TSK-015'], testIds: ['TEST-027'], coveragePercent: 100 },
    ];

    // Create fully compliant component validation
    fullComponents = createComponentValidation({
      performanceBudgetDefined: true,
      extensibleConfigDefined: true,
      explanationGeneratorDefined: true,
      securityMaskingDefined: true,
      auditLoggingDefined: true,
      libraryFirstCompliant: true,
      cliInterfaceDefined: true,
      testFirstCompliant: true,
      earsFormatCompliant: true,
      traceabilityCompliant: true,
      projectMemoryCompliant: true,
      designPatternsDocumented: true,
      adrCompliant: true,
      qualityGatesConfigured: true,
    });
  });

  describe('validate', () => {
    it('should pass when all criteria are met', () => {
      const result = validator.validate(fullTraceability, fullComponents);

      expect(result.passed).toBe(true);
      expect(result.gateName).toBe('DES-SYMB-001 Implementation Gate');
      expect(result.phase).toBe('design');
      expect(result.summary.blockerCount).toBe(0);
      expect(result.summary.criticalCount).toBe(0);
    });

    it('should fail when design coverage is incomplete', () => {
      // Remove design IDs from some requirements
      const incompleteTraceability = fullTraceability.map((t, i) =>
        i < 3 ? { ...t, designIds: [] } : t
      );

      const result = validator.validate(incompleteTraceability, fullComponents);

      expect(result.passed).toBe(false);
      expect(result.summary.blockerCount).toBeGreaterThan(0);
      
      const designCheck = result.checks.find(c => c.checkId === 'QG-TRACE-001');
      expect(designCheck?.passed).toBe(false);
    });

    it('should fail when performance budget is not defined', () => {
      const incompleteComponents = createComponentValidation({
        ...fullComponents,
        performanceBudgetDefined: false,
      });

      const result = validator.validate(fullTraceability, incompleteComponents);

      expect(result.passed).toBe(false);
      
      const perfCheck = result.checks.find(c => c.checkId === 'QG-NFR-001');
      expect(perfCheck?.passed).toBe(false);
      expect(perfCheck?.severity).toBe('blocker');
    });

    it('should fail when audit logging is not defined', () => {
      const incompleteComponents = createComponentValidation({
        ...fullComponents,
        auditLoggingDefined: false,
      });

      const result = validator.validate(fullTraceability, incompleteComponents);

      expect(result.passed).toBe(false);
      
      const auditCheck = result.checks.find(c => c.checkId === 'QG-SEC-002');
      expect(auditCheck?.passed).toBe(false);
      expect(auditCheck?.severity).toBe('blocker');
    });

    it('should check all 9 Constitution articles', () => {
      const result = validator.validate(fullTraceability, fullComponents);

      const constitutionChecks = result.checks.filter(c => c.category === 'constitution');
      expect(constitutionChecks.length).toBe(9);

      // All should pass
      for (const check of constitutionChecks) {
        expect(check.passed).toBe(true);
      }
    });

    it('should fail for non-compliant Constitution articles', () => {
      const incompleteComponents = createComponentValidation({
        ...fullComponents,
        traceabilityCompliant: false, // Article V
      });

      const result = validator.validate(fullTraceability, incompleteComponents);

      expect(result.passed).toBe(false);
      
      const articleVCheck = result.checks.find(c => c.checkId === 'QG-CONST-V');
      expect(articleVCheck?.passed).toBe(false);
      expect(articleVCheck?.severity).toBe('blocker'); // Article V is blocker
    });

    it('should include explanation with reasoning', () => {
      const result = validator.validate(fullTraceability, fullComponents);

      expect(result.explanation).toBeDefined();
      expect(result.explanation.summary).toContain('PASSED');
      expect(result.explanation.reasoning.length).toBeGreaterThan(0);
      expect(result.explanation.evidence.length).toBeGreaterThan(0);
    });
  });

  describe('custom configuration', () => {
    it('should use custom min design coverage', () => {
      const customConfig: Partial<QualityGateConfig> = {
        minDesignCoverage: 90,
      };
      const customValidator = new QualityGateValidator(customConfig);

      // Remove design from ~5% of requirements (2 out of 27)
      const partialTraceability = fullTraceability.map((t, i) =>
        i < 2 ? { ...t, designIds: [] } : t
      );

      const result = customValidator.validate(partialTraceability, fullComponents);

      // 25/27 = 92.6% > 90%, should pass
      const designCheck = result.checks.find(c => c.checkId === 'QG-TRACE-001');
      expect(designCheck?.passed).toBe(true);
    });
  });

  describe('generateApprovalReport', () => {
    it('should generate markdown report for passed gate', () => {
      const result = validator.validate(fullTraceability, fullComponents);
      const report = validator.generateApprovalReport(result);

      expect(report).toContain('# Quality Gate Approval Report');
      expect(report).toContain('✅ PASSED');
      expect(report).toContain('## Summary');
      expect(report).toContain('## Traceability Checks');
      expect(report).toContain('## Non-Functional Checks');
      expect(report).toContain('## Security & Audit Checks');
      expect(report).toContain('## Constitution Checks');
      expect(report).toContain('## Approval Record');
    });

    it('should generate markdown report for failed gate', () => {
      const incompleteComponents = createComponentValidation({
        ...fullComponents,
        performanceBudgetDefined: false,
        auditLoggingDefined: false,
      });

      const result = validator.validate(fullTraceability, incompleteComponents);
      const report = validator.generateApprovalReport(result);

      expect(report).toContain('❌ FAILED');
      expect(report).toContain('🚫'); // Blocker icon
    });
  });

  describe('createComponentValidation', () => {
    it('should create validation with defaults', () => {
      const validation = createComponentValidation({});

      expect(validation.performanceBudgetDefined).toBe(false);
      expect(validation.auditLoggingDefined).toBe(false);
      expect(validation.libraryFirstCompliant).toBe(false);
    });

    it('should create validation with partial overrides', () => {
      const validation = createComponentValidation({
        performanceBudgetDefined: true,
        auditLoggingDefined: true,
      });

      expect(validation.performanceBudgetDefined).toBe(true);
      expect(validation.auditLoggingDefined).toBe(true);
      expect(validation.extensibleConfigDefined).toBe(false);
    });
  });

  describe('traceability checks', () => {
    it('should detect coverage gaps', () => {
      // Create traceability with gaps
      const gappyTraceability = fullTraceability.map((t, i) =>
        i % 3 === 0 ? { ...t, coveragePercent: 50 } : t
      );

      const result = validator.validate(gappyTraceability, fullComponents);

      const gapCheck = result.checks.find(c => c.checkId === 'QG-TRACE-003');
      expect(gapCheck?.passed).toBe(false);
      expect(gapCheck?.message).toContain('coverage gaps');
    });

    it('should report task coverage', () => {
      const result = validator.validate(fullTraceability, fullComponents);

      const taskCheck = result.checks.find(c => c.checkId === 'QG-TRACE-002');
      expect(taskCheck?.passed).toBe(true);
      expect(taskCheck?.message).toContain('100');
    });
  });

  describe('edge cases', () => {
    it('should handle empty traceability', () => {
      const result = validator.validate([], fullComponents);

      expect(result.checks.length).toBeGreaterThan(0);
      // Design coverage should be 0% which fails
      const designCheck = result.checks.find(c => c.checkId === 'QG-TRACE-001');
      expect(designCheck?.passed).toBe(false);
    });

    it('should handle partial component validation', () => {
      const partialComponents = createComponentValidation({
        performanceBudgetDefined: true,
        auditLoggingDefined: true,
        // Everything else defaults to false
      });

      const result = validator.validate(fullTraceability, partialComponents);

      // Should fail due to missing components
      expect(result.passed).toBe(false);
      expect(result.summary.criticalCount).toBeGreaterThan(0);
    });
  });
});
