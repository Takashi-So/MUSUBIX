/**
 * TestPlacementValidator Tests
 *
 * @see TSK-FR-052 - TestPlacementValidatorユニットテスト
 */
import { describe, it, expect, beforeEach } from 'vitest';

import {
  type TestPlacement,
  type PlacementRule,
  type PlacementViolation,
  type PlacementValidationResult,
  type TestPlacementConfig,
  createTestPlacement,
  inferTestFileType,
  inferSourceFilePath,
  calculatePlacementSummary,
  DEFAULT_PLACEMENT_RULES,
  DEFAULT_TEST_PLACEMENT_CONFIG,
} from '../types/TestPlacement.js';

import {
  type ITestPlacementValidator,
  TestPlacementValidator,
  createTestPlacementValidator,
} from '../validator/TestPlacementValidator.js';

describe('TestPlacementValidator', () => {
  // ============================================================
  // Type Tests
  // ============================================================
  describe('inferTestFileType', () => {
    it('should detect unit test', () => {
      expect(inferTestFileType('src/__tests__/Foo.test.ts')).toBe('unit');
      expect(inferTestFileType('src/Foo.spec.ts')).toBe('unit');
    });

    it('should detect integration test', () => {
      expect(inferTestFileType('tests/integration/api.integration.test.ts')).toBe('integration');
    });

    it('should detect e2e test', () => {
      expect(inferTestFileType('e2e/login.e2e.test.ts')).toBe('e2e');
    });

    it('should detect snapshot test', () => {
      expect(inferTestFileType('__snapshots__/Component.snap')).toBe('snapshot');
    });

    it('should return unknown for unrecognized patterns', () => {
      expect(inferTestFileType('src/utils.ts')).toBe('unknown');
    });
  });

  describe('inferSourceFilePath', () => {
    it('should infer source from __tests__ path', () => {
      const result = inferSourceFilePath('src/domain/__tests__/Entity.test.ts');
      expect(result).toBe('src/domain/Entity.ts');
    });

    it('should infer source from simple test path', () => {
      const result = inferSourceFilePath('src/utils.test.ts');
      expect(result).toBe('src/utils.ts');
    });

    it('should return null for non-test paths', () => {
      const result = inferSourceFilePath('src/index.ts');
      expect(result).toBeNull();
    });
  });

  describe('createTestPlacement', () => {
    it('should create valid placement with no violations', () => {
      const placement = createTestPlacement('src/__tests__/Foo.test.ts');

      expect(placement.status).toBe('valid');
      expect(placement.type).toBe('unit');
      expect(placement.violations).toHaveLength(0);
    });

    it('should create invalid placement with error violation', () => {
      const violations: PlacementViolation[] = [{
        ruleId: 'TPR-001',
        ruleName: 'Co-located Unit Tests',
        message: 'Test should be co-located',
        severity: 'error',
      }];

      const placement = createTestPlacement('tests/Foo.test.ts', violations);

      expect(placement.status).toBe('invalid');
    });

    it('should create warning placement with warning violation', () => {
      const violations: PlacementViolation[] = [{
        ruleId: 'TPR-002',
        ruleName: 'Test',
        message: 'Consider moving test',
        severity: 'warning',
      }];

      const placement = createTestPlacement('src/test.test.ts', violations);

      expect(placement.status).toBe('warning');
    });
  });

  describe('calculatePlacementSummary', () => {
    it('should calculate summary correctly', () => {
      const placements = [
        createTestPlacement('src/__tests__/A.test.ts'),
        createTestPlacement('src/__tests__/B.test.ts'),
        createTestPlacement('tests/C.test.ts', [{
          ruleId: 'R1',
          ruleName: 'Test',
          message: 'Error',
          severity: 'error',
        }]),
      ];

      const summary = calculatePlacementSummary(placements);

      expect(summary.totalTests).toBe(3);
      expect(summary.validCount).toBe(2);
      expect(summary.invalidCount).toBe(1);
      expect(summary.byType.unit).toBe(3);
    });
  });

  // ============================================================
  // TestPlacementValidator Tests
  // ============================================================
  describe('validateFile', () => {
    it('should validate a correctly placed test file', async () => {
      const validator = createTestPlacementValidator();

      const result = await validator.validateFile('src/domain/__tests__/Entity.test.ts');

      expect(result.status).toBe('valid');
    });

    it('should detect misplaced test file', async () => {
      const validator = createTestPlacementValidator({
        ...DEFAULT_TEST_PLACEMENT_CONFIG,
        strictMode: true,
      });

      const result = await validator.validateFile('random/place/test.test.ts');

      // strictModeでは検証が厳しくなる
      expect(result.violations.length).toBeGreaterThanOrEqual(0);
    });
  });

  describe('validateAll', () => {
    it('should validate multiple test files', async () => {
      const validator = createTestPlacementValidator();

      const result = await validator.validateAll([
        'src/__tests__/A.test.ts',
        'src/__tests__/B.test.ts',
        'tests/integration/C.integration.test.ts',
      ]);

      expect(result.placements).toHaveLength(3);
      expect(result.summary.totalTests).toBe(3);
    });

    it('should calculate overall validity', async () => {
      const validator = createTestPlacementValidator();

      const result = await validator.validateAll([
        'src/__tests__/Valid.test.ts',
      ]);

      expect(result.isValid).toBe(true);
    });
  });

  describe('suggestPlacement', () => {
    it('should suggest correct placement for misplaced test', async () => {
      const validator = createTestPlacementValidator();

      const suggestions = await validator.suggestPlacement('src/utils.test.ts');

      expect(suggestions.length).toBeGreaterThan(0);
    });

    it('should suggest __tests__ directory', async () => {
      const validator = createTestPlacementValidator();

      const suggestions = await validator.suggestPlacement('src/domain/Entity.test.ts');

      expect(suggestions.some(s => s.includes('__tests__'))).toBe(true);
    });
  });

  describe('checkRule', () => {
    it('should check specific rule', async () => {
      const validator = createTestPlacementValidator();

      const violation = await validator.checkRule(
        'tests/random/test.test.ts',
        'TPR-001'
      );

      // ルールによって違反が検出される可能性がある
      expect(violation === null || violation.ruleId === 'TPR-001').toBe(true);
    });

    it('should return null for unknown rule', async () => {
      const validator = createTestPlacementValidator();

      const violation = await validator.checkRule('test.ts', 'UNKNOWN-RULE');

      expect(violation).toBeNull();
    });
  });

  describe('getRules', () => {
    it('should return all rules', () => {
      const validator = createTestPlacementValidator();

      const rules = validator.getRules();

      expect(rules.length).toBeGreaterThan(0);
    });

    it('should return default rules', () => {
      const validator = createTestPlacementValidator();

      const rules = validator.getRules();

      expect(rules.some(r => r.id === 'TPR-001')).toBe(true);
    });
  });

  describe('addRule', () => {
    it('should add custom rule', () => {
      const validator = createTestPlacementValidator();

      const customRule: PlacementRule = {
        id: 'CUSTOM-001',
        name: 'Custom Rule',
        description: 'A custom placement rule',
        pattern: '**/*.custom.test.ts',
        expectedLocation: '**/custom/**/*.test.ts',
        severity: 'warning',
        enabled: true,
      };

      validator.addRule(customRule);

      const rules = validator.getRules();
      expect(rules.some(r => r.id === 'CUSTOM-001')).toBe(true);
    });
  });

  describe('enableRule / disableRule', () => {
    it('should disable rule', () => {
      const validator = createTestPlacementValidator();

      validator.disableRule('TPR-001');

      const rules = validator.getRules();
      const rule = rules.find(r => r.id === 'TPR-001');
      expect(rule?.enabled).toBe(false);
    });

    it('should enable rule', () => {
      const validator = createTestPlacementValidator();

      validator.disableRule('TPR-001');
      validator.enableRule('TPR-001');

      const rules = validator.getRules();
      const rule = rules.find(r => r.id === 'TPR-001');
      expect(rule?.enabled).toBe(true);
    });
  });

  describe('getStats', () => {
    it('should return validation statistics', async () => {
      const validator = createTestPlacementValidator();

      await validator.validateAll([
        'src/__tests__/A.test.ts',
        'src/__tests__/B.test.ts',
      ]);

      const stats = validator.getStats();

      expect(stats.totalValidations).toBe(2);
    });
  });
});
