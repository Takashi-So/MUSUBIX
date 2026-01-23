/**
 * BalanceRuleEngine Tests
 *
 * @see TSK-FR-032 - BalanceRuleEngineユニットテスト
 */
import { describe, it, expect, beforeEach } from 'vitest';

import {
  type BalanceChange,
  type BalanceConfig,
  type BalanceChangeType,
  createBalanceChange,
  getChangeCategory,
  isCounted,
  getTotalLines,
  getWeightedLines,
  CHANGE_TYPE_CATEGORIES,
  DEFAULT_BALANCE_CONFIG,
} from '../types.js';

import {
  type IBalanceRuleEngine,
  BalanceRuleEngine,
  createBalanceRuleEngine,
} from '../BalanceRuleEngine.js';

describe('BalanceRuleEngine', () => {
  // ============================================================
  // Value Object Tests
  // ============================================================
  describe('Balance Types', () => {
    describe('CHANGE_TYPE_CATEGORIES', () => {
      it('should categorize feature, bugfix, test, refactor as counted', () => {
        expect(CHANGE_TYPE_CATEGORIES.feature).toBe('counted');
        expect(CHANGE_TYPE_CATEGORIES.bugfix).toBe('counted');
        expect(CHANGE_TYPE_CATEGORIES.test).toBe('counted');
        expect(CHANGE_TYPE_CATEGORIES.refactor).toBe('counted');
      });

      it('should categorize config, build, ci, docs, style, chore as non-counted', () => {
        expect(CHANGE_TYPE_CATEGORIES.config).toBe('non-counted');
        expect(CHANGE_TYPE_CATEGORIES.build).toBe('non-counted');
        expect(CHANGE_TYPE_CATEGORIES.ci).toBe('non-counted');
        expect(CHANGE_TYPE_CATEGORIES.docs).toBe('non-counted');
        expect(CHANGE_TYPE_CATEGORIES.style).toBe('non-counted');
        expect(CHANGE_TYPE_CATEGORIES.chore).toBe('non-counted');
      });
    });

    describe('isCounted', () => {
      it('should return true for counted types', () => {
        expect(isCounted('feature')).toBe(true);
        expect(isCounted('bugfix')).toBe(true);
        expect(isCounted('test')).toBe(true);
        expect(isCounted('refactor')).toBe(true);
      });

      it('should return false for non-counted types', () => {
        expect(isCounted('config')).toBe(false);
        expect(isCounted('build')).toBe(false);
        expect(isCounted('docs')).toBe(false);
      });
    });

    describe('createBalanceChange', () => {
      it('should create a balance change with auto-generated ID', () => {
        const change = createBalanceChange({
          type: 'feature',
          file: 'src/index.ts',
          linesAdded: 50,
          linesRemoved: 10,
        });

        expect(change.id).toMatch(/^CHG-/);
        expect(change.type).toBe('feature');
        expect(change.category).toBe('counted');
        expect(change.file).toBe('src/index.ts');
        expect(change.linesAdded).toBe(50);
        expect(change.linesRemoved).toBe(10);
      });

      it('should be immutable', () => {
        const change = createBalanceChange({
          type: 'config',
          file: 'config.json',
          linesAdded: 5,
          linesRemoved: 2,
        });

        expect(() => {
          (change as any).type = 'feature';
        }).toThrow();
      });
    });

    describe('getTotalLines', () => {
      it('should return sum of added and removed lines', () => {
        const change = createBalanceChange({
          type: 'feature',
          file: 'test.ts',
          linesAdded: 100,
          linesRemoved: 30,
        });

        expect(getTotalLines(change)).toBe(130);
      });
    });

    describe('getWeightedLines', () => {
      it('should apply weight for feature (1.0)', () => {
        const change = createBalanceChange({
          type: 'feature',
          file: 'test.ts',
          linesAdded: 100,
          linesRemoved: 0,
        });

        expect(getWeightedLines(change)).toBe(100);
      });

      it('should apply weight for test (0.5)', () => {
        const change = createBalanceChange({
          type: 'test',
          file: 'test.spec.ts',
          linesAdded: 100,
          linesRemoved: 0,
        });

        expect(getWeightedLines(change)).toBe(50);
      });

      it('should apply weight for config (0)', () => {
        const change = createBalanceChange({
          type: 'config',
          file: 'config.json',
          linesAdded: 100,
          linesRemoved: 0,
        });

        expect(getWeightedLines(change)).toBe(0);
      });
    });
  });

  // ============================================================
  // BalanceRuleEngine Tests
  // ============================================================
  describe('evaluateBalance', () => {
    it('should pass when all changes are counted', async () => {
      const engine = createBalanceRuleEngine();
      engine.addChange(createBalanceChange({
        type: 'feature',
        file: 'src/feature.ts',
        linesAdded: 100,
        linesRemoved: 0,
      }));

      const result = await engine.evaluateBalance();

      expect(result.passed).toBe(true);
      expect(result.metrics.ratio).toBe(0); // 0% non-counted
    });

    it('should pass when non-counted is within threshold', async () => {
      const engine = createBalanceRuleEngine();
      // 90% counted
      engine.addChange(createBalanceChange({
        type: 'feature',
        file: 'src/feature.ts',
        linesAdded: 90,
        linesRemoved: 0,
      }));
      // 10% non-counted (at threshold)
      engine.addChange(createBalanceChange({
        type: 'config',
        file: 'config.json',
        linesAdded: 10,
        linesRemoved: 0,
      }));

      const result = await engine.evaluateBalance();

      expect(result.passed).toBe(true);
      expect(result.metrics.ratio).toBe(0.1); // 10% non-counted
    });

    it('should fail when non-counted exceeds threshold', async () => {
      const engine = createBalanceRuleEngine();
      // 80% counted
      engine.addChange(createBalanceChange({
        type: 'feature',
        file: 'src/feature.ts',
        linesAdded: 80,
        linesRemoved: 0,
      }));
      // 20% non-counted (exceeds 10%)
      engine.addChange(createBalanceChange({
        type: 'config',
        file: 'config.json',
        linesAdded: 20,
        linesRemoved: 0,
      }));

      const result = await engine.evaluateBalance();

      expect(result.passed).toBe(false);
      expect(result.metrics.ratio).toBe(0.2); // 20% non-counted
      expect(result.metrics.exceedsThreshold).toBe(true);
    });

    it('should pass with empty changes', async () => {
      const engine = createBalanceRuleEngine();

      const result = await engine.evaluateBalance();

      expect(result.passed).toBe(true);
      expect(result.metrics.totalChanges).toBe(0);
    });
  });

  describe('getStats', () => {
    it('should return correct statistics', async () => {
      const engine = createBalanceRuleEngine();
      engine.addChange(createBalanceChange({
        type: 'feature',
        file: 'src/a.ts',
        linesAdded: 50,
        linesRemoved: 10,
      }));
      engine.addChange(createBalanceChange({
        type: 'bugfix',
        file: 'src/b.ts',
        linesAdded: 20,
        linesRemoved: 5,
      }));
      engine.addChange(createBalanceChange({
        type: 'docs',
        file: 'README.md',
        linesAdded: 15,
        linesRemoved: 0,
      }));

      const stats = await engine.getStats();

      expect(stats.countedChanges).toBe(2);
      expect(stats.nonCountedChanges).toBe(1);
      expect(stats.totalChanges).toBe(3);
      expect(stats.countedLines).toBe(85); // 60 + 25
      expect(stats.nonCountedLines).toBe(15);
      expect(stats.totalLines).toBe(100);
    });
  });

  describe('getBalanceReport', () => {
    it('should generate a detailed report', async () => {
      const engine = createBalanceRuleEngine();
      engine.addChange(createBalanceChange({
        type: 'feature',
        file: 'src/feature.ts',
        linesAdded: 100,
        linesRemoved: 0,
      }));
      engine.addChange(createBalanceChange({
        type: 'config',
        file: 'config.json',
        linesAdded: 5,
        linesRemoved: 0,
      }));

      const report = await engine.getBalanceReport();

      expect(report).toContain('Balance Report');
      expect(report).toContain('counted');
      expect(report).toContain('non-counted');
    });
  });

  describe('addChange / removeChange / clear', () => {
    it('should manage changes correctly', () => {
      const engine = createBalanceRuleEngine();
      const change = createBalanceChange({
        id: 'change-1',
        type: 'feature',
        file: 'test.ts',
        linesAdded: 10,
        linesRemoved: 0,
      });

      engine.addChange(change);
      expect(engine.getChanges()).toHaveLength(1);

      engine.removeChange('change-1');
      expect(engine.getChanges()).toHaveLength(0);
    });

    it('should clear all changes', () => {
      const engine = createBalanceRuleEngine();
      engine.addChange(createBalanceChange({
        type: 'feature',
        file: 'a.ts',
        linesAdded: 10,
        linesRemoved: 0,
      }));
      engine.addChange(createBalanceChange({
        type: 'bugfix',
        file: 'b.ts',
        linesAdded: 20,
        linesRemoved: 0,
      }));

      engine.clear();

      expect(engine.getChanges()).toHaveLength(0);
    });
  });

  describe('custom configuration', () => {
    it('should use custom threshold', async () => {
      const config: BalanceConfig = {
        ...DEFAULT_BALANCE_CONFIG,
        maxNonCountedRatio: 0.2, // 20% allowed
      };
      const engine = createBalanceRuleEngine(config);

      // 80% counted, 20% non-counted
      engine.addChange(createBalanceChange({
        type: 'feature',
        file: 'src/feature.ts',
        linesAdded: 80,
        linesRemoved: 0,
      }));
      engine.addChange(createBalanceChange({
        type: 'config',
        file: 'config.json',
        linesAdded: 20,
        linesRemoved: 0,
      }));

      const result = await engine.evaluateBalance();

      expect(result.passed).toBe(true); // 20% is within 20% threshold
    });

    it('should apply custom type weights', async () => {
      const config: BalanceConfig = {
        ...DEFAULT_BALANCE_CONFIG,
        typeWeights: {
          ...DEFAULT_BALANCE_CONFIG.typeWeights,
          test: 1.0, // Count tests at 100%
        },
      };
      const engine = createBalanceRuleEngine(config);

      engine.addChange(createBalanceChange({
        type: 'test',
        file: 'test.spec.ts',
        linesAdded: 100,
        linesRemoved: 0,
      }));

      const stats = await engine.getStats();
      expect(stats.countedLines).toBe(100); // Full weight
    });
  });

  describe('inferChangeType', () => {
    it('should infer test type from test file', () => {
      const engine = createBalanceRuleEngine();
      
      expect(engine.inferChangeType('src/index.test.ts')).toBe('test');
      expect(engine.inferChangeType('__tests__/app.spec.ts')).toBe('test');
    });

    it('should infer config type from config files', () => {
      const engine = createBalanceRuleEngine();
      
      expect(engine.inferChangeType('tsconfig.json')).toBe('config');
      expect(engine.inferChangeType('.eslintrc.js')).toBe('config');
      expect(engine.inferChangeType('vitest.config.ts')).toBe('config');
    });

    it('should infer docs type from documentation files', () => {
      const engine = createBalanceRuleEngine();
      
      expect(engine.inferChangeType('README.md')).toBe('docs');
      expect(engine.inferChangeType('docs/guide.md')).toBe('docs');
    });

    it('should infer ci type from CI files', () => {
      const engine = createBalanceRuleEngine();
      
      expect(engine.inferChangeType('.github/workflows/ci.yml')).toBe('ci');
    });

    it('should default to feature for source files', () => {
      const engine = createBalanceRuleEngine();
      
      expect(engine.inferChangeType('src/index.ts')).toBe('feature');
      expect(engine.inferChangeType('packages/core/src/app.ts')).toBe('feature');
    });
  });
});
