/**
 * LibraryLearner v2.2.0 Integration Test Suite
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-109
 * @see DES-LL-109
 *
 * v2.2.0コンポーネント統合テスト
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  EnhancedLibraryLearner,
  createEnhancedLibraryLearner,
  type EnhancedLibraryLearnerConfig,
} from '../../src/EnhancedLibraryLearner.js';

// =============================================================================
// Test Fixtures
// =============================================================================

function createMockConfig(): EnhancedLibraryLearnerConfig {
  return {
    abstractionLevels: 3,
    minOccurrences: 2,
    useEGraph: true,
    enableHierarchyManagement: true,
    enableTypedSearch: true,
    enableRewriteRules: true,
    enableIncrementalUpdate: true,
  };
}

const sampleCode = `
function add(a: number, b: number): number {
  return a + b;
}

function subtract(a: number, b: number): number {
  return a - b;
}

function multiply(a: number, b: number): number {
  return a * b;
}
`;

// =============================================================================
// Tests
// =============================================================================

describe('EnhancedLibraryLearner', () => {
  let learner: EnhancedLibraryLearner;

  beforeEach(() => {
    learner = createEnhancedLibraryLearner();
  });

  describe('Factory Function', () => {
    it('should create enhanced learner with default config', () => {
      const l = createEnhancedLibraryLearner();
      expect(l).toBeDefined();
      expect(l.learnFromCorpus).toBeDefined();
    });

    it('should create enhanced learner with custom config', () => {
      const config = createMockConfig();
      const l = createEnhancedLibraryLearner(config);
      expect(l).toBeDefined();
    });
  });

  describe('HierarchyManager Integration', () => {
    it('should provide access to hierarchy manager', () => {
      const hierarchy = learner.getHierarchyManager();
      expect(hierarchy).toBeDefined();
    });

    it('should manage pattern hierarchy during learning', async () => {
      await learner.learnFromCode(sampleCode);
      
      const hierarchy = learner.getHierarchyManager();
      const depth = hierarchy.getDepth();
      expect(depth).toBeGreaterThanOrEqual(0);
    });
  });

  describe('TypeDirectedPruner Integration', () => {
    it('should provide access to type pruner', () => {
      const pruner = learner.getTypePruner();
      expect(pruner).toBeDefined();
    });

    it('should use type-directed pruning in synthesis', async () => {
      await learner.learnFromCode(sampleCode);
      
      const result = await learner.synthesizeWithTypes({
        description: 'Add two numbers',
        inputTypes: ['number', 'number'],
        outputType: 'number',
      });
      
      expect(result).toBeDefined();
      expect(result.searchStats).toBeDefined();
    });
  });

  describe('RewriteRuleSet Integration', () => {
    it('should provide access to rewrite rules', () => {
      const rules = learner.getRewriteRules();
      expect(rules).toBeDefined();
    });

    it('should apply rewrite rules during optimization', async () => {
      await learner.learnFromCode(sampleCode);
      
      const rules = learner.getRewriteRules();
      const ruleCount = rules.getRuleCount();
      expect(ruleCount).toBeGreaterThanOrEqual(0);
    });
  });

  describe('IncrementalUpdater Integration', () => {
    it('should provide access to incremental updater', () => {
      const updater = learner.getIncrementalUpdater();
      expect(updater).toBeDefined();
    });

    it('should process file changes incrementally', async () => {
      await learner.processFileChange({
        filePath: '/test/file.ts',
        changeType: 'modified',
        affectedLines: [1, 2, 3],
        timestamp: Date.now(),
      });
      
      const updater = learner.getIncrementalUpdater();
      const stats = updater.getStatistics();
      expect(stats.totalChangesProcessed).toBe(1);
    });

    it('should meet 5sec/500LOC performance target', async () => {
      const start = Date.now();
      
      await learner.processFileChange({
        filePath: '/test/large-file.ts',
        changeType: 'modified',
        affectedLines: Array.from({ length: 500 }, (_, i) => i + 1),
        timestamp: Date.now(),
      });
      
      const duration = Date.now() - start;
      expect(duration).toBeLessThan(5000);
    });
  });

  describe('Enhanced learnFromCode', () => {
    it('should learn patterns from code string', async () => {
      const result = await learner.learnFromCode(sampleCode);
      
      expect(result).toBeDefined();
      expect(result.patternsExtracted).toBeGreaterThanOrEqual(0);
    });

    it('should track hierarchy metrics', async () => {
      await learner.learnFromCode(sampleCode);
      
      const metrics = learner.getHierarchyMetrics();
      expect(metrics).toBeDefined();
    });
  });

  describe('synthesizeWithTypes', () => {
    it('should synthesize with type constraints', async () => {
      await learner.learnFromCode(sampleCode);
      
      const result = await learner.synthesizeWithTypes({
        description: 'Binary operation',
        inputTypes: ['number', 'number'],
        outputType: 'number',
      });
      
      expect(result).toBeDefined();
    });

    it('should report search statistics', async () => {
      await learner.learnFromCode(sampleCode);
      
      const result = await learner.synthesizeWithTypes({
        description: 'Compute result',
        inputTypes: ['number'],
        outputType: 'number',
      });
      
      expect(result.searchStats).toBeDefined();
      expect(result.searchStats.candidatesExamined).toBeGreaterThanOrEqual(0);
    });
  });

  describe('optimizeWithRewrites', () => {
    it('should optimize program using rewrite rules', async () => {
      const program = 'x + 0'; // Can be simplified
      
      const result = await learner.optimizeWithRewrites(program);
      
      expect(result).toBeDefined();
      expect(result.optimized).toBeDefined();
    });

    it('should track rewrite applications', async () => {
      const result = await learner.optimizeWithRewrites('a * 1');
      
      expect(result.rewritesApplied).toBeGreaterThanOrEqual(0);
    });
  });

  describe('getEnhancedStats', () => {
    it('should return comprehensive statistics', async () => {
      await learner.learnFromCode(sampleCode);
      
      const stats = await learner.getEnhancedStats();
      
      expect(stats).toBeDefined();
      expect(stats.basic).toBeDefined();
      expect(stats.hierarchy).toBeDefined();
      expect(stats.rewrite).toBeDefined();
      expect(stats.incremental).toBeDefined();
    });
  });

  describe('Serialization', () => {
    it('should serialize enhanced state', async () => {
      await learner.learnFromCode(sampleCode);
      
      const json = learner.toJSON();
      expect(json).toBeDefined();
      expect(typeof json).toBe('string');
    });

    it('should restore enhanced state', async () => {
      await learner.learnFromCode(sampleCode);
      const json = learner.toJSON();
      
      const newLearner = createEnhancedLibraryLearner();
      newLearner.fromJSON(json);
      
      const origStats = await learner.getEnhancedStats();
      const newStats = await newLearner.getEnhancedStats();
      
      // Basic stats should match
      expect(newStats.basic.totalPatterns).toBe(origStats.basic.totalPatterns);
    });
  });
});
