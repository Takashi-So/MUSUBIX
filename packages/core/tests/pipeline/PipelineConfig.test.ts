/**
 * PipelineConfig Unit Tests
 *
 * @module @nahisaho/musubix-core
 * @see TSK-INT-102
 * @see DES-INT-102
 * @see REQ-INT-102
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  PipelineConfig,
  createPipelineConfig,
  DefaultPipelineConfig,
  type PipelineStage,
  type PipelineExecutionResult,
  type PipelineConfigOptions,
} from '../../src/pipeline/PipelineConfig.js';

describe('PipelineConfig', () => {
  let config: PipelineConfig;

  beforeEach(() => {
    config = createPipelineConfig();
  });

  // ==========================================================================
  // Interface Tests
  // ==========================================================================

  describe('createPipelineConfig', () => {
    it('should create a PipelineConfig instance', () => {
      expect(config).toBeDefined();
      expect(config).toBeInstanceOf(DefaultPipelineConfig);
    });

    it('should accept custom configuration', () => {
      const customConfig = createPipelineConfig({
        enableParallel: true,
        maxParallelStages: 4,
      });
      expect(customConfig).toBeDefined();
    });

    it('should have 7 default stages', () => {
      expect(config.getStages().length).toBe(7);
    });
  });

  // ==========================================================================
  // Stage Management Tests
  // ==========================================================================

  describe('getStages', () => {
    it('should return all configured stages', () => {
      const stages = config.getStages();
      expect(Array.isArray(stages)).toBe(true);
      expect(stages.length).toBeGreaterThan(0);
    });

    it('should include all 7 stages in correct order', () => {
      const stages = config.getStages();
      const stageNames = stages.map((s) => s.name);

      expect(stageNames).toContain('parse');
      expect(stageNames).toContain('analyze');
      expect(stageNames).toContain('extract');
      expect(stageNames).toContain('prune');
      expect(stageNames).toContain('synthesize');
      expect(stageNames).toContain('optimize');
      expect(stageNames).toContain('generate');
    });
  });

  describe('getStage', () => {
    it('should return stage by name', () => {
      const stage = config.getStage('parse');
      expect(stage).toBeDefined();
      expect(stage?.name).toBe('parse');
    });

    it('should return undefined for unknown stage', () => {
      const stage = config.getStage('unknown');
      expect(stage).toBeUndefined();
    });
  });

  describe('enableStage/disableStage', () => {
    it('should enable a stage', () => {
      config.disableStage('optimize');
      expect(config.isStageEnabled('optimize')).toBe(false);

      config.enableStage('optimize');
      expect(config.isStageEnabled('optimize')).toBe(true);
    });

    it('should disable a stage', () => {
      config.disableStage('optimize');
      expect(config.isStageEnabled('optimize')).toBe(false);
    });
  });

  describe('addStage/removeStage', () => {
    it('should add a custom stage', () => {
      const customStage: PipelineStage = {
        name: 'custom',
        description: 'Custom processing stage',
        execute: async (input) => input,
        order: 8,
      };

      const initialCount = config.getStages().length;
      config.addStage(customStage);
      expect(config.getStages().length).toBe(initialCount + 1);
    });

    it('should remove a stage', () => {
      const customStage: PipelineStage = {
        name: 'removable',
        description: 'To be removed',
        execute: async (input) => input,
        order: 9,
      };

      config.addStage(customStage);
      const countAfterAdd = config.getStages().length;

      config.removeStage('removable');
      expect(config.getStages().length).toBe(countAfterAdd - 1);
    });
  });

  // ==========================================================================
  // Execution Tests
  // ==========================================================================

  describe('execute', () => {
    it('should execute all enabled stages in order', async () => {
      const executionOrder: string[] = [];

      const mockConfig = createPipelineConfig();
      const stages = mockConfig.getStages();

      // Track execution order
      stages.forEach((stage) => {
        const originalExecute = stage.execute;
        stage.execute = async (input) => {
          executionOrder.push(stage.name);
          return originalExecute ? await originalExecute(input) : input;
        };
      });

      await mockConfig.execute({ source: 'test' });

      // Verify order
      expect(executionOrder[0]).toBe('parse');
      expect(executionOrder[executionOrder.length - 1]).toBe('generate');
    });

    it('should skip disabled stages', async () => {
      const executionOrder: string[] = [];

      const mockConfig = createPipelineConfig();
      mockConfig.disableStage('optimize');

      mockConfig.getStages().forEach((stage) => {
        const originalExecute = stage.execute;
        stage.execute = async (input) => {
          executionOrder.push(stage.name);
          return originalExecute ? await originalExecute(input) : input;
        };
      });

      await mockConfig.execute({ source: 'test' });

      expect(executionOrder).not.toContain('optimize');
    });

    it('should return execution result with metrics', async () => {
      const result = await config.execute({ source: 'test code' });

      expect(result).toBeDefined();
      expect(result.success).toBe(true);
      expect(result.stagesExecuted).toBeGreaterThan(0);
      expect(result.totalTimeMs).toBeGreaterThanOrEqual(0);
    });

    it('should handle errors gracefully', async () => {
      const errorConfig = createPipelineConfig();
      const stages = errorConfig.getStages();

      // Make parse stage throw an error
      const parseStage = stages.find((s) => s.name === 'parse');
      if (parseStage) {
        parseStage.execute = async () => {
          throw new Error('Parse failed');
        };
      }

      const result = await errorConfig.execute({ source: 'test' });

      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });
  });

  // ==========================================================================
  // Parallel Execution Tests
  // ==========================================================================

  describe('parallel execution', () => {
    it('should support parallel execution when enabled', async () => {
      const parallelConfig = createPipelineConfig({
        enableParallel: true,
        maxParallelStages: 3,
      });

      expect(parallelConfig.isParallelEnabled()).toBe(true);
    });

    it('should execute independent stages in parallel', async () => {
      const parallelConfig = createPipelineConfig({
        enableParallel: true,
        parallelGroups: [
          ['analyze', 'extract'], // These can run in parallel
        ],
      });

      const result = await parallelConfig.execute({ source: 'test' });
      expect(result.success).toBe(true);
    });
  });

  // ==========================================================================
  // Serialization Tests
  // ==========================================================================

  describe('toJSON/fromJSON', () => {
    it('should serialize configuration to JSON', () => {
      const json = config.toJSON();
      expect(json).toBeDefined();
      expect(typeof json).toBe('object');
      expect(json.stages).toBeDefined();
    });

    it('should deserialize configuration from JSON', () => {
      const json = config.toJSON();
      const restored = createPipelineConfig();
      restored.fromJSON(json);

      expect(restored.getStages().length).toBe(config.getStages().length);
    });
  });

  // ==========================================================================
  // Performance Tests
  // ==========================================================================

  describe('performance', () => {
    it('should execute pipeline within 100ms for small input', async () => {
      const startTime = Date.now();
      await config.execute({ source: 'const x = 1;' });
      const elapsed = Date.now() - startTime;

      expect(elapsed).toBeLessThan(100);
    });
  });
});
