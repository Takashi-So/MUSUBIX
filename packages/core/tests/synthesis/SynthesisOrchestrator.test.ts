/**
 * SynthesisOrchestrator Test Suite
 * @module @nahisaho/musubix-core
 * @see TSK-INT-101
 * @see DES-INT-101
 * @see REQ-INT-101
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  SynthesisOrchestrator,
  createSynthesisOrchestrator,
  type OrchestratorConfig,
  type SynthesisRequest,
  type SynthesisResponse,
  type OrchestratorStatistics,
} from '../../src/synthesis/SynthesisOrchestrator.js';

// =============================================================================
// Test Fixtures
// =============================================================================

function createMockConfig(): OrchestratorConfig {
  return {
    pipelinePreset: 'balanced',
    timeout: 30000,
    maxIterations: 1000,
    enableLibraryLearning: true,
    enableNeuralSearch: true,
  };
}

function createMockRequest(): SynthesisRequest {
  return {
    specification: 'Create a function that adds two numbers',
    examples: [
      { input: [1, 2], output: 3 },
      { input: [5, 3], output: 8 },
    ],
    constraints: [],
    hints: [],
  };
}

// =============================================================================
// Tests
// =============================================================================

describe('SynthesisOrchestrator', () => {
  let orchestrator: SynthesisOrchestrator;

  beforeEach(() => {
    orchestrator = createSynthesisOrchestrator();
  });

  describe('Factory Function', () => {
    it('should create orchestrator with default config', () => {
      const o = createSynthesisOrchestrator();
      expect(o).toBeDefined();
      expect(o.synthesize).toBeDefined();
    });

    it('should create orchestrator with custom config', () => {
      const config = createMockConfig();
      const o = createSynthesisOrchestrator(config);
      expect(o).toBeDefined();
    });
  });

  describe('synthesize', () => {
    it('should handle basic synthesis request', async () => {
      const request = createMockRequest();
      const response = await orchestrator.synthesize(request);
      
      expect(response).toBeDefined();
      expect(response.status).toBeDefined();
    });

    it('should return timing information', async () => {
      const request = createMockRequest();
      const response = await orchestrator.synthesize(request);
      
      expect(response.timing).toBeDefined();
      expect(response.timing.totalMs).toBeGreaterThanOrEqual(0);
    });

    it('should track pipeline stages', async () => {
      const request = createMockRequest();
      const response = await orchestrator.synthesize(request);
      
      expect(response.stagesExecuted).toBeDefined();
      expect(Array.isArray(response.stagesExecuted)).toBe(true);
    });

    it('should handle empty examples gracefully', async () => {
      const request: SynthesisRequest = {
        specification: 'Create a function',
        examples: [],
        constraints: [],
        hints: [],
      };
      
      const response = await orchestrator.synthesize(request);
      expect(response).toBeDefined();
    });
  });

  describe('synthesizeFromNL', () => {
    it('should convert natural language to synthesis request', async () => {
      const nlSpec = 'Create a function that doubles a number';
      const response = await orchestrator.synthesizeFromNL(nlSpec);
      
      expect(response).toBeDefined();
      expect(response.status).toBeDefined();
    });

    it('should handle complex natural language', async () => {
      const nlSpec = 'Build a function that takes a list of numbers and returns their sum';
      const response = await orchestrator.synthesizeFromNL(nlSpec);
      
      expect(response).toBeDefined();
    });

    it('should support additional examples', async () => {
      const nlSpec = 'Double a number';
      const examples = [{ input: 5, output: 10 }];
      const response = await orchestrator.synthesizeFromNL(nlSpec, examples);
      
      expect(response).toBeDefined();
    });
  });

  describe('synthesizeWithLibrary', () => {
    it('should use library patterns when available', async () => {
      const request = createMockRequest();
      const response = await orchestrator.synthesizeWithLibrary(request, []);
      
      expect(response).toBeDefined();
      expect(response.libraryPatternsUsed).toBeDefined();
    });

    it('should track library pattern usage', async () => {
      const request = createMockRequest();
      const libraryPatterns = [
        { id: 'pattern-1', name: 'add-two-numbers' },
      ];
      
      const response = await orchestrator.synthesizeWithLibrary(request, libraryPatterns);
      expect(response.libraryPatternsUsed).toBeGreaterThanOrEqual(0);
    });
  });

  describe('getStatistics', () => {
    it('should return initial statistics', () => {
      const stats = orchestrator.getStatistics();
      
      expect(stats).toBeDefined();
      expect(stats.totalRequests).toBe(0);
      expect(stats.successCount).toBe(0);
      expect(stats.failureCount).toBe(0);
    });

    it('should update statistics after synthesis', async () => {
      const request = createMockRequest();
      await orchestrator.synthesize(request);
      
      const stats = orchestrator.getStatistics();
      expect(stats.totalRequests).toBe(1);
    });

    it('should track average synthesis time', async () => {
      const request = createMockRequest();
      await orchestrator.synthesize(request);
      await orchestrator.synthesize(request);
      
      const stats = orchestrator.getStatistics();
      expect(stats.averageSynthesisTimeMs).toBeGreaterThanOrEqual(0);
    });
  });

  describe('reset', () => {
    it('should reset all statistics', async () => {
      const request = createMockRequest();
      await orchestrator.synthesize(request);
      
      orchestrator.reset();
      
      const stats = orchestrator.getStatistics();
      expect(stats.totalRequests).toBe(0);
    });
  });

  describe('Pipeline Integration', () => {
    it('should execute parse stage', async () => {
      const request = createMockRequest();
      const response = await orchestrator.synthesize(request);
      
      expect(response.stagesExecuted).toContain('parse');
    });

    it('should execute analyze stage', async () => {
      const request = createMockRequest();
      const response = await orchestrator.synthesize(request);
      
      expect(response.stagesExecuted).toContain('analyze');
    });

    it('should respect disabled stages', async () => {
      const config: OrchestratorConfig = {
        ...createMockConfig(),
        enableNeuralSearch: false,
      };
      const o = createSynthesisOrchestrator(config);
      
      const response = await o.synthesize(createMockRequest());
      expect(response).toBeDefined();
    });
  });

  describe('Error Handling', () => {
    it('should handle timeout gracefully', async () => {
      const config: OrchestratorConfig = {
        ...createMockConfig(),
        timeout: 1, // Very short timeout
      };
      const o = createSynthesisOrchestrator(config);
      
      const response = await o.synthesize(createMockRequest());
      // Should not throw, but may have error status
      expect(response).toBeDefined();
    });

    it('should provide error details in response', async () => {
      const request: SynthesisRequest = {
        specification: '', // Invalid empty spec
        examples: [],
        constraints: [],
        hints: [],
      };
      
      const response = await orchestrator.synthesize(request);
      expect(response.status).toBeDefined();
    });
  });

  describe('Preset Configurations', () => {
    it('should support fast preset', async () => {
      const config: OrchestratorConfig = {
        ...createMockConfig(),
        pipelinePreset: 'fast',
      };
      const o = createSynthesisOrchestrator(config);
      
      const response = await o.synthesize(createMockRequest());
      expect(response).toBeDefined();
    });

    it('should support accurate preset', async () => {
      const config: OrchestratorConfig = {
        ...createMockConfig(),
        pipelinePreset: 'accurate',
      };
      const o = createSynthesisOrchestrator(config);
      
      const response = await o.synthesize(createMockRequest());
      expect(response).toBeDefined();
    });

    it('should support balanced preset', async () => {
      const config: OrchestratorConfig = {
        ...createMockConfig(),
        pipelinePreset: 'balanced',
      };
      const o = createSynthesisOrchestrator(config);
      
      const response = await o.synthesize(createMockRequest());
      expect(response).toBeDefined();
    });
  });

  describe('toJSON / fromJSON', () => {
    it('should serialize orchestrator state', () => {
      const json = orchestrator.toJSON();
      expect(json).toBeDefined();
      expect(typeof json).toBe('string');
    });

    it('should restore orchestrator state', async () => {
      await orchestrator.synthesize(createMockRequest());
      
      const json = orchestrator.toJSON();
      
      const newOrchestrator = createSynthesisOrchestrator();
      newOrchestrator.fromJSON(json);
      
      // Statistics should be similar
      const origStats = orchestrator.getStatistics();
      const newStats = newOrchestrator.getStatistics();
      
      expect(newStats.totalRequests).toBe(origStats.totalRequests);
    });
  });
});
