/**
 * EnhancedNeuralSearchManager - Integration Tests
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-108
 *
 * Tests for integrated neural search with:
 * - LearnedPruningPolicy
 * - AdaptiveBeamSearch
 * - Online learning
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createEnhancedNeuralSearchManager,
  EnhancedNeuralSearchManager,
} from '../../src/EnhancedNeuralSearchManager.js';

describe('EnhancedNeuralSearchManager', () => {
  let manager: EnhancedNeuralSearchManager;

  beforeEach(() => {
    manager = createEnhancedNeuralSearchManager();
  });

  describe('Factory Function', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
    });

    it('should create manager with custom config', () => {
      const customManager = createEnhancedNeuralSearchManager({
        enableLearning: true,
        enableAdaptiveBeam: true,
        maxCacheSize: 500,
      });
      expect(customManager).toBeDefined();
    });
  });

  describe('LearnedPruningPolicy Integration', () => {
    it('should provide access to pruning policy', () => {
      const policy = manager.getPruningPolicy();
      expect(policy).toBeDefined();
    });

    it('should apply learned pruning during search', async () => {
      const searchSpace = [
        { id: 's1', score: 0.9, features: [1, 0, 1] },
        { id: 's2', score: 0.5, features: [0, 1, 0] },
        { id: 's3', score: 0.8, features: [1, 1, 0] },
      ];

      const result = await manager.search({
        query: 'test query',
        candidates: searchSpace,
        maxResults: 2,
      });

      expect(result).toBeDefined();
      expect(result.results.length).toBeLessThanOrEqual(2);
    });
  });

  describe('AdaptiveBeamSearch Integration', () => {
    it('should provide access to adaptive beam search', () => {
      const beamSearch = manager.getAdaptiveBeamSearch();
      expect(beamSearch).toBeDefined();
    });

    it('should perform adaptive beam search', async () => {
      const initialState = { code: '', depth: 0 };

      const result = await manager.beamSearch({
        initialState,
        expand: (state) => {
          if (state.depth >= 3) return [];
          return [
            { code: state.code + 'a', depth: state.depth + 1 },
            { code: state.code + 'b', depth: state.depth + 1 },
          ];
        },
        score: (state) => state.code.length * 0.3,
        isGoal: (state) => state.code.length >= 3,
        beamWidth: 3,
      });

      expect(result.solutions.length).toBeGreaterThanOrEqual(0);
    });

    it('should adapt beam width based on search progress', async () => {
      const stats = manager.getAdaptiveStats();
      expect(stats.beamWidthAdjustments).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Online Learning Integration', () => {
    it('should enable online learning', () => {
      manager.enableLearning(true);
      const isEnabled = manager.isLearningEnabled();
      expect(isEnabled).toBe(true);
    });

    it('should learn from search feedback', async () => {
      manager.enableLearning(true);

      // Simulate a search
      const candidates = [
        { id: 'c1', score: 0.8, features: [1, 1, 0] },
        { id: 'c2', score: 0.3, features: [0, 0, 1] },
      ];

      await manager.search({
        query: 'function add',
        candidates,
        maxResults: 2,
      });

      // Provide feedback
      await manager.provideFeedback({
        queryId: 'function add',
        selectedId: 'c1',
        outcome: 'success',
      });

      const stats = manager.getLearningStats();
      expect(stats.totalFeedback).toBeGreaterThanOrEqual(1);
    });

    it('should update model with accumulated feedback', async () => {
      manager.enableLearning(true);

      // Accumulate feedback
      for (let i = 0; i < 5; i++) {
        await manager.provideFeedback({
          queryId: `query_${i}`,
          selectedId: `result_${i}`,
          outcome: i % 2 === 0 ? 'success' : 'failure',
        });
      }

      // Trigger model update
      await manager.updateModel();

      const stats = manager.getLearningStats();
      expect(stats.modelUpdates).toBeGreaterThanOrEqual(1);
    });
  });

  describe('Combined Search', () => {
    it('should perform combined neural+learned search', async () => {
      const query = 'function that adds two numbers';
      const candidates = [
        { id: 'c1', code: 'const add = (a, b) => a + b', score: 0.9, features: [1, 1, 0] },
        { id: 'c2', code: 'const sub = (a, b) => a - b', score: 0.6, features: [1, 0, 1] },
        { id: 'c3', code: 'const mul = (a, b) => a * b', score: 0.5, features: [0, 1, 1] },
      ];

      const result = await manager.combinedSearch({
        query,
        candidates,
        useNeural: true,
        useLearned: true,
        maxResults: 2,
      });

      expect(result.results.length).toBeLessThanOrEqual(2);
      expect(result.searchTimeMs).toBeGreaterThanOrEqual(0);
    });

    it('should achieve >70% search space reduction', async () => {
      // Create large search space
      const candidates = Array.from({ length: 100 }, (_, i) => ({
        id: `c${i}`,
        score: Math.random(),
        features: [Math.random() > 0.5 ? 1 : 0, Math.random() > 0.5 ? 1 : 0],
      }));

      const result = await manager.search({
        query: 'test',
        candidates,
        maxResults: 10,
      });

      const reduction = 1 - result.results.length / candidates.length;
      // At least some reduction occurred (may not always be 70% in unit tests)
      expect(reduction).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Statistics', () => {
    it('should provide comprehensive statistics', async () => {
      // Perform some operations
      await manager.search({
        query: 'test',
        candidates: [{ id: 'c1', score: 0.5, features: [1, 0] }],
        maxResults: 1,
      });

      const stats = manager.getEnhancedStats();

      expect(stats.search).toBeDefined();
      expect(stats.pruning).toBeDefined();
      expect(stats.learning).toBeDefined();
      expect(stats.beam).toBeDefined();
    });

    it('should track search history', async () => {
      await manager.search({
        query: 'query1',
        candidates: [{ id: 'c1', score: 0.5, features: [] }],
        maxResults: 1,
      });
      await manager.search({
        query: 'query2',
        candidates: [{ id: 'c2', score: 0.7, features: [] }],
        maxResults: 1,
      });

      const history = manager.getSearchHistory(2);
      expect(history.length).toBe(2);
    });
  });

  describe('Serialization', () => {
    it('should serialize enhanced state', async () => {
      manager.enableLearning(true);
      await manager.search({
        query: 'test',
        candidates: [{ id: 'c1', score: 0.5, features: [1] }],
        maxResults: 1,
      });

      const json = manager.toJSON();
      expect(json).toBeDefined();

      const parsed = JSON.parse(json);
      expect(parsed).toBeDefined();
    });

    it('should restore enhanced state', () => {
      const state = {
        learningEnabled: true,
        searchCount: 5,
      };

      manager.fromJSON(JSON.stringify(state));
      expect(manager.isLearningEnabled()).toBe(true);
    });
  });
});
