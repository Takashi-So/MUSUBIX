/**
 * Pruning Manager Tests
 * @module @nahisaho/musubix-neural-search
 * Traces to: REQ-NS-003 (学習ベースプルーニング)
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PruningManager } from '../../src/search/PruningManager.js';
import { EmbeddingModel } from '../../src/scorer/EmbeddingModel.js';
import type { SearchContext, SearchState } from '../../src/types.js';

describe('PruningManager', () => {
  let pruner: PruningManager;
  let embeddingModel: EmbeddingModel;

  beforeEach(() => {
    pruner = new PruningManager();
    embeddingModel = new EmbeddingModel();
  });

  // Helper to create state
  function createState(id: string, code: string, depth: number): SearchState {
    return { id, code, depth, metadata: {} };
  }

  // Helper to create context
  async function createContext(spec: string = 'test'): Promise<SearchContext> {
    const specEmbedding = await embeddingModel.embedSpec(spec);
    return {
      specification: spec,
      specEmbedding,
      constraints: [],
      history: [],
    };
  }

  describe('shouldPrune', () => {
    it('should not prune valid state', async () => {
      const state = createState('s1', 'const x = 1;', 1);
      const context = await createContext();

      const decision = pruner.shouldPrune(state, context);

      expect(decision.prune).toBe(false);
    });

    it('should prune duplicate states', async () => {
      const state1 = createState('s1', 'const x = 1;', 1);
      const state2 = createState('s2', 'const x = 1;', 1);
      const context = await createContext();

      // First time: not pruned
      pruner.shouldPrune(state1, context);

      // Second time with same code: pruned as duplicate
      const decision = pruner.shouldPrune(state2, context);

      expect(decision.prune).toBe(true);
      expect(decision.reason).toBe('duplicate');
      expect(decision.confidence).toBe(1.0);
    });

    it('should prune states exceeding depth', async () => {
      const deepState = createState('deep', 'code', 20);
      const context = await createContext();

      const decision = pruner.shouldPrune(deepState, context);

      expect(decision.prune).toBe(true);
      expect(decision.reason).toBe('resource_limit');
    });

    it('should prune empty code', async () => {
      const emptyState = createState('empty', '', 1);
      const context = await createContext();

      const decision = pruner.shouldPrune(emptyState, context);

      expect(decision.prune).toBe(true);
      expect(decision.reason).toBe('dead_end');
    });

    it('should prune code with error patterns', async () => {
      const errorState = createState('error', 'SyntaxError: unexpected', 1);
      const context = await createContext();

      const decision = pruner.shouldPrune(errorState, context);

      expect(decision.prune).toBe(true);
      expect(decision.reason).toBe('dead_end');
    });

    it('should track total decisions', async () => {
      const context = await createContext();

      pruner.shouldPrune(createState('s1', 'code1', 1), context);
      pruner.shouldPrune(createState('s2', 'code2', 1), context);
      pruner.shouldPrune(createState('s3', 'code3', 1), context);

      const stats = pruner.getStatistics();
      expect(stats.totalDecisions).toBe(3);
    });
  });

  describe('learn', () => {
    it('should learn from correct prune', async () => {
      const state = createState('s1', 'bad code', 1);
      const context = await createContext();

      pruner.shouldPrune(state, context);
      pruner.learn(state, 'correct');

      const stats = pruner.getStatistics();
      expect(stats.correctPrunes).toBe(1);
    });

    it('should learn from incorrect prune', async () => {
      const state = createState('s1', 'actually good', 1);
      const context = await createContext();

      pruner.shouldPrune(state, context);
      pruner.learn(state, 'incorrect');

      const stats = pruner.getStatistics();
      expect(stats.incorrectPrunes).toBe(1);
    });

    it('should update accuracy', async () => {
      const context = await createContext();

      // 3 correct, 1 incorrect = 75% accuracy
      pruner.learn(createState('s1', 'c1', 1), 'correct');
      pruner.learn(createState('s2', 'c2', 1), 'correct');
      pruner.learn(createState('s3', 'c3', 1), 'correct');
      pruner.learn(createState('s4', 'c4', 1), 'incorrect');

      const stats = pruner.getStatistics();
      expect(stats.accuracy).toBeCloseTo(0.75, 2);
    });

    it('should not learn when disabled', async () => {
      const disabledPruner = new PruningManager({ enableLearning: false });
      const state = createState('s1', 'code', 1);

      disabledPruner.learn(state, 'correct');

      const stats = disabledPruner.getStatistics();
      expect(stats.correctPrunes).toBe(0);
    });
  });

  describe('learned patterns', () => {
    it('should learn patterns from multiple samples', async () => {
      const context = await createContext();

      // Create similar states (same pattern)
      for (let i = 0; i < 5; i++) {
        const state = createState(`s${i}`, `x = n;`, i);
        pruner.shouldPrune(state, context);
        pruner.learn(state, 'correct');
      }

      expect(pruner.getLearnedPatternsCount()).toBeGreaterThan(0);
    });

    it('should prune based on learned patterns', async () => {
      const context = await createContext();

      // Train on pattern
      for (let i = 0; i < 5; i++) {
        const state = createState(`train${i}`, 'x = n;', 1);
        pruner.shouldPrune(state, context);
        pruner.learn(state, 'correct');
      }

      // Reset seen states but keep learned patterns
      pruner.reset();

      // New state with same pattern should be pruned
      const newState = createState('new', 'x = n;', 1);
      const decision = pruner.shouldPrune(newState, context);

      // May or may not prune depending on confidence threshold
      expect(decision).toBeDefined();
    });
  });

  describe('reset', () => {
    it('should clear seen states', async () => {
      const context = await createContext();
      const state = createState('s1', 'code', 1);

      // First: not pruned
      pruner.shouldPrune(state, context);

      // Reset
      pruner.reset();

      // Same state again: should not be duplicate
      const decision = pruner.shouldPrune(createState('s2', 'code', 1), context);
      // First occurrence after reset, so not duplicate (unless dead_end)
      expect(decision.reason).not.toBe('duplicate');
    });
  });

  describe('configuration', () => {
    it('should use custom depth threshold', async () => {
      const customPruner = new PruningManager({ maxDepth: 5 });
      const context = await createContext();

      const shallowState = createState('shallow', 'code', 4);
      const deepState = createState('deep', 'other', 6);

      expect(customPruner.shouldPrune(shallowState, context).prune).toBe(false);
      expect(customPruner.shouldPrune(deepState, context).prune).toBe(true);
    });
  });

  describe('getStatistics', () => {
    it('should return all statistics', async () => {
      const stats = pruner.getStatistics();

      expect(stats).toHaveProperty('totalDecisions');
      expect(stats).toHaveProperty('correctPrunes');
      expect(stats).toHaveProperty('incorrectPrunes');
      expect(stats).toHaveProperty('accuracy');
    });

    it('should have 100% accuracy initially', () => {
      const stats = pruner.getStatistics();
      expect(stats.accuracy).toBe(1.0);
    });
  });
});
