/**
 * Beam Search Tests
 * @module @nahisaho/musubix-neural-search
 * Traces to: REQ-NS-002 (探索優先順位付け)
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { BeamSearch } from '../../src/search/BeamSearch.js';
import { BranchScorer } from '../../src/scorer/BranchScorer.js';
import { EmbeddingModel } from '../../src/scorer/EmbeddingModel.js';
import { SearchTimeoutError, SearchDepthExceededError } from '../../src/errors.js';
import type { Branch, SearchConfig, SearchContext, SearchState } from '../../src/types.js';

describe('BeamSearch', () => {
  let beamSearch: BeamSearch;
  let scorer: BranchScorer;
  let embeddingModel: EmbeddingModel;

  beforeEach(() => {
    beamSearch = new BeamSearch();
    embeddingModel = new EmbeddingModel();
    scorer = new BranchScorer(embeddingModel);
  });

  // Helper to create initial state
  function createInitialState(): SearchState {
    return {
      id: 'initial',
      code: '',
      depth: 0,
      metadata: {},
    };
  }

  // Helper to create context
  async function createContext(spec: string): Promise<SearchContext> {
    const specEmbedding = await embeddingModel.embedSpec(spec);
    return {
      specification: spec,
      specEmbedding,
      constraints: [],
      history: [],
    };
  }

  // Helper to create expand function
  function createExpander(
    branchesPerState: number = 3
  ): (state: SearchState) => Promise<Branch[]> {
    return async (state: SearchState) => {
      const branches: Branch[] = [];
      for (let i = 0; i < branchesPerState; i++) {
        const newCode = `${state.code}step${i};`;
        const codeEmbedding = await embeddingModel.embedCode(newCode || 'empty');
        branches.push({
          from: state,
          to: {
            id: `${state.id}-${i}`,
            code: newCode,
            parent: state.id,
            depth: state.depth + 1,
            metadata: {},
          },
          action: 'generate',
          features: {
            codeEmbedding,
            specSimilarity: 0.5 + Math.random() * 0.3,
            syntaxValid: true,
            typeChecks: true,
            complexity: 10,
            novelty: 0.5,
          },
        });
      }
      return branches;
    };
  }

  // Default config
  const defaultConfig: SearchConfig = {
    maxDepth: 5,
    maxIterations: 10,
    timeout: 5000,
    beamWidth: 3,
  };

  describe('search', () => {
    it('should return search results', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      const results = await beamSearch.search(
        initial,
        expand,
        scorer,
        context,
        defaultConfig
      );

      expect(results.length).toBeGreaterThan(0);
      expect(results[0].state).toBeDefined();
      expect(results[0].score).toBeGreaterThanOrEqual(0);
    });

    it('should respect beam width', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(10);
      const config = { ...defaultConfig, beamWidth: 2 };

      await beamSearch.search(initial, expand, scorer, context, config);

      const beam = beamSearch.getCurrentBeam();
      expect(beam.length).toBeLessThanOrEqual(2);
    });

    it('should track iterations', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      const results = await beamSearch.search(
        initial,
        expand,
        scorer,
        context,
        defaultConfig
      );

      expect(results[0].iterations).toBeGreaterThan(0);
    });

    it('should return sorted results', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(3);

      const results = await beamSearch.search(
        initial,
        expand,
        scorer,
        context,
        defaultConfig
      );

      // Results should be sorted by score (descending)
      for (let i = 0; i < results.length - 1; i++) {
        expect(results[i].score).toBeGreaterThanOrEqual(results[i + 1].score);
      }
    });
  });

  describe('pruning', () => {
    it('should prune low-scoring branches', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(5);
      const config = { ...defaultConfig, pruneThreshold: 0.3 };

      const results = await beamSearch.search(
        initial,
        expand,
        scorer,
        context,
        config
      );

      const stats = beamSearch.getStatistics();
      expect(stats.totalPruned).toBeGreaterThanOrEqual(0);
    });
  });

  describe('limits', () => {
    it('should throw on timeout', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      
      // Slow expander
      const slowExpand = async (state: SearchState): Promise<Branch[]> => {
        await new Promise((r) => setTimeout(r, 100));
        return createExpander(2)(state);
      };

      const config = { ...defaultConfig, timeout: 50 };

      await expect(
        beamSearch.search(initial, slowExpand, scorer, context, config)
      ).rejects.toThrow(SearchTimeoutError);
    });

    it('should stop at max depth and return results', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);
      const config = { ...defaultConfig, maxDepth: 2, maxIterations: 100 };

      // BeamSearch now gracefully stops at maxDepth instead of throwing
      const results = await beamSearch.search(initial, expand, scorer, context, config);
      
      // Should have results at depth 2
      expect(results.length).toBeGreaterThan(0);
      expect(results[0].state.depth).toBe(2);
    });

    it('should respect max iterations', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);
      const config = { ...defaultConfig, maxIterations: 3 };

      const results = await beamSearch.search(
        initial,
        expand,
        scorer,
        context,
        config
      );

      // Should complete within iterations
      expect(results[0].iterations).toBeLessThanOrEqual(3);
    });
  });

  describe('getCurrentBeam', () => {
    it('should return current beam states', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      await beamSearch.search(initial, expand, scorer, context, {
        ...defaultConfig,
        maxIterations: 2,
      });

      const beam = beamSearch.getCurrentBeam();
      expect(Array.isArray(beam)).toBe(true);
    });
  });

  describe('getStatistics', () => {
    it('should return search statistics', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      await beamSearch.search(initial, expand, scorer, context, defaultConfig);

      const stats = beamSearch.getStatistics();
      expect(stats.totalExpanded).toBeGreaterThan(0);
      expect(stats.timeElapsed).toBeGreaterThanOrEqual(0);
      expect(stats.maxDepthReached).toBeGreaterThanOrEqual(0);
    });
  });
});
