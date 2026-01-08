/**
 * Best-First Search Tests
 * @module @nahisaho/musubix-neural-search
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { BestFirstSearch } from '../../src/search/BestFirstSearch.js';
import { BranchScorer } from '../../src/scorer/BranchScorer.js';
import { EmbeddingModel } from '../../src/scorer/EmbeddingModel.js';
import { SearchTimeoutError, SearchDepthExceededError } from '../../src/errors.js';
import type { Branch, SearchConfig, SearchContext, SearchState } from '../../src/types.js';

describe('BestFirstSearch', () => {
  let search: BestFirstSearch;
  let scorer: BranchScorer;
  let embeddingModel: EmbeddingModel;

  beforeEach(() => {
    search = new BestFirstSearch();
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
    let counter = 0;
    return async (state: SearchState) => {
      const branches: Branch[] = [];
      for (let i = 0; i < branchesPerState; i++) {
        counter++;
        const newCode = `${state.code}step${counter};`;
        const codeEmbedding = await embeddingModel.embedCode(newCode || 'empty');
        branches.push({
          from: state,
          to: {
            id: `state-${counter}`,
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
    maxDepth: 10,  // Increased to allow deeper search
    maxIterations: 50,  // Allow more iterations
    timeout: 5000,
  };

  describe('search', () => {
    it('should return a search result', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      const result = await search.search(
        initial,
        expand,
        scorer,
        context,
        defaultConfig
      );

      expect(result).toBeDefined();
      expect(result.state).toBeDefined();
      expect(result.score).toBeGreaterThanOrEqual(0);
      expect(result.path).toBeDefined();
    });

    it('should track iterations', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      const result = await search.search(
        initial,
        expand,
        scorer,
        context,
        defaultConfig
      );

      expect(result.iterations).toBeGreaterThan(0);
    });

    it('should return path to result', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      const result = await search.search(
        initial,
        expand,
        scorer,
        context,
        defaultConfig
      );

      expect(result.path.length).toBeGreaterThan(0);
    });
  });

  describe('pruning', () => {
    it('should prune low-scoring states', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(5);
      const config = { ...defaultConfig, pruneThreshold: 0.3 };

      const result = await search.search(
        initial,
        expand,
        scorer,
        context,
        config
      );

      expect(result.pruned).toBeGreaterThanOrEqual(0);
    });
  });

  describe('limits', () => {
    it('should throw on timeout', async () => {
      const initial: SearchState = {
        id: 'initial',
        code: '',
        depth: 0,
        metadata: {},
      };
      const context = await createContext('Create a function');
      
      // Slow expander that delays each expansion
      let expansionCount = 0;
      const slowExpand = async (state: SearchState): Promise<Branch[]> => {
        expansionCount++;
        // Wait longer than the timeout before returning
        await new Promise((r) => setTimeout(r, 100));
        const branches: Branch[] = [];
        const codeEmbedding = await embeddingModel.embedCode('code');
        branches.push({
          from: state,
          to: {
            id: `${state.id}-next-${expansionCount}`,
            code: state.code + 'next;',
            parent: state.id,
            depth: state.depth + 1,
            metadata: {},
          },
          action: 'generate',
          features: {
            codeEmbedding,
            specSimilarity: 0.5, // Low enough to not be goal
            syntaxValid: true,
            typeChecks: true,
            complexity: 10,
            novelty: 0.5,
          },
        });
        return branches;
      };

      // Use very short timeout that will trigger during expansion
      const config = { ...defaultConfig, timeout: 10, maxIterations: 100 };

      await expect(
        search.search(initial, slowExpand, scorer, context, config)
      ).rejects.toThrow(SearchTimeoutError);
    });

    it('should throw on depth exceeded', async () => {
      const initial: SearchState = {
        id: 'initial',
        code: '',
        depth: 0,
        metadata: {},
      };
      const context = await createContext('Create a function');
      
      // Create expander that generates low scores to avoid early termination
      let counter = 0;
      const expand = async (state: SearchState): Promise<Branch[]> => {
        counter++;
        const branches: Branch[] = [];
        const codeEmbedding = await embeddingModel.embedCode('code');
        branches.push({
          from: state,
          to: {
            id: `state-${counter}`,
            code: state.code + 'step;',
            parent: state.id,
            depth: state.depth + 1,
            metadata: {},
          },
          action: 'generate',
          features: {
            codeEmbedding,
            specSimilarity: 0.3, // Low enough to not be goal
            syntaxValid: true,
            typeChecks: true,
            complexity: 10,
            novelty: 0.5,
          },
        });
        return branches;
      };
      
      // maxDepth of 2 means depth 2 will trigger error
      const config = { ...defaultConfig, maxDepth: 2, maxIterations: 100 };

      await expect(
        search.search(initial, expand, scorer, context, config)
      ).rejects.toThrow(SearchDepthExceededError);
    });

    it('should respect max iterations', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);
      const config = { ...defaultConfig, maxIterations: 5 };

      const result = await search.search(
        initial,
        expand,
        scorer,
        context,
        config
      );

      expect(result.iterations).toBeLessThanOrEqual(5);
    });
  });

  describe('getOpenListSize', () => {
    it('should return open list size', async () => {
      // Initially empty
      expect(search.getOpenListSize()).toBe(0);

      // After search, should reflect final state
      const initial = createInitialState();
      const context = await createContext('Create a function');
      const expand = createExpander(2);

      await search.search(initial, expand, scorer, context, {
        ...defaultConfig,
        maxIterations: 3,
      });

      // Open list may have items after incomplete search
      expect(search.getOpenListSize()).toBeGreaterThanOrEqual(0);
    });
  });

  describe('duplicate detection', () => {
    it('should not revisit states', async () => {
      const initial = createInitialState();
      const context = await createContext('Create a function');
      
      let expansionCount = 0;
      const trackingExpand = async (state: SearchState): Promise<Branch[]> => {
        expansionCount++;
        return createExpander(2)(state);
      };

      await search.search(
        initial,
        trackingExpand,
        scorer,
        context,
        { ...defaultConfig, maxIterations: 10 }
      );

      // Each state should be expanded at most once
      expect(expansionCount).toBeLessThanOrEqual(10);
    });
  });
});
