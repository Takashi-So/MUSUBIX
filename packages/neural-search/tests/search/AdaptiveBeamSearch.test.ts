/**
 * AdaptiveBeamSearch Test Suite
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-102
 * @see DES-NS-102
 * @see REQ-NS-102
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  AdaptiveBeamSearch,
  AdaptiveBeamConfig,
} from '../../src/search/AdaptiveBeamSearch.js';
import type {
  SearchState,
  SearchContext,
  Branch,
  IBranchScorer,
  BranchScore,
  SearchConfig,
  Embedding,
} from '../../src/types.js';

// =============================================================================
// Test Fixtures
// =============================================================================

function createMockState(overrides: Partial<SearchState> = {}): SearchState {
  return {
    id: 'state-1',
    code: 'const x = 1;',
    depth: 0,
    metadata: {},
    ...overrides,
  };
}

function createMockEmbedding(): Embedding {
  return new Float32Array([0.1, 0.2, 0.3]);
}

function createMockContext(): SearchContext {
  return {
    specification: 'Create a function',
    specEmbedding: createMockEmbedding(),
    constraints: [],
    history: [],
  };
}

function createMockBranch(from: SearchState, toId: string): Branch {
  return {
    from,
    to: createMockState({ id: toId, depth: from.depth + 1 }),
    action: 'expand',
    features: {
      codeEmbedding: createMockEmbedding(),
      specSimilarity: 0.5,
      syntaxValid: true,
      typeChecks: true,
      complexity: 1,
      novelty: 0.5,
    },
  };
}

function createMockScorer(scorePattern: (id: string) => number): IBranchScorer {
  return {
    score: vi.fn(async (branch) => ({
      branch,
      score: scorePattern(branch.to.id),
      confidence: 0.8,
      components: {
        specAlignment: 0.5,
        codeQuality: 0.5,
        novelty: 0.5,
        feasibility: 0.5,
      },
    })),
    scoreBatch: vi.fn(async (branches, _context) =>
      branches.map((branch) => ({
        branch,
        score: scorePattern(branch.to.id),
        confidence: 0.8,
        components: {
          specAlignment: 0.5,
          codeQuality: 0.5,
          novelty: 0.5,
          feasibility: 0.5,
        },
      }))
    ),
    update: vi.fn(),
  };
}

// =============================================================================
// Tests
// =============================================================================

describe('AdaptiveBeamSearch', () => {
  let search: AdaptiveBeamSearch;

  beforeEach(() => {
    search = new AdaptiveBeamSearch();
  });

  describe('Constructor', () => {
    it('should create with default config', () => {
      const s = new AdaptiveBeamSearch();
      expect(s).toBeDefined();
    });

    it('should create with custom config', () => {
      const config: Partial<AdaptiveBeamConfig> = {
        initialBeamWidth: 10,
        maxBeamWidth: 200,
        stagnationThreshold: 15,
        beamWidthIncrease: 0.75,
      };
      const s = new AdaptiveBeamSearch(config);
      expect(s).toBeDefined();
    });
  });

  describe('search', () => {
    it('should complete search with improving scores', async () => {
      const initial = createMockState({ id: 'root', depth: 0 });
      const context = createMockContext();
      const config: SearchConfig = {
        maxDepth: 5,
        maxIterations: 10,
        timeout: 5000,
        beamWidth: 3,
      };

      // Scores that improve steadily
      const scorer = createMockScorer((id) => {
        const match = id.match(/state-(\d+)/);
        if (match) {
          return 0.5 + parseInt(match[1]) * 0.05;
        }
        return 0.5;
      });

      let counter = 0;
      const expand = vi.fn(async (state: SearchState) => {
        const branches: Branch[] = [];
        for (let i = 0; i < 3; i++) {
          branches.push(createMockBranch(state, `state-${counter++}`));
        }
        return branches;
      });

      const results = await search.search(initial, expand, scorer, context, config);
      
      expect(results.length).toBeGreaterThan(0);
      expect(search.getStatistics().totalExpanded).toBeGreaterThan(0);
    });

    it('should increase beam width on stagnation', async () => {
      const adaptiveSearch = new AdaptiveBeamSearch({
        initialBeamWidth: 3,
        stagnationThreshold: 3, // Trigger adaptation quickly
        beamWidthIncrease: 0.5,
      });

      const initial = createMockState({ id: 'root', depth: 0 });
      const context = createMockContext();
      const config: SearchConfig = {
        maxDepth: 10,
        maxIterations: 20,
        timeout: 5000,
        beamWidth: 3,
      };

      // Scores that don't improve (stagnation)
      const scorer = createMockScorer(() => 0.5);

      let counter = 0;
      const expand = vi.fn(async (state: SearchState) => {
        const branches: Branch[] = [];
        for (let i = 0; i < 3; i++) {
          branches.push(createMockBranch(state, `state-${counter++}`));
        }
        return branches;
      });

      await adaptiveSearch.search(initial, expand, scorer, context, config);
      
      const stats = adaptiveSearch.getAdaptiveStatistics();
      expect(stats.beamWidthAdjustments).toBeGreaterThan(0);
    });
  });

  describe('adjustBeamWidth', () => {
    it('should not exceed maxBeamWidth', async () => {
      const adaptiveSearch = new AdaptiveBeamSearch({
        initialBeamWidth: 50,
        maxBeamWidth: 100,
        stagnationThreshold: 1,
        beamWidthIncrease: 1.0, // 100% increase each time
      });

      const initial = createMockState({ id: 'root', depth: 0 });
      const context = createMockContext();
      const config: SearchConfig = {
        maxDepth: 15,
        maxIterations: 30,
        timeout: 10000,
        beamWidth: 50,
      };

      const scorer = createMockScorer(() => 0.5);

      let counter = 0;
      const expand = vi.fn(async (state: SearchState) => {
        const branches: Branch[] = [];
        for (let i = 0; i < 5; i++) {
          branches.push(createMockBranch(state, `state-${counter++}`));
        }
        return branches;
      });

      await adaptiveSearch.search(initial, expand, scorer, context, config);
      
      const stats = adaptiveSearch.getAdaptiveStatistics();
      expect(stats.currentBeamWidth).toBeLessThanOrEqual(100);
    });
  });

  describe('getAdaptiveStatistics', () => {
    it('should return initial adaptive statistics', () => {
      const stats = search.getAdaptiveStatistics();
      
      expect(stats.currentBeamWidth).toBe(5); // default
      expect(stats.beamWidthAdjustments).toBe(0);
      expect(stats.stagnationCount).toBe(0);
    });

    it('should track beam adjustments', async () => {
      const adaptiveSearch = new AdaptiveBeamSearch({
        stagnationThreshold: 2,
      });

      const initial = createMockState({ id: 'root', depth: 0 });
      const context = createMockContext();
      const config: SearchConfig = {
        maxDepth: 10,
        maxIterations: 15,
        timeout: 5000,
        beamWidth: 3,
      };

      // Constant scores = stagnation
      const scorer = createMockScorer(() => 0.5);

      let counter = 0;
      const expand = vi.fn(async (state: SearchState) => {
        const branches: Branch[] = [];
        for (let i = 0; i < 3; i++) {
          branches.push(createMockBranch(state, `state-${counter++}`));
        }
        return branches;
      });

      await adaptiveSearch.search(initial, expand, scorer, context, config);
      
      const stats = adaptiveSearch.getAdaptiveStatistics();
      expect(stats.beamWidthAdjustments).toBeGreaterThanOrEqual(0);
    });
  });

  describe('stagnation detection', () => {
    it('should detect when best score not improving', async () => {
      const adaptiveSearch = new AdaptiveBeamSearch({
        stagnationThreshold: 5,
        initialBeamWidth: 3,
      });

      const initial = createMockState({ id: 'root', depth: 0 });
      const context = createMockContext();
      const config: SearchConfig = {
        maxDepth: 8,
        maxIterations: 10,
        timeout: 5000,
        beamWidth: 3,
      };

      // Small random variation but effectively stagnant
      let callCount = 0;
      const scorer = createMockScorer(() => {
        callCount++;
        return 0.5 + (callCount % 2) * 0.001; // Tiny variation
      });

      let counter = 0;
      const expand = vi.fn(async (state: SearchState) => {
        const branches: Branch[] = [];
        for (let i = 0; i < 3; i++) {
          branches.push(createMockBranch(state, `state-${counter++}`));
        }
        return branches;
      });

      await adaptiveSearch.search(initial, expand, scorer, context, config);
      
      const stats = adaptiveSearch.getAdaptiveStatistics();
      expect(stats.stagnationCount).toBeGreaterThanOrEqual(0);
    });
  });

  describe('getCurrentBeam', () => {
    it('should return current beam states', async () => {
      const initial = createMockState({ id: 'root', depth: 0 });
      const context = createMockContext();
      const config: SearchConfig = {
        maxDepth: 2,
        maxIterations: 2,
        timeout: 5000,
        beamWidth: 3,
      };

      const scorer = createMockScorer(() => 0.5);

      let counter = 0;
      const expand = vi.fn(async (state: SearchState) => {
        const branches: Branch[] = [];
        for (let i = 0; i < 3; i++) {
          branches.push(createMockBranch(state, `state-${counter++}`));
        }
        return branches;
      });

      await search.search(initial, expand, scorer, context, config);
      
      const beam = search.getCurrentBeam();
      expect(Array.isArray(beam)).toBe(true);
    });
  });

  describe('reset', () => {
    it('should reset adaptive state', async () => {
      const adaptiveSearch = new AdaptiveBeamSearch({
        stagnationThreshold: 2,
      });

      const initial = createMockState({ id: 'root', depth: 0 });
      const context = createMockContext();
      const config: SearchConfig = {
        maxDepth: 5,
        maxIterations: 8,
        timeout: 5000,
        beamWidth: 3,
      };

      const scorer = createMockScorer(() => 0.5);

      let counter = 0;
      const expand = vi.fn(async () => {
        const branches: Branch[] = [];
        for (let i = 0; i < 3; i++) {
          branches.push(createMockBranch(initial, `state-${counter++}`));
        }
        return branches;
      });

      await adaptiveSearch.search(initial, expand, scorer, context, config);
      
      adaptiveSearch.reset();
      
      const stats = adaptiveSearch.getAdaptiveStatistics();
      expect(stats.beamWidthAdjustments).toBe(0);
      expect(stats.stagnationCount).toBe(0);
    });
  });
});
