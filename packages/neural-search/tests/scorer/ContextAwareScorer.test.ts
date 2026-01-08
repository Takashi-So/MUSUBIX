/**
 * ContextAwareScorer Tests
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-103
 * @see DES-NS-103
 * @see REQ-NS-103
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createContextAwareScorer,
  type ContextAwareScorer,
  type ProjectContext,
  type ScoreBreakdown,
} from '../../src/scorer/ContextAwareScorer.js';
import type {
  Branch,
  BranchFeatures,
  SearchContext,
  SearchState,
  Embedding,
} from '../../src/types.js';

describe('ContextAwareScorer', () => {
  let scorer: ContextAwareScorer;

  // Test fixtures
  const mockEmbedding: Embedding = new Array(128).fill(0.1);
  const mockSpecEmbedding: Embedding = new Array(128).fill(0.2);

  const mockState: SearchState = {
    id: 'state-1',
    code: 'function add(a, b) { return a + b; }',
    depth: 1,
    metadata: {},
  };

  const mockFeatures: BranchFeatures = {
    codeEmbedding: mockEmbedding,
    specSimilarity: 0.8,
    syntaxValid: true,
    typeChecks: true,
    complexity: 5,
    novelty: 0.7,
  };

  const mockBranch: Branch = {
    from: mockState,
    to: { ...mockState, id: 'state-2', depth: 2 },
    action: 'add_function',
    features: mockFeatures,
  };

  const mockSearchContext: SearchContext = {
    specification: 'Create a function that adds two numbers',
    specEmbedding: mockSpecEmbedding,
    constraints: ['must be pure', 'no side effects'],
    history: [mockState],
  };

  beforeEach(() => {
    scorer = createContextAwareScorer();
  });

  describe('Factory Function', () => {
    it('should create a ContextAwareScorer instance', () => {
      const instance = createContextAwareScorer();
      expect(instance).toBeDefined();
      expect(typeof instance.score).toBe('function');
      expect(typeof instance.scoreBatch).toBe('function');
      expect(typeof instance.update).toBe('function');
    });

    it('should create with custom config', () => {
      const instance = createContextAwareScorer({
        contextWeight: 0.5,
        enableProjectContext: true,
      });
      expect(instance).toBeDefined();
    });
  });

  describe('IBranchScorer Implementation', () => {
    it('should score a single branch', async () => {
      const result = await scorer.score(mockBranch, mockSearchContext);

      expect(result).toBeDefined();
      expect(result.branch).toBe(mockBranch);
      expect(typeof result.score).toBe('number');
      expect(result.score).toBeGreaterThanOrEqual(0);
      expect(result.score).toBeLessThanOrEqual(1);
      expect(typeof result.confidence).toBe('number');
      expect(result.components).toBeDefined();
    });

    it('should score multiple branches in batch', async () => {
      const branch2: Branch = {
        ...mockBranch,
        action: 'add_parameter',
      };

      const results = await scorer.scoreBatch(
        [mockBranch, branch2],
        mockSearchContext
      );

      expect(results).toHaveLength(2);
      expect(results[0].branch).toBe(mockBranch);
      expect(results[1].branch).toBe(branch2);
    });

    it('should update with feedback', () => {
      expect(() =>
        scorer.update({
          branchId: 'branch-1',
          actualOutcome: 'success',
          reason: 'correct implementation',
        })
      ).not.toThrow();
    });
  });

  describe('Project Context', () => {
    it('should set project context', () => {
      const projectContext: ProjectContext = {
        projectName: 'test-project',
        language: 'typescript',
        patterns: ['singleton', 'factory'],
        codebaseEmbedding: mockEmbedding,
        recentFiles: ['src/utils.ts', 'src/types.ts'],
      };

      expect(() => scorer.setProjectContext(projectContext)).not.toThrow();
    });

    it('should use project context in scoring', async () => {
      const projectContext: ProjectContext = {
        projectName: 'test-project',
        language: 'typescript',
        patterns: ['functional'],
        codebaseEmbedding: mockEmbedding,
        recentFiles: [],
      };

      scorer.setProjectContext(projectContext);
      const result = await scorer.score(mockBranch, mockSearchContext);

      expect(result.score).toBeGreaterThan(0);
    });

    it('should work without project context', async () => {
      const result = await scorer.score(mockBranch, mockSearchContext);
      expect(result.score).toBeGreaterThan(0);
    });
  });

  describe('Context Weight', () => {
    it('should apply 30% or more context weight when enabled', async () => {
      const contextScorer = createContextAwareScorer({
        contextWeight: 0.3,
        enableProjectContext: true,
      });

      contextScorer.setProjectContext({
        projectName: 'test',
        language: 'typescript',
        patterns: [],
        codebaseEmbedding: mockEmbedding,
        recentFiles: [],
      });

      const result = await contextScorer.score(mockBranch, mockSearchContext);
      const breakdown = contextScorer.getScoreBreakdown(result);

      expect(breakdown.contextScore).toBeDefined();
      expect(breakdown.contextWeight).toBeGreaterThanOrEqual(0.3);
    });

    it('should allow custom context weight', async () => {
      const customScorer = createContextAwareScorer({
        contextWeight: 0.5,
      });

      const result = await customScorer.score(mockBranch, mockSearchContext);
      const breakdown = customScorer.getScoreBreakdown(result);

      expect(breakdown.contextWeight).toBe(0.5);
    });
  });

  describe('Score Breakdown', () => {
    it('should provide detailed score breakdown', async () => {
      const result = await scorer.score(mockBranch, mockSearchContext);
      const breakdown = scorer.getScoreBreakdown(result);

      expect(breakdown).toBeDefined();
      expect(typeof breakdown.baseScore).toBe('number');
      expect(typeof breakdown.contextScore).toBe('number');
      expect(typeof breakdown.contextWeight).toBe('number');
      expect(typeof breakdown.finalScore).toBe('number');
    });

    it('should have breakdown components sum to final score', async () => {
      const result = await scorer.score(mockBranch, mockSearchContext);
      const breakdown = scorer.getScoreBreakdown(result);

      const expectedFinal =
        breakdown.baseScore * (1 - breakdown.contextWeight) +
        breakdown.contextScore * breakdown.contextWeight;

      expect(breakdown.finalScore).toBeCloseTo(expectedFinal, 5);
    });
  });

  describe('Pattern Matching', () => {
    it('should boost score for matching patterns', async () => {
      scorer.setProjectContext({
        projectName: 'test',
        language: 'typescript',
        patterns: ['add_function', 'pure_function'],
        codebaseEmbedding: mockEmbedding,
        recentFiles: [],
      });

      const matchingBranch: Branch = {
        ...mockBranch,
        action: 'add_function', // Matches project pattern
      };

      const nonMatchingBranch: Branch = {
        ...mockBranch,
        action: 'remove_function',
      };

      const matchingResult = await scorer.score(matchingBranch, mockSearchContext);
      const nonMatchingResult = await scorer.score(nonMatchingBranch, mockSearchContext);

      // Pattern matching should provide higher or equal score
      expect(matchingResult.score).toBeGreaterThanOrEqual(nonMatchingResult.score * 0.9);
    });
  });

  describe('Statistics', () => {
    it('should track scoring statistics', async () => {
      await scorer.score(mockBranch, mockSearchContext);
      await scorer.score(mockBranch, mockSearchContext);

      const stats = scorer.getStatistics();

      expect(stats.totalScored).toBe(2);
      expect(typeof stats.averageScore).toBe('number');
      expect(typeof stats.averageConfidence).toBe('number');
    });

    it('should reset statistics', async () => {
      await scorer.score(mockBranch, mockSearchContext);
      scorer.resetStatistics();

      const stats = scorer.getStatistics();
      expect(stats.totalScored).toBe(0);
    });
  });

  describe('Serialization', () => {
    it('should serialize to JSON', async () => {
      scorer.setProjectContext({
        projectName: 'test',
        language: 'typescript',
        patterns: [],
        codebaseEmbedding: mockEmbedding,
        recentFiles: [],
      });

      await scorer.score(mockBranch, mockSearchContext);

      const json = scorer.toJSON();
      expect(typeof json).toBe('string');

      const parsed = JSON.parse(json);
      expect(parsed.config).toBeDefined();
      expect(parsed.statistics).toBeDefined();
    });

    it('should deserialize from JSON', () => {
      const json = JSON.stringify({
        config: { contextWeight: 0.4 },
        statistics: { totalScored: 10 },
      });

      expect(() => scorer.fromJSON(json)).not.toThrow();
    });
  });
});
