/**
 * Branch Scorer Tests
 * @module @nahisaho/musubix-neural-search
 * Traces to: REQ-NS-001 (分岐スコアリング)
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { BranchScorer } from '../../src/scorer/BranchScorer.js';
import { EmbeddingModel } from '../../src/scorer/EmbeddingModel.js';
import type { Branch, SearchContext, SearchState, Embedding } from '../../src/types.js';

describe('BranchScorer', () => {
  let scorer: BranchScorer;
  let embeddingModel: EmbeddingModel;

  beforeEach(() => {
    embeddingModel = new EmbeddingModel();
    scorer = new BranchScorer(embeddingModel);
  });

  // Helper to create test states
  function createState(id: string, code: string, depth: number): SearchState {
    return { id, code, depth, metadata: {} };
  }

  // Helper to create test branch
  async function createBranch(
    fromCode: string,
    toCode: string,
    depth: number
  ): Promise<Branch> {
    const codeEmbedding = await embeddingModel.embedCode(toCode);
    return {
      from: createState('from', fromCode, depth - 1),
      to: createState('to', toCode, depth),
      action: 'generate',
      features: {
        codeEmbedding,
        specSimilarity: 0.7,
        syntaxValid: true,
        typeChecks: true,
        complexity: 10,
        novelty: 0.5,
      },
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

  describe('score', () => {
    it('should score a branch', async () => {
      const branch = await createBranch('', 'function add(a, b) { return a + b; }', 1);
      const context = await createContext('Create an addition function');

      const result = await scorer.score(branch, context);

      expect(result.branch).toBe(branch);
      expect(result.score).toBeGreaterThan(0);
      expect(result.score).toBeLessThanOrEqual(1);
      expect(result.confidence).toBeGreaterThan(0);
    });

    it('should return higher score for valid code', async () => {
      const validBranch = await createBranch('', 'const x = 1;', 1);
      const invalidBranch = await createBranch('', 'const x = 1;', 1);
      invalidBranch.features.syntaxValid = false;
      invalidBranch.features.typeChecks = false;

      const context = await createContext('Create a constant');

      const validResult = await scorer.score(validBranch, context);
      const invalidResult = await scorer.score(invalidBranch, context);

      expect(validResult.score).toBeGreaterThan(invalidResult.score);
    });

    it('should include score components', async () => {
      const branch = await createBranch('', 'function test() {}', 1);
      const context = await createContext('Create a test function');

      const result = await scorer.score(branch, context);

      expect(result.components).toHaveProperty('specAlignment');
      expect(result.components).toHaveProperty('codeQuality');
      expect(result.components).toHaveProperty('novelty');
      expect(result.components).toHaveProperty('feasibility');
    });

    it('should penalize high complexity', async () => {
      const simpleBranch = await createBranch('', 'x = 1', 1);
      simpleBranch.features.complexity = 5;

      const complexBranch = await createBranch('', 'x = 1', 1);
      complexBranch.features.complexity = 100;

      const context = await createContext('Create a variable');

      const simpleResult = await scorer.score(simpleBranch, context);
      const complexResult = await scorer.score(complexBranch, context);

      expect(simpleResult.components.codeQuality).toBeGreaterThan(
        complexResult.components.codeQuality
      );
    });

    it('should penalize deep exploration', async () => {
      const shallowBranch = await createBranch('', 'code', 2);
      const deepBranch = await createBranch('', 'code', 20);

      const context = await createContext('spec');

      const shallowResult = await scorer.score(shallowBranch, context);
      const deepResult = await scorer.score(deepBranch, context);

      expect(shallowResult.components.novelty).toBeGreaterThan(
        deepResult.components.novelty
      );
    });
  });

  describe('scoreBatch', () => {
    it('should score multiple branches', async () => {
      const branches = [
        await createBranch('', 'code1', 1),
        await createBranch('', 'code2', 1),
        await createBranch('', 'code3', 1),
      ];
      const context = await createContext('spec');

      const results = await scorer.scoreBatch(branches, context);

      expect(results).toHaveLength(3);
      results.forEach((result) => {
        expect(result.score).toBeGreaterThanOrEqual(0);
      });
    });
  });

  describe('update', () => {
    it('should record feedback', () => {
      scorer.update({
        branchId: 'branch-1',
        actualOutcome: 'success',
        reason: 'Good code',
      });

      const history = scorer.getFeedbackHistory('branch-1');
      expect(history).toHaveLength(1);
      expect(history[0].actualOutcome).toBe('success');
    });

    it('should accumulate multiple feedback', () => {
      scorer.update({ branchId: 'branch-1', actualOutcome: 'success' });
      scorer.update({ branchId: 'branch-1', actualOutcome: 'failure' });
      scorer.update({ branchId: 'branch-1', actualOutcome: 'partial' });

      const history = scorer.getFeedbackHistory('branch-1');
      expect(history).toHaveLength(3);
    });

    it('should return empty array for unknown branch', () => {
      const history = scorer.getFeedbackHistory('unknown');
      expect(history).toHaveLength(0);
    });
  });

  describe('weights', () => {
    it('should use default weights', () => {
      const weights = scorer.getWeights();

      expect(weights.specAlignment).toBe(0.4);
      expect(weights.codeQuality).toBe(0.3);
      expect(weights.novelty).toBe(0.15);
      expect(weights.feasibility).toBe(0.15);
    });

    it('should use custom weights', async () => {
      const customScorer = new BranchScorer(embeddingModel, {
        specAlignment: 0.8,
        codeQuality: 0.1,
        novelty: 0.05,
        feasibility: 0.05,
      });

      const weights = customScorer.getWeights();
      expect(weights.specAlignment).toBe(0.8);
    });

    it('should apply weights to score calculation', async () => {
      const specFocusedScorer = new BranchScorer(embeddingModel, {
        specAlignment: 1.0,
        codeQuality: 0,
        novelty: 0,
        feasibility: 0,
      });

      const branch = await createBranch('', 'code', 1);
      const context = await createContext('spec');

      const result = await specFocusedScorer.score(branch, context);

      // Score should be approximately equal to specAlignment component
      expect(result.score).toBeCloseTo(result.components.specAlignment, 2);
    });
  });

  describe('confidence', () => {
    it('should have higher confidence for valid code', async () => {
      const validBranch = await createBranch('', 'code', 1);
      validBranch.features.syntaxValid = true;
      validBranch.features.typeChecks = true;

      const invalidBranch = await createBranch('', 'code', 1);
      invalidBranch.features.syntaxValid = false;
      invalidBranch.features.typeChecks = false;

      const context = await createContext('spec');

      const validResult = await scorer.score(validBranch, context);
      const invalidResult = await scorer.score(invalidBranch, context);

      expect(validResult.confidence).toBeGreaterThan(invalidResult.confidence);
    });

    it('should have higher confidence with more history', async () => {
      const branch = await createBranch('', 'code', 1);

      const contextNoHistory = await createContext('spec');
      const contextWithHistory: SearchContext = {
        ...contextNoHistory,
        history: [
          createState('s1', 'code1', 1),
          createState('s2', 'code2', 2),
          createState('s3', 'code3', 3),
        ],
      };

      const resultNoHistory = await scorer.score(branch, contextNoHistory);
      const resultWithHistory = await scorer.score(branch, contextWithHistory);

      expect(resultWithHistory.confidence).toBeGreaterThan(resultNoHistory.confidence);
    });
  });
});
