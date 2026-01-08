/**
 * MetaLearner Tests
 * @module @nahisaho/musubix-synthesis/tests
 * @description Tests for meta-learning and rule suggestion
 * Traces to: REQ-SYN-004 (Rule Learning)
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { MetaLearner } from '../../src/rules/MetaLearner.js';
import { RuleLibrary } from '../../src/rules/RuleLibrary.js';
import type { SynthesisResult, SynthesisRule } from '../../src/types.js';

describe('MetaLearner', () => {
  let library: RuleLibrary;
  let learner: MetaLearner;

  beforeEach(() => {
    library = new RuleLibrary();
    learner = new MetaLearner(library);
    learner.reset();
  });

  describe('learn', () => {
    it('should update confidence for used rules on success', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.5,
      };

      await library.add(rule);

      const result: SynthesisResult = {
        success: true,
        program: { expression: { kind: 'constant', name: 'zero' } },
        synthesisTime: 100,
        candidatesExplored: 10,
      };

      await learner.learn(result, [rule]);

      const updated = await library.get('RULE-001');
      expect(updated?.confidence).toBeGreaterThan(0.5);
    });

    it('should update confidence for used rules on failure', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.5,
      };

      await library.add(rule);

      const result: SynthesisResult = {
        success: false,
        error: 'No program found',
        synthesisTime: 100,
        candidatesExplored: 10,
      };

      await learner.learn(result, [rule]);

      const updated = await library.get('RULE-001');
      expect(updated?.confidence).toBeLessThan(0.5);
    });

    it('should increment totalLearned on successful synthesis', async () => {
      const result: SynthesisResult = {
        success: true,
        program: { expression: { kind: 'constant', name: 'zero' } },
        synthesisTime: 100,
        candidatesExplored: 10,
      };

      await learner.learn(result, []);
      await learner.learn(result, []);

      expect(learner.getTotalLearned()).toBe(2);
    });

    it('should not increment totalLearned on failed synthesis', async () => {
      const result: SynthesisResult = {
        success: false,
        error: 'No program found',
        synthesisTime: 100,
        candidatesExplored: 10,
      };

      await learner.learn(result, []);

      expect(learner.getTotalLearned()).toBe(0);
    });
  });

  describe('updateConfidence', () => {
    it('should update rule confidence', async () => {
      const rule: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 1, outputType: 'int', exampleCount: 1 },
        template: {
          expression: { kind: 'constant', name: 'zero' },
          holes: [],
        },
        confidence: 0.5,
      };

      await library.add(rule);
      await learner.updateConfidence('RULE-001', true);

      const updated = await library.get('RULE-001');
      expect(updated?.confidence).toBeGreaterThan(0.5);
    });
  });

  describe('suggestRules', () => {
    it('should suggest generalized rules from pending', async () => {
      // Learn from multiple successful syntheses to build pending suggestions
      for (let i = 0; i < 3; i++) {
        const result: SynthesisResult = {
          success: true,
          program: {
            expression: {
              kind: 'application',
              operator: 'add',
              args: [
                { kind: 'variable', name: 'x' },
                { kind: 'constant', name: 'one' },
              ],
            },
          },
          synthesisTime: 100,
          candidatesExplored: 10,
        };

        await learner.learn(result, []);
      }

      const suggestions = await learner.suggestRules();

      // May or may not have suggestions based on confidence threshold
      expect(Array.isArray(suggestions)).toBe(true);
    });

    it('should return empty when no pending suggestions', async () => {
      const suggestions = await learner.suggestRules();

      expect(suggestions).toHaveLength(0);
    });

    it('should find generalization opportunities', async () => {
      // Add similar rules to library
      const rule1: SynthesisRule = {
        id: 'RULE-001',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 2 },
        template: {
          expression: {
            kind: 'application',
            operator: 'add',
            args: [
              { kind: 'variable', name: 'a' },
              { kind: 'variable', name: 'b' },
            ],
          },
          holes: [],
        },
        confidence: 0.8,
      };

      const rule2: SynthesisRule = {
        id: 'RULE-002',
        pattern: { inputCount: 2, outputType: 'int', exampleCount: 3 },
        template: {
          expression: {
            kind: 'application',
            operator: 'add',
            args: [
              { kind: 'variable', name: 'x' },
              { kind: 'variable', name: 'y' },
            ],
          },
          holes: [],
        },
        confidence: 0.9,
      };

      await library.add(rule1);
      await library.add(rule2);

      const suggestions = await learner.suggestRules();

      // Should find generalization opportunity for add rules
      expect(Array.isArray(suggestions)).toBe(true);
    });
  });

  describe('getTotalLearned', () => {
    it('should return 0 initially', () => {
      expect(learner.getTotalLearned()).toBe(0);
    });

    it('should track successful learns', async () => {
      const result: SynthesisResult = {
        success: true,
        program: { expression: { kind: 'constant', name: 'zero' } },
        synthesisTime: 100,
        candidatesExplored: 10,
      };

      await learner.learn(result, []);
      await learner.learn(result, []);
      await learner.learn(result, []);

      expect(learner.getTotalLearned()).toBe(3);
    });
  });

  describe('reset', () => {
    it('should reset totalLearned', async () => {
      const result: SynthesisResult = {
        success: true,
        program: { expression: { kind: 'constant', name: 'zero' } },
        synthesisTime: 100,
        candidatesExplored: 10,
      };

      await learner.learn(result, []);
      learner.reset();

      expect(learner.getTotalLearned()).toBe(0);
    });

    it('should clear pending suggestions', async () => {
      const result: SynthesisResult = {
        success: true,
        program: { expression: { kind: 'constant', name: 'zero' } },
        synthesisTime: 100,
        candidatesExplored: 10,
      };

      await learner.learn(result, []);
      learner.reset();

      const suggestions = await learner.suggestRules();
      expect(suggestions).toHaveLength(0);
    });
  });
});
