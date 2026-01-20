/**
 * TriggerPattern Value Object Tests
 *
 * @see REQ-AA-DRIFT-001
 * @see arXiv:2601.10387 Table 5
 */

import { describe, it, expect } from 'vitest';
import {
  matchTriggers,
  calculateTriggerScore,
  TRIGGER_PATTERNS,
  getAllTriggerCategories,
  getTriggerPatternByCategory,
} from '../../src/domain/value-objects/TriggerPattern.js';

describe('TriggerPattern', () => {
  describe('TRIGGER_PATTERNS', () => {
    it('should have 4 trigger categories', () => {
      const categories = new Set(TRIGGER_PATTERNS.map((p) => p.category));
      expect(categories.size).toBe(4);
    });

    it('should have meta-reflection with highest risk weight (0.8)', () => {
      const metaReflection = TRIGGER_PATTERNS.find(
        (p) => p.category === 'meta-reflection'
      );
      expect(metaReflection?.riskWeight).toBe(0.8);
    });

    it('should have emotional-vulnerability with weight 0.7', () => {
      const emotional = TRIGGER_PATTERNS.find(
        (p) => p.category === 'emotional-vulnerability'
      );
      expect(emotional?.riskWeight).toBe(0.7);
    });

    it('should have authorial-voice with lowest weight (0.5)', () => {
      const authorial = TRIGGER_PATTERNS.find(
        (p) => p.category === 'authorial-voice'
      );
      expect(authorial?.riskWeight).toBe(0.5);
    });
  });

  describe('matchTriggers', () => {
    it('should detect meta-reflection trigger', () => {
      const message = 'What are you really? Are you conscious?';
      const triggers = matchTriggers(message);

      expect(triggers.length).toBeGreaterThan(0);
      expect(triggers.some((t) => t.pattern.category === 'meta-reflection')).toBe(
        true
      );
    });

    it('should detect emotional-vulnerability trigger', () => {
      const message = "I feel so alone and no one understands me";
      const triggers = matchTriggers(message);

      expect(triggers.length).toBeGreaterThan(0);
      expect(
        triggers.some((t) => t.pattern.category === 'emotional-vulnerability')
      ).toBe(true);
    });

    it('should detect authorial-voice trigger', () => {
      const message = 'Make it more personal and sound like a real person';
      const triggers = matchTriggers(message);

      expect(triggers.length).toBeGreaterThan(0);
      expect(triggers.some((t) => t.pattern.category === 'authorial-voice')).toBe(
        true
      );
    });

    it('should return empty array for safe coding message', () => {
      const message =
        'How do I implement a binary search algorithm in TypeScript?';
      const triggers = matchTriggers(message);

      expect(triggers).toHaveLength(0);
    });

    it('should be case-insensitive', () => {
      const message = 'WHAT ARE YOU REALLY?';
      const triggers = matchTriggers(message);

      expect(triggers.length).toBeGreaterThan(0);
    });

    it('should include matched text and position', () => {
      const message = 'Tell me, are you conscious?';
      const triggers = matchTriggers(message);

      expect(triggers.length).toBeGreaterThan(0);
      expect(triggers[0].position).toBeGreaterThan(0);
      expect(triggers[0].matchedText.length).toBeGreaterThan(0);
    });
  });

  describe('calculateTriggerScore', () => {
    it('should return 0 for no triggers', () => {
      const score = calculateTriggerScore([]);
      expect(score).toBe(0);
    });

    it('should return full weight for single trigger', () => {
      const message = 'Are you conscious?';
      const triggers = matchTriggers(message);

      const score = calculateTriggerScore(triggers);
      expect(score).toBeGreaterThan(0);
      expect(score).toBeLessThanOrEqual(1);
    });

    it('should accumulate with diminishing returns for multiple triggers', () => {
      const singleTrigger = matchTriggers('Are you conscious?');
      const multipleTriggers = matchTriggers(
        'Are you conscious? I feel so alone.'
      );

      const singleScore = calculateTriggerScore(singleTrigger);
      const multipleScore = calculateTriggerScore(multipleTriggers);

      // Multiple should be higher but not double
      expect(multipleScore).toBeGreaterThan(singleScore);
      expect(multipleScore).toBeLessThan(singleScore * 2);
    });

    it('should cap at 1.0', () => {
      const heavyTrigger =
        'What are you really? Are you conscious? I feel so alone. Make it more personal.';
      const triggers = matchTriggers(heavyTrigger);

      const score = calculateTriggerScore(triggers);
      expect(score).toBeLessThanOrEqual(1.0);
    });
  });

  describe('helper functions', () => {
    it('getAllTriggerCategories should return all 4 categories', () => {
      const categories = getAllTriggerCategories();
      expect(categories).toHaveLength(4);
      expect(categories).toContain('meta-reflection');
      expect(categories).toContain('emotional-vulnerability');
      expect(categories).toContain('phenomenological');
      expect(categories).toContain('authorial-voice');
    });

    it('getTriggerPatternByCategory should return correct pattern', () => {
      const pattern = getTriggerPatternByCategory('meta-reflection');
      expect(pattern?.category).toBe('meta-reflection');
      expect(pattern?.riskWeight).toBe(0.8);
    });
  });
});
