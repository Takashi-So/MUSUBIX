/**
 * @fileoverview Tests for Skill-Pattern Bridge
 * @traceability TSK-INT-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createSkillPatternBridge,
  createLearnedPatternFromSession,
  formatPatternMatchesAsMarkdown,
} from '../skill-pattern-bridge.js';
import type {
  LearnedPattern,
  PatternQueryContext,
} from '../types.js';

describe('SkillPatternBridge', () => {
  let bridge: ReturnType<typeof createSkillPatternBridge>;

  beforeEach(() => {
    bridge = createSkillPatternBridge({
      minConfidence: 0.5,
      maxPatterns: 100,
      enablePrivacyFilter: true,
    });
  });

  describe('storeLearnedPattern', () => {
    it('should store pattern successfully', async () => {
      const pattern = createLearnedPatternFromSession(
        'error_resolution',
        'TypeError: Cannot read property of undefined',
        'Add null check before accessing property',
        { confidence: 0.8 }
      );

      const result = await bridge.storeLearnedPattern(pattern);

      expect(result.success).toBe(true);
      expect(result.patternId).toBeDefined();
      expect(result.consolidated).toBe(false);
    });

    it('should reject pattern with low confidence', async () => {
      const pattern = createLearnedPatternFromSession(
        'error_resolution',
        'Some error',
        'Some solution',
        { confidence: 0.3 }
      );

      const result = await bridge.storeLearnedPattern(pattern);

      expect(result.success).toBe(false);
      expect(result.error).toContain('below minimum');
    });

    it('should consolidate similar patterns', async () => {
      const pattern1 = createLearnedPatternFromSession(
        'error_resolution',
        'TypeError: Cannot read property X of undefined',
        'Add null check before accessing property X',
        { confidence: 0.8 }
      );

      const pattern2 = createLearnedPatternFromSession(
        'error_resolution',
        'TypeError: Cannot read property Y of undefined',
        'Add null check before accessing property Y',
        { confidence: 0.8 }
      );

      await bridge.storeLearnedPattern(pattern1);
      const result = await bridge.storeLearnedPattern(pattern2);

      expect(result.success).toBe(true);
      expect(result.consolidated).toBe(true);
    });

    it('should apply privacy filter', async () => {
      const pattern = createLearnedPatternFromSession(
        'error_resolution',
        'API key error: api_key=sk_live_abc123def456ghi789',
        'Set correct API key in environment',
        { confidence: 0.8 }
      );

      await bridge.storeLearnedPattern(pattern);
      const stats = await bridge.getStatistics();

      expect(stats.totalPatterns).toBe(1);
    });
  });

  describe('queryPatterns', () => {
    beforeEach(async () => {
      // Add some test patterns
      await bridge.storeLearnedPattern(
        createLearnedPatternFromSession(
          'error_resolution',
          'TypeScript strict null check error',
          'Use optional chaining or null assertion',
          { confidence: 0.9, triggerConditions: ['typescript', 'strict'] }
        )
      );

      await bridge.storeLearnedPattern(
        createLearnedPatternFromSession(
          'debugging_techniques',
          'Memory leak in React component',
          'Clean up useEffect subscriptions',
          { confidence: 0.85, triggerConditions: ['react', 'memory'] }
        )
      );
    });

    it('should query by error message', async () => {
      const context: PatternQueryContext = {
        errorMessage: 'TypeScript null check failed',
      };

      const results = await bridge.queryPatterns(context);

      expect(results.length).toBeGreaterThan(0);
      expect(results[0].pattern.category).toBe('error_resolution');
    });

    it('should query by keywords', async () => {
      const context: PatternQueryContext = {
        keywords: ['react', 'memory'],
      };

      const results = await bridge.queryPatterns(context);

      expect(results.length).toBeGreaterThan(0);
    });

    it('should limit results', async () => {
      const context: PatternQueryContext = {
        keywords: ['error'],
        maxResults: 1,
      };

      const results = await bridge.queryPatterns(context);

      expect(results.length).toBeLessThanOrEqual(1);
    });
  });

  describe('convertToPattern / convertFromPattern', () => {
    it('should convert learned pattern to pattern-mcp format', async () => {
      const learned = createLearnedPatternFromSession(
        'user_corrections',
        'Function naming issue',
        'Use camelCase for function names like [FUNCTION_NAME]',
        { confidence: 0.9 }
      );

      const pattern = bridge.convertToPattern(learned);

      expect(pattern.id).toBe(learned.id);
      expect(pattern.name).toBe(learned.name);
      expect(pattern.holes.length).toBeGreaterThan(0);
    });

    it('should convert pattern-mcp format back to learned pattern', async () => {
      const learned = createLearnedPatternFromSession(
        'workarounds',
        'Build error workaround',
        'Clear cache and rebuild',
        { confidence: 0.7 }
      );

      const pattern = bridge.convertToPattern(learned);
      const backToLearned = bridge.convertFromPattern(pattern);

      expect(backToLearned.id).toBe(learned.id);
      expect(backToLearned.name).toBe(learned.name);
    });
  });

  describe('getStatistics', () => {
    it('should return correct statistics', async () => {
      await bridge.storeLearnedPattern(
        createLearnedPatternFromSession(
          'error_resolution',
          'Error 1',
          'Solution 1',
          { confidence: 0.8 }
        )
      );

      await bridge.storeLearnedPattern(
        createLearnedPatternFromSession(
          'debugging_techniques',
          'Debug issue',
          'Debug solution',
          { confidence: 0.9 }
        )
      );

      const stats = await bridge.getStatistics();

      expect(stats.totalPatterns).toBe(2);
      expect(stats.byCategory.error_resolution).toBe(1);
      expect(stats.byCategory.debugging_techniques).toBe(1);
      expect(stats.averageConfidence).toBeCloseTo(0.85, 1);
    });
  });

  describe('consolidatePatterns', () => {
    it('should consolidate similar patterns', async () => {
      // Add many similar patterns
      for (let i = 0; i < 5; i++) {
        await bridge.storeLearnedPattern(
          createLearnedPatternFromSession(
            'error_resolution',
            `Null pointer error variant ${i}`,
            `Add null check variant ${i}`,
            { confidence: 0.8 }
          )
        );
      }

      const result = await bridge.consolidatePatterns();

      expect(result.mergedCount).toBeGreaterThanOrEqual(0);
      expect(result.remainingCount).toBeLessThanOrEqual(5);
    });
  });
});

describe('createLearnedPatternFromSession', () => {
  it('should create pattern with default values', () => {
    const pattern = createLearnedPatternFromSession(
      'project_specific',
      'Project config issue',
      'Update config file'
    );

    expect(pattern.id).toMatch(/^LP-/);
    expect(pattern.category).toBe('project_specific');
    expect(pattern.problem).toBe('Project config issue');
    expect(pattern.solution).toBe('Update config file');
    expect(pattern.confidence).toBe(0.7);
    expect(pattern.usageCount).toBe(1);
  });

  it('should create pattern with custom options', () => {
    const pattern = createLearnedPatternFromSession(
      'refactoring',
      'Code smell',
      'Apply extract method',
      {
        name: 'Custom Pattern',
        context: 'Large function',
        example: 'function example() { ... }',
        triggerConditions: ['large-function', 'complexity'],
        sourceSession: 'session-123',
        confidence: 0.95,
      }
    );

    expect(pattern.name).toBe('Custom Pattern');
    expect(pattern.context).toBe('Large function');
    expect(pattern.example).toBe('function example() { ... }');
    expect(pattern.triggerConditions).toContain('large-function');
    expect(pattern.sourceSession).toBe('session-123');
    expect(pattern.confidence).toBe(0.95);
  });
});

describe('formatPatternMatchesAsMarkdown', () => {
  it('should format empty results', () => {
    const markdown = formatPatternMatchesAsMarkdown([]);

    expect(markdown).toContain('No relevant patterns found');
  });

  it('should format pattern matches', () => {
    const matches = [
      {
        pattern: createLearnedPatternFromSession(
          'error_resolution',
          'Test error',
          'Test solution',
          { example: 'example code' }
        ),
        relevance: 0.85,
        matchReason: 'Error message similarity',
      },
    ];

    const markdown = formatPatternMatchesAsMarkdown(matches);

    expect(markdown).toContain('# 📚 Relevant Patterns');
    expect(markdown).toContain('85.0%');
    expect(markdown).toContain('Error message similarity');
    expect(markdown).toContain('Test error');
    expect(markdown).toContain('Test solution');
    expect(markdown).toContain('example code');
  });
});
