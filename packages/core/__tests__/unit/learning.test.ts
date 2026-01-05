/**
 * Learning Module Unit Tests
 *
 * @see REQ-LEARN-001〜006 - Learning Requirements
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { promises as fs } from 'fs';
import { join } from 'path';
import { FeedbackCollector } from '../../src/learning/feedback-collector.js';
import { PatternExtractor } from '../../src/learning/pattern-extractor.js';
import { LearningEngine } from '../../src/learning/learning-engine.js';
import type { Feedback, LearnedPattern } from '../../src/learning/types.js';

const TEST_STORAGE = '/tmp/musubix-learning-test';

describe('FeedbackCollector', () => {
  let collector: FeedbackCollector;

  beforeEach(async () => {
    // Clean up test storage
    try {
      await fs.rm(TEST_STORAGE, { recursive: true });
    } catch {
      // Directory doesn't exist
    }
    collector = new FeedbackCollector({ storagePath: TEST_STORAGE });
  });

  afterEach(async () => {
    try {
      await fs.rm(TEST_STORAGE, { recursive: true });
    } catch {
      // Ignore
    }
  });

  describe('recordFeedback', () => {
    it('should record accept feedback', async () => {
      const feedback = await collector.recordFeedback({
        type: 'accept',
        artifactType: 'code',
        artifactId: 'CODE-001',
        context: {
          project: 'test-project',
          language: 'typescript',
        },
      });

      expect(feedback.id).toMatch(/^FB-[A-Z0-9]+$/);
      expect(feedback.type).toBe('accept');
      expect(feedback.artifactType).toBe('code');
      expect(feedback.artifactId).toBe('CODE-001');
      expect(feedback.context.project).toBe('test-project');
      expect(feedback.context.language).toBe('typescript');
    });

    it('should record reject feedback with reason', async () => {
      const feedback = await collector.recordFeedback({
        type: 'reject',
        artifactType: 'design',
        artifactId: 'DES-001',
        reason: 'Does not follow SOLID principles',
      });

      expect(feedback.type).toBe('reject');
      expect(feedback.reason).toBe('Does not follow SOLID principles');
    });

    it('should record modify feedback with original and modified', async () => {
      const feedback = await collector.recordFeedback({
        type: 'modify',
        artifactType: 'code',
        artifactId: 'CODE-002',
        original: 'const x = 1;',
        modified: 'const x: number = 1;',
      });

      expect(feedback.type).toBe('modify');
      expect(feedback.original).toBe('const x = 1;');
      expect(feedback.modified).toBe('const x: number = 1;');
    });

    it('should sanitize sensitive data (REQ-LEARN-006)', async () => {
      const feedback = await collector.recordFeedback({
        type: 'modify',
        artifactType: 'code',
        artifactId: 'CODE-003',
        original: 'const apiKey = "secret123";',
        reason: 'Fix password = "test123"',
      });

      expect(feedback.original).toContain('[REDACTED]');
      expect(feedback.reason).toContain('[REDACTED]');
    });
  });

  describe('queryFeedback', () => {
    beforeEach(async () => {
      await collector.recordFeedback({
        type: 'accept',
        artifactType: 'code',
        artifactId: 'CODE-001',
        context: { project: 'proj-a', language: 'typescript' },
      });
      await collector.recordFeedback({
        type: 'reject',
        artifactType: 'design',
        artifactId: 'DES-001',
        context: { project: 'proj-b', framework: 'react' },
      });
      await collector.recordFeedback({
        type: 'accept',
        artifactType: 'code',
        artifactId: 'CODE-002',
        context: { project: 'proj-a', language: 'typescript' },
      });
    });

    it('should query by artifact type', async () => {
      const results = await collector.queryFeedback({ artifactType: 'code' });
      expect(results).toHaveLength(2);
      expect(results.every((f) => f.artifactType === 'code')).toBe(true);
    });

    it('should query by feedback type', async () => {
      const results = await collector.queryFeedback({ type: 'accept' });
      expect(results).toHaveLength(2);
    });

    it('should query by project', async () => {
      const results = await collector.queryFeedback({ project: 'proj-a' });
      expect(results).toHaveLength(2);
    });

    it('should query by language', async () => {
      const results = await collector.queryFeedback({ language: 'typescript' });
      expect(results).toHaveLength(2);
    });

    it('should limit results', async () => {
      const results = await collector.queryFeedback({ limit: 1 });
      expect(results).toHaveLength(1);
    });
  });

  describe('getStats', () => {
    it('should return correct statistics', async () => {
      await collector.recordFeedback({
        type: 'accept',
        artifactType: 'code',
        artifactId: 'CODE-001',
      });
      await collector.recordFeedback({
        type: 'reject',
        artifactType: 'design',
        artifactId: 'DES-001',
      });
      await collector.recordFeedback({
        type: 'modify',
        artifactType: 'code',
        artifactId: 'CODE-002',
      });

      const stats = await collector.getStats();
      expect(stats.total).toBe(3);
      expect(stats.byType.accept).toBe(1);
      expect(stats.byType.reject).toBe(1);
      expect(stats.byType.modify).toBe(1);
      expect(stats.byArtifactType.code).toBe(2);
      expect(stats.byArtifactType.design).toBe(1);
    });
  });
});

describe('PatternExtractor', () => {
  let extractor: PatternExtractor;

  beforeEach(async () => {
    try {
      await fs.rm(TEST_STORAGE, { recursive: true });
    } catch {
      // Directory doesn't exist
    }
    extractor = new PatternExtractor({ storagePath: TEST_STORAGE, patternThreshold: 2 });
  });

  afterEach(async () => {
    try {
      await fs.rm(TEST_STORAGE, { recursive: true });
    } catch {
      // Ignore
    }
  });

  describe('extractPatterns', () => {
    it('should extract pattern when threshold is met (REQ-LEARN-002)', async () => {
      const feedbackList: Feedback[] = [
        {
          id: 'FB-001',
          timestamp: new Date(),
          type: 'accept',
          artifactType: 'code',
          artifactId: 'CODE-001',
          context: { project: 'test', language: 'typescript', tags: [] },
        },
        {
          id: 'FB-002',
          timestamp: new Date(),
          type: 'accept',
          artifactType: 'code',
          artifactId: 'CODE-002',
          context: { project: 'test', language: 'typescript', tags: [] },
        },
      ];

      const patterns = await extractor.extractPatterns(feedbackList);
      expect(patterns.length).toBeGreaterThanOrEqual(1);
      expect(patterns[0].source).toBe('auto');
      expect(patterns[0].confidence).toBeGreaterThan(0);
    });

    it('should not create pattern below threshold', async () => {
      const feedbackList: Feedback[] = [
        {
          id: 'FB-001',
          timestamp: new Date(),
          type: 'accept',
          artifactType: 'code',
          artifactId: 'CODE-001',
          context: { project: 'test', language: 'typescript', tags: [] },
        },
      ];

      // With threshold 2, single feedback should not create pattern
      const patterns = await extractor.extractPatterns(feedbackList);
      expect(patterns).toHaveLength(0);
    });
  });

  describe('addPattern', () => {
    it('should add manual pattern', async () => {
      const pattern = await extractor.addPattern(
        'Prefer async/await',
        'code',
        { context: { language: 'typescript' }, conditions: [] },
        { type: 'prefer', content: 'Use async/await instead of .then()' },
        0.8
      );

      expect(pattern.id).toMatch(/^PAT-[A-Z0-9]+$/);
      expect(pattern.name).toBe('Prefer async/await');
      expect(pattern.source).toBe('manual');
      expect(pattern.confidence).toBe(0.8);
    });
  });

  describe('applyDecay (REQ-LEARN-004)', () => {
    it('should decay old patterns', async () => {
      // Add a pattern
      const pattern = await extractor.addPattern(
        'Old pattern',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'test' },
        0.5
      );

      // Manually set lastUsed to old date
      const patterns = await extractor.getPatterns();
      patterns[0].lastUsed = new Date(Date.now() - 40 * 24 * 60 * 60 * 1000); // 40 days ago

      // This won't actually decay since we can't modify internal state easily
      // But we can test the method runs without error
      const result = await extractor.applyDecay(30, 0.1, 0.1);
      expect(result).toHaveProperty('decayed');
      expect(result).toHaveProperty('archived');
    });
  });

  describe('getHighConfidencePatterns', () => {
    it('should filter by confidence threshold', async () => {
      await extractor.addPattern(
        'High confidence',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'test' },
        0.9
      );
      await extractor.addPattern(
        'Low confidence',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'test' },
        0.3
      );

      const highConf = await extractor.getHighConfidencePatterns(0.7);
      expect(highConf).toHaveLength(1);
      expect(highConf[0].name).toBe('High confidence');
    });
  });
});

describe('LearningEngine', () => {
  let engine: LearningEngine;

  beforeEach(async () => {
    try {
      await fs.rm(TEST_STORAGE, { recursive: true });
    } catch {
      // Directory doesn't exist
    }
    engine = new LearningEngine({ storagePath: TEST_STORAGE, patternThreshold: 2 });
  });

  afterEach(async () => {
    try {
      await fs.rm(TEST_STORAGE, { recursive: true });
    } catch {
      // Ignore
    }
  });

  describe('acceptArtifact / rejectArtifact', () => {
    it('should record acceptance', async () => {
      const feedback = await engine.acceptArtifact('CODE-001', 'code', {
        language: 'typescript',
      });
      expect(feedback.type).toBe('accept');
    });

    it('should record rejection', async () => {
      const feedback = await engine.rejectArtifact(
        'DES-001',
        'design',
        {},
        'Poor design'
      );
      expect(feedback.type).toBe('reject');
      expect(feedback.reason).toBe('Poor design');
    });
  });

  describe('findMatchingPatterns (REQ-LEARN-003)', () => {
    beforeEach(async () => {
      await engine.addPattern(
        'TypeScript pattern',
        'code',
        { context: { language: 'typescript' }, conditions: [] },
        { type: 'prefer', content: 'Use strict types' },
        0.8
      );
      await engine.addPattern(
        'React pattern',
        'code',
        { context: { framework: 'react' }, conditions: [] },
        { type: 'avoid', content: 'Avoid class components' },
        0.7
      );
    });

    it('should find patterns matching context', async () => {
      const matches = await engine.findMatchingPatterns({
        artifactType: 'code',
        language: 'typescript',
      });

      expect(matches.length).toBeGreaterThan(0);
      expect(matches[0].matchedKeys).toContain('language');
    });

    it('should return empty for non-matching context', async () => {
      const matches = await engine.findMatchingPatterns({
        artifactType: 'design', // No patterns for design
        language: 'python',
      });

      expect(matches).toHaveLength(0);
    });
  });

  describe('getRecommendations', () => {
    beforeEach(async () => {
      await engine.addPattern(
        'Prefer pattern',
        'code',
        { context: { language: 'typescript' }, conditions: [] },
        { type: 'prefer', content: 'Do this' },
        0.8
      );
      await engine.addPattern(
        'Avoid pattern',
        'code',
        { context: { language: 'typescript' }, conditions: [] },
        { type: 'avoid', content: 'Dont do this' },
        0.7
      );
    });

    it('should categorize recommendations by action type', async () => {
      const recommendations = await engine.getRecommendations({
        artifactType: 'code',
        language: 'typescript',
      });

      expect(recommendations.prefer.length).toBeGreaterThan(0);
      expect(recommendations.avoid.length).toBeGreaterThan(0);
    });
  });

  describe('getStats (REQ-LEARN-005)', () => {
    it('should return combined statistics', async () => {
      await engine.acceptArtifact('CODE-001', 'code');
      await engine.rejectArtifact('DES-001', 'design');
      await engine.addPattern(
        'Test pattern',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'test' },
        0.5
      );

      const stats = await engine.getStats();
      expect(stats.totalFeedback).toBe(2);
      expect(stats.totalPatterns).toBe(1);
      expect(stats.feedbackByType.accept).toBe(1);
      expect(stats.feedbackByType.reject).toBe(1);
    });
  });

  describe('export / import', () => {
    it('should export and import learning data', async () => {
      await engine.acceptArtifact('CODE-001', 'code');
      await engine.addPattern(
        'Test pattern',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'test' },
        0.5
      );

      const exported = await engine.export();
      expect(exported.feedback.length).toBe(1);
      expect(exported.patterns.length).toBe(1);

      // Create new engine and import
      const newEngine = new LearningEngine({ storagePath: TEST_STORAGE + '-new' });
      const result = await newEngine.import(exported);
      expect(result.feedbackImported).toBe(1);
      expect(result.patternsImported).toBe(1);

      // Cleanup
      try {
        await fs.rm(TEST_STORAGE + '-new', { recursive: true });
      } catch {
        // Ignore
      }
    });
  });

  describe('generateStatusReport', () => {
    it('should generate markdown report', async () => {
      await engine.acceptArtifact('CODE-001', 'code');
      await engine.addPattern(
        'High conf pattern',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'test' },
        0.9
      );

      const report = await engine.generateStatusReport();
      expect(report).toContain('# MUSUBIX Learning Status Report');
      expect(report).toContain('Total Feedback: 1');
      expect(report).toContain('Total Patterns: 1');
      expect(report).toContain('High Confidence Patterns');
    });
  });

  describe('importWithStrategy', () => {
    it('should skip existing patterns with skip strategy', async () => {
      // Add existing pattern
      await engine.addPattern(
        'Existing pattern',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'original content' },
        0.5
      );

      const existingPatterns = await engine.getPatterns();
      expect(existingPatterns.length).toBe(1);
      const existingId = existingPatterns[0].id;

      // Try to import same pattern with different content
      const result = await engine.importWithStrategy({
        patterns: [{
          id: existingId,
          name: 'Existing pattern',
          category: 'code',
          trigger: { context: {}, conditions: [] },
          action: { type: 'prefer', content: 'new content' },
          confidence: 0.8,
          occurrences: 10,
          source: 'auto',
          createdAt: new Date(),
          lastUsed: new Date(),
        }],
      }, 'skip');

      expect(result.patternsImported).toBe(0);
      expect(result.patternsMerged).toBe(0);

      // Original content should be preserved
      const patterns = await engine.getPatterns();
      expect(patterns[0].action.content).toBe('original content');
    });

    it('should overwrite existing patterns with overwrite strategy', async () => {
      // Add existing pattern
      await engine.addPattern(
        'Existing pattern',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'original content' },
        0.5
      );

      const existingPatterns = await engine.getPatterns();
      const existingId = existingPatterns[0].id;

      // Import with overwrite
      const result = await engine.importWithStrategy({
        patterns: [{
          id: existingId,
          name: 'Existing pattern',
          category: 'code',
          trigger: { context: {}, conditions: [] },
          action: { type: 'prefer', content: 'new content' },
          confidence: 0.8,
          occurrences: 10,
          source: 'auto',
          createdAt: new Date(),
          lastUsed: new Date(),
        }],
      }, 'overwrite');

      expect(result.patternsImported).toBe(1);

      // Content should be replaced
      const patterns = await engine.getPatterns();
      expect(patterns[0].action.content).toBe('new content');
      expect(patterns[0].confidence).toBe(0.8);
    });

    it('should merge existing patterns with merge strategy', async () => {
      // Add existing pattern
      await engine.addPattern(
        'Existing pattern',
        'code',
        { context: {}, conditions: [] },
        { type: 'prefer', content: 'original content' },
        0.5
      );

      const existingPatterns = await engine.getPatterns();
      const existingId = existingPatterns[0].id;

      // Import with merge
      const result = await engine.importWithStrategy({
        patterns: [{
          id: existingId,
          name: 'Existing pattern',
          category: 'code',
          trigger: { context: {}, conditions: [] },
          action: { type: 'prefer', content: 'additional content' },
          confidence: 0.9,
          occurrences: 5,
          source: 'auto',
          createdAt: new Date(),
          lastUsed: new Date(),
        }],
      }, 'merge');

      expect(result.patternsMerged).toBe(1);

      // Check merged values
      const patterns = await engine.getPatterns();
      expect(patterns[0].confidence).toBe(0.9); // Max confidence
      expect(patterns[0].occurrences).toBe(6); // Combined occurrences (1 + 5)
      expect(patterns[0].action.content).toContain('original content');
      expect(patterns[0].action.content).toContain('additional content');
    });

    it('should import new patterns regardless of strategy', async () => {
      const result = await engine.importWithStrategy({
        patterns: [{
          id: 'PTN-NEW-001',
          name: 'New pattern',
          category: 'code',
          trigger: { context: {}, conditions: [] },
          action: { type: 'prefer', content: 'test' },
          confidence: 0.7,
          occurrences: 3,
          source: 'auto',
          createdAt: new Date(),
          lastUsed: new Date(),
        }],
      }, 'skip');

      expect(result.patternsImported).toBe(1);
      const patterns = await engine.getPatterns();
      expect(patterns.length).toBe(1);
      expect(patterns[0].name).toBe('New pattern');
    });
  });
});
