/**
 * ComplexityAnalyzer Domain Service Tests
 * 
 * @see REQ-SDD-001 - Task Complexity Evaluation
 * @see DES-SDD-001 - ComplexityAnalyzer
 */

import { describe, it, expect } from 'vitest';
import {
  createComplexityAnalyzer,
  type IComplexityAnalyzer,
} from '../../src/domain/services/ComplexityAnalyzer.js';
import {
  createTask,
  type Task,
} from '../../src/domain/entities/Task.js';

describe('ComplexityAnalyzer', () => {
  // Helper to create test tasks
  const createSimpleTask = (): Task => createTask({
    id: 'TSK-001',
    title: 'Fix typo in README.md',
    description: 'Fix a simple typo',
    priority: 'low',
    estimatedScope: 1,
    dependencyCount: 0,
    estimatedFileCount: 1,
    testCoverageRequired: 0,
    uncertaintyLevel: 1,
  });

  const createComplexTask = (): Task => createTask({
    id: 'TSK-002',
    title: 'Implement full authentication system',
    description: 'OAuth2, JWT, MFA integration',
    priority: 'critical',
    estimatedScope: 10,
    dependencyCount: 8,
    estimatedFileCount: 15,
    testCoverageRequired: 100,
    uncertaintyLevel: 9,
  });

  describe('createComplexityAnalyzer', () => {
    it('should create analyzer with default config', () => {
      const analyzer = createComplexityAnalyzer();
      expect(analyzer).toBeDefined();
      expect(analyzer.analyze).toBeInstanceOf(Function);
      expect(analyzer.shouldDecompose).toBeInstanceOf(Function);
      expect(analyzer.getRecommendation).toBeInstanceOf(Function);
    });

    it('should accept custom threshold', () => {
      const analyzer = createComplexityAnalyzer({ threshold: 5 });
      expect(analyzer).toBeDefined();
    });
  });

  describe('analyze', () => {
    it('should analyze simple task as low complexity', () => {
      const analyzer = createComplexityAnalyzer();
      const task = createSimpleTask();
      const score = analyzer.analyze(task);

      expect(score).toBeDefined();
      expect(score.value).toBeLessThan(5);
      expect(score.factors).toBeDefined();
    });

    it('should analyze complex task as high complexity', () => {
      const analyzer = createComplexityAnalyzer();
      const task = createComplexTask();
      const score = analyzer.analyze(task);

      expect(score.value).toBeGreaterThan(6);
    });
  });

  describe('shouldDecompose', () => {
    it('should recommend decomposition for high complexity', () => {
      const analyzer = createComplexityAnalyzer({ threshold: 6 });
      const task = createComplexTask();
      const score = analyzer.analyze(task);

      expect(analyzer.shouldDecompose(score)).toBe(true);
    });

    it('should not recommend decomposition for low complexity', () => {
      const analyzer = createComplexityAnalyzer({ threshold: 6 });
      const task = createSimpleTask();
      const score = analyzer.analyze(task);

      expect(analyzer.shouldDecompose(score)).toBe(false);
    });
  });

  describe('getRecommendation', () => {
    it('should return recommendation with reasoning', () => {
      const analyzer = createComplexityAnalyzer();
      const task = createComplexTask();
      const recommendation = analyzer.getRecommendation(task);

      expect(recommendation).toBeDefined();
      expect(recommendation.shouldDecompose).toBe(true);
      expect(recommendation.score).toBeDefined();
      expect(recommendation.reasoning).toBeTruthy();
      expect(recommendation.suggestedSubtaskCount).toBeGreaterThan(0);
      expect(recommendation.primaryFactors).toHaveLength(3);
    });

    it('should not recommend decomposition for simple task', () => {
      const analyzer = createComplexityAnalyzer();
      const task = createSimpleTask();
      const recommendation = analyzer.getRecommendation(task);

      expect(recommendation.shouldDecompose).toBe(false);
      expect(recommendation.suggestedSubtaskCount).toBeLessThanOrEqual(2);
    });
  });
});
