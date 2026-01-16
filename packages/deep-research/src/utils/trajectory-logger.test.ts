// Trajectory Logger Tests
// TSK-DR-004

import { describe, it, expect, beforeEach } from 'vitest';
import { TrajectoryLogger } from './trajectory-logger.js';
import type { IterationLog } from '../types/index.js';

describe('TrajectoryLogger', () => {
  let logger: TrajectoryLogger;

  beforeEach(() => {
    logger = new TrajectoryLogger();
  });

  it('should log iterations', () => {
    const log: IterationLog = {
      iteration: 0,
      action: { type: 'search', query: 'test', resultsCount: 5 },
      tokensUsed: 100,
      knowledgeGained: 3,
      timestamp: Date.now(),
    };

    logger.logIteration(log);
    expect(logger.getLogs()).toHaveLength(1);
  });

  it('should track multiple iterations', () => {
    logger.logIteration({
      iteration: 0,
      action: { type: 'search', query: 'q1', resultsCount: 5 },
      tokensUsed: 100,
      knowledgeGained: 2,
      timestamp: Date.now(),
    });

    logger.logIteration({
      iteration: 1,
      action: { type: 'reason', tokensUsed: 200, knowledgeGained: 3 },
      tokensUsed: 200,
      knowledgeGained: 3,
      timestamp: Date.now(),
    });

    expect(logger.getLogs()).toHaveLength(2);
  });

  it('should generate summary statistics', () => {
    logger.logIteration({
      iteration: 0,
      action: { type: 'search', query: 'test', resultsCount: 5 },
      tokensUsed: 100,
      knowledgeGained: 2,
      timestamp: Date.now(),
    });

    logger.logIteration({
      iteration: 1,
      action: { type: 'reason', tokensUsed: 200, knowledgeGained: 3 },
      tokensUsed: 200,
      knowledgeGained: 3,
      timestamp: Date.now(),
    });

    const summary = logger.getSummary();
    expect(summary.totalIterations).toBe(2);
    expect(summary.totalTokens).toBe(300);
    expect(summary.totalKnowledge).toBe(5);
    expect(summary.actions.search).toBe(1);
    expect(summary.actions.reason).toBe(1);
  });

  it('should export as JSON', () => {
    logger.logIteration({
      iteration: 0,
      action: { type: 'search', query: 'test', resultsCount: 5 },
      tokensUsed: 100,
      knowledgeGained: 2,
      timestamp: Date.now(),
    });

    const json = logger.export('json');
    expect(typeof json).toBe('string');
    
    const parsed = JSON.parse(json);
    expect(parsed).toHaveLength(1);
    expect(parsed[0].iteration).toBe(0);
  });

  it('should throw error for Parquet export (not yet implemented)', () => {
    expect(() => logger.export('parquet')).toThrow('not yet implemented');
  });

  it('should clear logs', () => {
    logger.logIteration({
      iteration: 0,
      action: { type: 'search', query: 'test', resultsCount: 5 },
      tokensUsed: 100,
      knowledgeGained: 2,
      timestamp: Date.now(),
    });

    expect(logger.getLogs()).toHaveLength(1);
    logger.clear();
    expect(logger.getLogs()).toHaveLength(0);
  });
});
