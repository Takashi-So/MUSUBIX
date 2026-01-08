/**
 * Trajectory Log Tests
 * @module @nahisaho/musubix-neural-search
 * Traces to: REQ-NS-004 (探索履歴学習)
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { TrajectoryLog } from '../../src/learning/TrajectoryLog.js';
import type { SearchTrajectory, TrajectoryStep } from '../../src/types.js';

describe('TrajectoryLog', () => {
  let log: TrajectoryLog;

  beforeEach(() => {
    log = new TrajectoryLog();
  });

  // Helper to create trajectory
  function createTrajectory(
    id: string,
    spec: string,
    success: boolean,
    finalScore: number = 0.8
  ): SearchTrajectory {
    const steps: TrajectoryStep[] = [
      {
        state: { id: `${id}-s1`, code: 'step1', depth: 1, metadata: {} },
        score: 0.5,
        action: 'generate',
        duration: 100,
      },
      {
        state: { id: `${id}-s2`, code: 'step2', depth: 2, metadata: {} },
        score: 0.7,
        action: 'refine',
        duration: 150,
      },
    ];

    return {
      id,
      specification: spec,
      path: steps,
      outcome: {
        success,
        finalScore,
        reason: success ? 'completed' : 'failed',
      },
      timestamp: new Date(),
    };
  }

  describe('log', () => {
    it('should log trajectory', () => {
      const trajectory = createTrajectory('t1', 'Create a function', true);

      log.log(trajectory);

      expect(log.size()).toBe(1);
    });

    it('should store multiple trajectories', () => {
      log.log(createTrajectory('t1', 'spec1', true));
      log.log(createTrajectory('t2', 'spec2', false));
      log.log(createTrajectory('t3', 'spec3', true));

      expect(log.size()).toBe(3);
    });
  });

  describe('get', () => {
    it('should retrieve trajectory by ID', () => {
      const trajectory = createTrajectory('t1', 'Create a function', true);
      log.log(trajectory);

      const retrieved = log.get('t1');

      expect(retrieved).toBeDefined();
      expect(retrieved?.specification).toBe('Create a function');
    });

    it('should return undefined for unknown ID', () => {
      expect(log.get('unknown')).toBeUndefined();
    });
  });

  describe('queryBySpec', () => {
    it('should find trajectories by specification', () => {
      log.log(createTrajectory('t1', 'Create a function', true));
      log.log(createTrajectory('t2', 'Create a function', false));
      log.log(createTrajectory('t3', 'Build a class', true));

      const results = log.queryBySpec('Create a function');

      expect(results.length).toBe(2);
    });

    it('should be case insensitive', () => {
      log.log(createTrajectory('t1', 'Create a Function', true));

      const results = log.queryBySpec('create a function');

      expect(results.length).toBe(1);
    });

    it('should respect limit', () => {
      log.log(createTrajectory('t1', 'spec', true));
      log.log(createTrajectory('t2', 'spec', false));
      log.log(createTrajectory('t3', 'spec', true));

      const results = log.queryBySpec('spec', 2);

      expect(results.length).toBe(2);
    });

    it('should return empty for no matches', () => {
      log.log(createTrajectory('t1', 'something', true));

      const results = log.queryBySpec('else');

      expect(results.length).toBe(0);
    });
  });

  describe('getSuccessful', () => {
    it('should return only successful trajectories', () => {
      log.log(createTrajectory('t1', 'spec1', true, 0.9));
      log.log(createTrajectory('t2', 'spec2', false, 0.3));
      log.log(createTrajectory('t3', 'spec3', true, 0.8));

      const successful = log.getSuccessful();

      expect(successful.length).toBe(2);
      expect(successful.every((t) => t.outcome.success)).toBe(true);
    });

    it('should sort by final score', () => {
      log.log(createTrajectory('t1', 'spec1', true, 0.7));
      log.log(createTrajectory('t2', 'spec2', true, 0.9));
      log.log(createTrajectory('t3', 'spec3', true, 0.8));

      const successful = log.getSuccessful();

      expect(successful[0].outcome.finalScore).toBe(0.9);
      expect(successful[1].outcome.finalScore).toBe(0.8);
      expect(successful[2].outcome.finalScore).toBe(0.7);
    });

    it('should respect limit', () => {
      log.log(createTrajectory('t1', 'spec1', true));
      log.log(createTrajectory('t2', 'spec2', true));
      log.log(createTrajectory('t3', 'spec3', true));

      const successful = log.getSuccessful(2);

      expect(successful.length).toBe(2);
    });
  });

  describe('getAll', () => {
    it('should return all trajectories', () => {
      log.log(createTrajectory('t1', 'spec1', true));
      log.log(createTrajectory('t2', 'spec2', false));

      const all = log.getAll();

      expect(all.length).toBe(2);
    });

    it('should return empty array for empty log', () => {
      expect(log.getAll()).toEqual([]);
    });
  });

  describe('getStatistics', () => {
    it('should calculate success rate', () => {
      log.log(createTrajectory('t1', 'spec1', true));
      log.log(createTrajectory('t2', 'spec2', true));
      log.log(createTrajectory('t3', 'spec3', false));
      log.log(createTrajectory('t4', 'spec4', true));

      const stats = log.getStatistics();

      expect(stats.totalTrajectories).toBe(4);
      expect(stats.successRate).toBeCloseTo(0.75, 2);
    });

    it('should calculate average length', () => {
      log.log(createTrajectory('t1', 'spec1', true)); // 2 steps
      log.log(createTrajectory('t2', 'spec2', true)); // 2 steps

      const stats = log.getStatistics();

      expect(stats.averageLength).toBe(2);
    });

    it('should calculate average duration', () => {
      log.log(createTrajectory('t1', 'spec1', true)); // 100 + 150 = 250ms
      log.log(createTrajectory('t2', 'spec2', true)); // 100 + 150 = 250ms

      const stats = log.getStatistics();

      expect(stats.averageDuration).toBe(250); // 500 / 2
    });

    it('should handle empty log', () => {
      const stats = log.getStatistics();

      expect(stats.totalTrajectories).toBe(0);
      expect(stats.successRate).toBe(0);
      expect(stats.averageLength).toBe(0);
      expect(stats.averageDuration).toBe(0);
    });
  });

  describe('clear', () => {
    it('should remove all trajectories', () => {
      log.log(createTrajectory('t1', 'spec1', true));
      log.log(createTrajectory('t2', 'spec2', false));

      log.clear();

      expect(log.size()).toBe(0);
      expect(log.getAll()).toEqual([]);
    });
  });

  describe('size', () => {
    it('should return correct size', () => {
      expect(log.size()).toBe(0);

      log.log(createTrajectory('t1', 'spec1', true));
      expect(log.size()).toBe(1);

      log.log(createTrajectory('t2', 'spec2', false));
      expect(log.size()).toBe(2);
    });
  });
});
