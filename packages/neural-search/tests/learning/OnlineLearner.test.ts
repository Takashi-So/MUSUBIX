/**
 * Online Learner Tests
 * @module @nahisaho/musubix-neural-search
 * Traces to: REQ-NS-004 (探索履歴学習)
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { OnlineLearner } from '../../src/learning/OnlineLearner.js';
import type { SearchTrajectory, TrajectoryStep } from '../../src/types.js';

describe('OnlineLearner', () => {
  let learner: OnlineLearner;

  beforeEach(() => {
    learner = new OnlineLearner();
  });

  // Helper to create trajectory
  function createTrajectory(
    id: string,
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
        score: finalScore,
        action: 'refine',
        duration: 150,
      },
    ];

    return {
      id,
      specification: 'test spec',
      path: steps,
      outcome: {
        success,
        finalScore,
      },
      timestamp: new Date(),
    };
  }

  describe('learnFromTrajectory', () => {
    it('should return learning update', () => {
      const trajectory = createTrajectory('t1', true);

      const update = learner.learnFromTrajectory(trajectory);

      expect(update.trajectoryId).toBe('t1');
      expect(update.gradients).toBeDefined();
      expect(update.loss).toBeGreaterThanOrEqual(0);
    });

    it('should compute gradients for parameters', () => {
      const trajectory = createTrajectory('t1', true);

      const update = learner.learnFromTrajectory(trajectory);

      expect(update.gradients.has('specAlignment')).toBe(true);
      expect(update.gradients.has('codeQuality')).toBe(true);
    });

    it('should compute higher loss for failure', () => {
      // For cross-entropy loss:
      // Success with high score → low loss
      // Failure with high score → high loss (because model predicted success but outcome was failure)
      const successTrajectory = createTrajectory('t1', true, 0.9);
      const failTrajectory = createTrajectory('t2', false, 0.9); // High score but failed = high loss

      const successUpdate = learner.learnFromTrajectory(successTrajectory);
      const failUpdate = learner.learnFromTrajectory(failTrajectory);

      expect(failUpdate.loss).toBeGreaterThan(successUpdate.loss);
    });

    it('should increment total updates', () => {
      const initial = learner.getStatistics().totalUpdates;

      learner.learnFromTrajectory(createTrajectory('t1', true));
      learner.learnFromTrajectory(createTrajectory('t2', false));

      expect(learner.getStatistics().totalUpdates).toBe(initial + 2);
    });
  });

  describe('getParameters', () => {
    it('should return initial parameters', () => {
      const params = learner.getParameters();

      expect(params.get('specAlignment')).toBe(0.4);
      expect(params.get('codeQuality')).toBe(0.3);
      expect(params.get('novelty')).toBe(0.15);
      expect(params.get('feasibility')).toBe(0.15);
    });

    it('should return copy of parameters', () => {
      const params1 = learner.getParameters();
      const params2 = learner.getParameters();

      expect(params1).not.toBe(params2);
    });
  });

  describe('applyUpdate', () => {
    it('should update parameters', () => {
      const initialParams = learner.getParameters();
      const initialSpec = initialParams.get('specAlignment')!;

      const update = {
        trajectoryId: 't1',
        gradients: new Map([['specAlignment', 0.1]]),
        loss: 0.5,
      };

      learner.applyUpdate(update);

      const newParams = learner.getParameters();
      expect(newParams.get('specAlignment')).not.toBe(initialSpec);
    });

    it('should respect gradient clipping', () => {
      const learnerWithClip = new OnlineLearner({ gradientClip: 0.01 });
      const initialParams = learnerWithClip.getParameters();
      const initialSpec = initialParams.get('specAlignment')!;

      // Very large gradient
      const update = {
        trajectoryId: 't1',
        gradients: new Map([['specAlignment', 1000]]),
        loss: 0.5,
      };

      learnerWithClip.applyUpdate(update);

      const newParams = learnerWithClip.getParameters();
      const change = Math.abs(newParams.get('specAlignment')! - initialSpec);

      // Change should be small due to clipping
      expect(change).toBeLessThan(0.1);
    });

    it('should apply multiple updates', () => {
      const trajectory = createTrajectory('t1', true);

      for (let i = 0; i < 5; i++) {
        const update = learner.learnFromTrajectory(trajectory);
        learner.applyUpdate(update);
      }

      // Parameters should have changed
      const params = learner.getParameters();
      expect(params.get('specAlignment')).not.toBe(0.4);
    });
  });

  describe('getStatistics', () => {
    it('should return learning statistics', () => {
      const stats = learner.getStatistics();

      expect(stats).toHaveProperty('totalUpdates');
      expect(stats).toHaveProperty('averageLoss');
      expect(stats).toHaveProperty('learningRate');
      expect(stats).toHaveProperty('convergenceMetric');
    });

    it('should track average loss', () => {
      learner.learnFromTrajectory(createTrajectory('t1', true, 0.9));
      learner.learnFromTrajectory(createTrajectory('t2', true, 0.8));

      const stats = learner.getStatistics();

      expect(stats.averageLoss).toBeGreaterThan(0);
    });

    it('should compute convergence metric', () => {
      // Similar losses should give higher convergence
      for (let i = 0; i < 10; i++) {
        learner.learnFromTrajectory(createTrajectory(`t${i}`, true, 0.8));
      }

      const stats = learner.getStatistics();

      expect(stats.convergenceMetric).toBeGreaterThan(0);
      expect(stats.convergenceMetric).toBeLessThanOrEqual(1);
    });
  });

  describe('reset', () => {
    it('should reset to initial state', () => {
      // Make some changes
      learner.learnFromTrajectory(createTrajectory('t1', true));
      const update = learner.learnFromTrajectory(createTrajectory('t2', false));
      learner.applyUpdate(update);

      // Reset
      learner.reset();

      // Should be back to initial
      const params = learner.getParameters();
      expect(params.get('specAlignment')).toBe(0.4);

      const stats = learner.getStatistics();
      expect(stats.totalUpdates).toBe(0);
    });
  });

  describe('configuration', () => {
    it('should use custom learning rate', () => {
      const customLearner = new OnlineLearner({ learningRate: 0.1 });

      const stats = customLearner.getStatistics();
      expect(stats.learningRate).toBe(0.1);
    });

    it('should use custom momentum decay', () => {
      const customLearner = new OnlineLearner({ momentumDecay: 0.5 });

      // Apply updates and check momentum effect
      const trajectory = createTrajectory('t1', true);
      const update1 = customLearner.learnFromTrajectory(trajectory);
      customLearner.applyUpdate(update1);

      // Should work without error
      expect(customLearner.getParameters()).toBeDefined();
    });
  });
});
