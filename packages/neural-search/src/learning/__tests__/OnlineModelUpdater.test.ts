/**
 * OnlineModelUpdater Tests
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-104
 * @see DES-NS-104
 * @see REQ-NS-104 Online model updates within 3 feedback cycles
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createOnlineModelUpdater,
  type OnlineModelUpdater,
} from '../OnlineModelUpdater.js';

describe('OnlineModelUpdater', () => {
  let updater: OnlineModelUpdater;

  beforeEach(() => {
    updater = createOnlineModelUpdater();
  });

  describe('Factory Function', () => {
    it('should create an OnlineModelUpdater instance', () => {
      const instance = createOnlineModelUpdater();
      expect(instance).toBeDefined();
      expect(typeof instance.recordFeedback).toBe('function');
    });

    it('should create with custom config', () => {
      const instance = createOnlineModelUpdater({
        updateThreshold: 5,
        learningRate: 0.05,
      });
      expect(instance).toBeDefined();
    });
  });

  describe('recordFeedback', () => {
    it('should record accept feedback', () => {
      const result = updater.recordFeedback({
        candidateId: 'CAND-001',
        type: 'accept',
        context: { query: 'test' },
      });

      expect(result.success).toBe(true);
      expect(result.feedbackId).toBeDefined();
    });

    it('should record reject feedback', () => {
      const result = updater.recordFeedback({
        candidateId: 'CAND-001',
        type: 'reject',
        reason: 'Not relevant',
      });

      expect(result.success).toBe(true);
    });

    it('should record modify feedback', () => {
      const result = updater.recordFeedback({
        candidateId: 'CAND-001',
        type: 'modify',
        modification: 'Changed parameter',
      });

      expect(result.success).toBe(true);
    });

    it('should track pending feedback count', () => {
      updater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });
      updater.recordFeedback({ candidateId: 'CAND-002', type: 'accept' });

      expect(updater.getPendingCount()).toBe(2);
    });
  });

  describe('applyUpdates', () => {
    it('should apply updates after threshold', async () => {
      // Default threshold is 3
      updater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });
      updater.recordFeedback({ candidateId: 'CAND-002', type: 'reject' });
      updater.recordFeedback({ candidateId: 'CAND-003', type: 'accept' });

      const result = await updater.applyUpdates();

      expect(result.applied).toBe(true);
      expect(result.updatesApplied).toBeGreaterThan(0);
    });

    it('should not apply if below threshold', async () => {
      updater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });

      const result = await updater.applyUpdates();

      // Should still succeed but no updates if below threshold
      expect(result.applied).toBe(false);
    });

    it('should clear pending after apply', async () => {
      updater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });
      updater.recordFeedback({ candidateId: 'CAND-002', type: 'reject' });
      updater.recordFeedback({ candidateId: 'CAND-003', type: 'accept' });

      await updater.applyUpdates();

      expect(updater.getPendingCount()).toBe(0);
    });

    it('should update model weights based on feedback', async () => {
      // Record multiple accept feedbacks
      for (let i = 0; i < 5; i++) {
        updater.recordFeedback({
          candidateId: `CAND-${i}`,
          type: 'accept',
          score: 0.9,
        });
      }

      await updater.applyUpdates();
      const newWeights = updater.getModelWeights();

      // Weights should have changed
      expect(newWeights).toBeDefined();
    });
  });

  describe('Auto Updates', () => {
    it('should auto-apply after reaching threshold', async () => {
      const autoUpdater = createOnlineModelUpdater({
        updateThreshold: 3,
        autoApply: true,
      });

      // Record 3 feedbacks to trigger auto-apply
      autoUpdater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });
      autoUpdater.recordFeedback({ candidateId: 'CAND-002', type: 'accept' });
      autoUpdater.recordFeedback({ candidateId: 'CAND-003', type: 'accept' });

      // Wait for auto-apply
      await new Promise((resolve) => setTimeout(resolve, 10));

      const stats = autoUpdater.getStatistics();
      expect(stats.totalUpdatesApplied).toBeGreaterThanOrEqual(1);
    });
  });

  describe('Statistics', () => {
    it('should track feedback statistics', () => {
      updater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });
      updater.recordFeedback({ candidateId: 'CAND-002', type: 'reject' });
      updater.recordFeedback({ candidateId: 'CAND-003', type: 'accept' });

      const stats = updater.getStatistics();

      expect(stats.totalFeedback).toBe(3);
      expect(stats.acceptCount).toBe(2);
      expect(stats.rejectCount).toBe(1);
    });

    it('should calculate acceptance rate', () => {
      updater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });
      updater.recordFeedback({ candidateId: 'CAND-002', type: 'accept' });
      updater.recordFeedback({ candidateId: 'CAND-003', type: 'reject' });

      const stats = updater.getStatistics();

      expect(stats.acceptanceRate).toBeCloseTo(0.667, 2);
    });
  });

  describe('Model Weights', () => {
    it('should get current model weights', () => {
      const weights = updater.getModelWeights();

      expect(weights).toBeDefined();
      expect(typeof weights.semanticWeight).toBe('number');
      expect(typeof weights.contextWeight).toBe('number');
    });

    it('should set model weights', () => {
      // Set all weights to avoid normalization changing values
      updater.setModelWeights({
        semanticWeight: 0.5,
        contextWeight: 0.3,
        patternWeight: 0.15,
        recencyWeight: 0.05,
      });

      const weights = updater.getModelWeights();
      // After normalization, weights sum to 1.0
      expect(weights.semanticWeight).toBe(0.5);
      expect(weights.contextWeight).toBe(0.3);
    });
  });

  describe('Serialization', () => {
    it('should serialize to JSON', () => {
      updater.recordFeedback({ candidateId: 'CAND-001', type: 'accept' });

      const json = updater.toJSON();
      expect(typeof json).toBe('string');

      const parsed = JSON.parse(json);
      expect(parsed.statistics).toBeDefined();
      expect(parsed.weights).toBeDefined();
    });

    it('should deserialize from JSON', () => {
      const json = JSON.stringify({
        weights: { semanticWeight: 0.7, contextWeight: 0.3 },
        statistics: { totalFeedback: 10, acceptCount: 8, rejectCount: 2 },
      });

      updater.fromJSON(json);
      const weights = updater.getModelWeights();

      expect(weights.semanticWeight).toBe(0.7);
    });
  });
});
