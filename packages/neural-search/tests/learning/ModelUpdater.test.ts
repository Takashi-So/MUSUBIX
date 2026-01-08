/**
 * Model Updater Tests
 * @module @nahisaho/musubix-neural-search
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import { ModelUpdater } from '../../src/learning/ModelUpdater.js';
import type { LearningUpdate } from '../../src/types.js';

describe('ModelUpdater', () => {
  let updater: ModelUpdater;

  beforeEach(() => {
    vi.useFakeTimers();
    updater = new ModelUpdater();
  });

  afterEach(() => {
    updater.clear();
    vi.useRealTimers();
  });

  // Helper to create update
  function createUpdate(id: string): LearningUpdate {
    return {
      trajectoryId: id,
      gradients: new Map([['param', Math.random()]]),
      loss: Math.random(),
    };
  }

  describe('queueUpdate', () => {
    it('should queue update', () => {
      updater.queueUpdate(createUpdate('u1'));

      expect(updater.getPendingCount()).toBe(1);
    });

    it('should queue multiple updates', () => {
      updater.queueUpdate(createUpdate('u1'));
      updater.queueUpdate(createUpdate('u2'));
      updater.queueUpdate(createUpdate('u3'));

      expect(updater.getPendingCount()).toBe(3);
    });
  });

  describe('auto-flush on batch size', () => {
    it('should flush when batch size reached', async () => {
      const flushed: LearningUpdate[][] = [];
      const updaterWithHandler = new ModelUpdater(
        { batchSize: 3 },
        async (updates) => {
          flushed.push(updates);
        }
      );

      updaterWithHandler.queueUpdate(createUpdate('u1'));
      updaterWithHandler.queueUpdate(createUpdate('u2'));
      updaterWithHandler.queueUpdate(createUpdate('u3'));

      // Wait for async flush
      await vi.runAllTimersAsync();

      expect(flushed.length).toBe(1);
      expect(flushed[0].length).toBe(3);
      expect(updaterWithHandler.getPendingCount()).toBe(0);

      updaterWithHandler.clear();
    });
  });

  describe('flushUpdates', () => {
    it('should flush pending updates', async () => {
      const flushed: LearningUpdate[][] = [];
      const updaterWithHandler = new ModelUpdater({}, async (updates) => {
        flushed.push(updates);
      });

      updaterWithHandler.queueUpdate(createUpdate('u1'));
      updaterWithHandler.queueUpdate(createUpdate('u2'));

      await updaterWithHandler.flushUpdates();

      expect(flushed.length).toBe(1);
      expect(flushed[0].length).toBe(2);

      updaterWithHandler.clear();
    });

    it('should clear pending after flush', async () => {
      updater.queueUpdate(createUpdate('u1'));

      await updater.flushUpdates();

      expect(updater.getPendingCount()).toBe(0);
    });

    it('should do nothing for empty queue', async () => {
      let called = false;
      const updaterWithHandler = new ModelUpdater({}, async () => {
        called = true;
      });

      await updaterWithHandler.flushUpdates();

      expect(called).toBe(false);

      updaterWithHandler.clear();
    });

    it('should track total flushed', async () => {
      updater.queueUpdate(createUpdate('u1'));
      updater.queueUpdate(createUpdate('u2'));
      await updater.flushUpdates();

      updater.queueUpdate(createUpdate('u3'));
      await updater.flushUpdates();

      expect(updater.getTotalFlushed()).toBe(3);
    });
  });

  describe('timed flush', () => {
    it('should flush after interval', async () => {
      const flushed: LearningUpdate[][] = [];
      const updaterWithHandler = new ModelUpdater(
        { flushInterval: 1000 },
        async (updates) => {
          flushed.push(updates);
        }
      );

      updaterWithHandler.queueUpdate(createUpdate('u1'));

      // Fast-forward time
      await vi.advanceTimersByTimeAsync(1100);

      expect(flushed.length).toBe(1);

      updaterWithHandler.clear();
    });

    it('should not flush before interval', async () => {
      const flushed: LearningUpdate[][] = [];
      const updaterWithHandler = new ModelUpdater(
        { flushInterval: 1000 },
        async (updates) => {
          flushed.push(updates);
        }
      );

      updaterWithHandler.queueUpdate(createUpdate('u1'));

      // Fast-forward less than interval
      await vi.advanceTimersByTimeAsync(500);

      expect(flushed.length).toBe(0);

      updaterWithHandler.clear();
    });
  });

  describe('getPendingCount', () => {
    it('should return correct count', () => {
      expect(updater.getPendingCount()).toBe(0);

      updater.queueUpdate(createUpdate('u1'));
      expect(updater.getPendingCount()).toBe(1);

      updater.queueUpdate(createUpdate('u2'));
      expect(updater.getPendingCount()).toBe(2);
    });
  });

  describe('clear', () => {
    it('should clear pending updates', () => {
      updater.queueUpdate(createUpdate('u1'));
      updater.queueUpdate(createUpdate('u2'));

      updater.clear();

      expect(updater.getPendingCount()).toBe(0);
    });

    it('should cancel pending timer', async () => {
      const flushed: LearningUpdate[][] = [];
      const updaterWithHandler = new ModelUpdater(
        { flushInterval: 1000 },
        async (updates) => {
          flushed.push(updates);
        }
      );

      updaterWithHandler.queueUpdate(createUpdate('u1'));
      updaterWithHandler.clear();

      // Fast-forward time
      await vi.advanceTimersByTimeAsync(1100);

      expect(flushed.length).toBe(0);
    });
  });

  describe('configuration', () => {
    it('should use custom batch size', async () => {
      const flushed: LearningUpdate[][] = [];
      const updaterWithHandler = new ModelUpdater(
        { batchSize: 2 },
        async (updates) => {
          flushed.push(updates);
        }
      );

      updaterWithHandler.queueUpdate(createUpdate('u1'));
      updaterWithHandler.queueUpdate(createUpdate('u2'));

      await vi.runAllTimersAsync();

      expect(flushed.length).toBe(1);
      expect(flushed[0].length).toBe(2);

      updaterWithHandler.clear();
    });

    it('should use custom flush interval', async () => {
      const flushed: LearningUpdate[][] = [];
      const updaterWithHandler = new ModelUpdater(
        { flushInterval: 500 },
        async (updates) => {
          flushed.push(updates);
        }
      );

      updaterWithHandler.queueUpdate(createUpdate('u1'));

      await vi.advanceTimersByTimeAsync(600);

      expect(flushed.length).toBe(1);

      updaterWithHandler.clear();
    });
  });
});
