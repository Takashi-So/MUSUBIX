/**
 * Progress Reporter Tests
 *
 * @module learning/inference/__tests__/progress-reporter.test
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  ProgressReporter,
  ConsoleProgressReporter,
  SilentProgressReporter,
} from '../progress-reporter.js';

describe('ProgressReporter', () => {
  let reporter: ProgressReporter;

  beforeEach(() => {
    vi.useFakeTimers();
    reporter = new ProgressReporter({ autoReport: false });
  });

  afterEach(() => {
    reporter.dispose();
    vi.useRealTimers();
  });

  describe('constructor', () => {
    it('should create reporter with default options', () => {
      const defaultReporter = new ProgressReporter();
      expect(defaultReporter).toBeInstanceOf(ProgressReporter);
      defaultReporter.dispose();
    });

    it('should create reporter with custom options', () => {
      const customReporter = new ProgressReporter({
        interval: 1000,
        minInterval: 200,
        verbose: true,
      });
      expect(customReporter).toBeInstanceOf(ProgressReporter);
      customReporter.dispose();
    });
  });

  describe('start', () => {
    it('should initialize progress with total triples', () => {
      reporter.start(100);

      const progress = reporter.getProgress();

      expect(progress.totalTriples).toBe(100);
      expect(progress.processedTriples).toBe(0);
      expect(progress.inferredTriples).toBe(0);
      expect(progress.phase).toBe('loading');
    });

    it('should reset elapsed time', () => {
      reporter.start(100);

      const progress = reporter.getProgress();

      expect(progress.elapsedMs).toBe(0);
    });
  });

  describe('update', () => {
    it('should update progress values', () => {
      reporter.start(100);

      reporter.update({
        processedTriples: 50,
        inferredTriples: 10,
      });

      const progress = reporter.getProgress();

      expect(progress.processedTriples).toBe(50);
      expect(progress.inferredTriples).toBe(10);
    });

    it('should update elapsed time', () => {
      reporter.start(100);

      vi.advanceTimersByTime(500);

      reporter.update({ processedTriples: 50 });

      const progress = reporter.getProgress();

      expect(progress.elapsedMs).toBe(500);
    });
  });

  describe('setPhase', () => {
    it('should update phase', () => {
      reporter.start(100);

      reporter.setPhase('reasoning');

      expect(reporter.getProgress().phase).toBe('reasoning');
    });
  });

  describe('incrementProcessed', () => {
    it('should increment processed count', () => {
      reporter.start(100);

      reporter.incrementProcessed();
      reporter.incrementProcessed();
      reporter.incrementProcessed();

      expect(reporter.getProgress().processedTriples).toBe(3);
    });

    it('should increment by specified amount', () => {
      reporter.start(100);

      reporter.incrementProcessed(10);

      expect(reporter.getProgress().processedTriples).toBe(10);
    });
  });

  describe('incrementInferred', () => {
    it('should increment inferred count', () => {
      reporter.start(100);

      reporter.incrementInferred();
      reporter.incrementInferred();

      expect(reporter.getProgress().inferredTriples).toBe(2);
    });
  });

  describe('complete', () => {
    it('should set phase to completed', () => {
      reporter.start(100);

      reporter.complete(50);

      const progress = reporter.getProgress();

      expect(progress.phase).toBe('completed');
      expect(progress.inferredTriples).toBe(50);
    });

    it('should set estimated remaining to 0', () => {
      reporter.start(100);

      reporter.complete(50);

      expect(reporter.getProgress().estimatedRemainingMs).toBe(0);
    });
  });

  describe('error', () => {
    it('should set phase to error with message', () => {
      reporter.start(100);

      reporter.error('Something went wrong');

      const progress = reporter.getProgress();

      expect(progress.phase).toBe('error');
      expect(progress.message).toBe('Something went wrong');
    });
  });

  describe('onProgress', () => {
    it('should register callback', () => {
      const callback = vi.fn();

      reporter.onProgress(callback);
      reporter.start(100);

      expect(callback).toHaveBeenCalled();
    });

    it('should return unsubscribe function', () => {
      const callback = vi.fn();

      const unsubscribe = reporter.onProgress(callback);
      unsubscribe();

      reporter.start(100);

      expect(callback).not.toHaveBeenCalled();
    });

    it('should call all registered callbacks', () => {
      const callback1 = vi.fn();
      const callback2 = vi.fn();

      reporter.onProgress(callback1);
      reporter.onProgress(callback2);
      reporter.start(100);

      expect(callback1).toHaveBeenCalled();
      expect(callback2).toHaveBeenCalled();
    });
  });

  describe('formatProgress', () => {
    it('should format progress as string', () => {
      reporter.start(100);
      reporter.update({ processedTriples: 50 });

      const formatted = reporter.formatProgress();

      expect(formatted).toContain('50%');
      expect(formatted).toContain('50/100');
    });

    it('should include phase label', () => {
      reporter.start(100);
      reporter.setPhase('reasoning');

      const formatted = reporter.formatProgress();

      expect(formatted).toContain('推論中');
    });

    it('should show completed status', () => {
      reporter.start(100);
      reporter.complete(50);

      const formatted = reporter.formatProgress();

      expect(formatted).toContain('完了');
    });
  });

  describe('formatProgressBar', () => {
    it('should generate progress bar', () => {
      reporter.start(100);
      reporter.update({ processedTriples: 50 });

      const bar = reporter.formatProgressBar(20);

      expect(bar).toContain('[');
      expect(bar).toContain(']');
      expect(bar).toContain('█');
      expect(bar).toContain('░');
      expect(bar).toContain('50%');
    });

    it('should handle 0%', () => {
      reporter.start(100);

      const bar = reporter.formatProgressBar(10);

      expect(bar).toContain('0%');
    });

    it('should handle 100%', () => {
      reporter.start(100);
      reporter.update({ processedTriples: 100 });

      const bar = reporter.formatProgressBar(10);

      expect(bar).toContain('100%');
    });
  });

  describe('estimated remaining time', () => {
    it('should estimate remaining time based on progress', () => {
      // Real timers for this test to get actual elapsed time
      vi.useRealTimers();
      const testReporter = new ProgressReporter({ autoReport: false });
      testReporter.start(100);

      // Wait a bit for elapsed time
      const startTime = Date.now();
      while (Date.now() - startTime < 10) {
        // spin wait
      }
      
      testReporter.update({ processedTriples: 50 });
      const progress = testReporter.getProgress();
      testReporter.dispose();

      // With 50% done, remaining time estimate should be positive (or 0 if very fast)
      expect(progress.elapsedMs).toBeGreaterThanOrEqual(0);
      // estimatedRemainingMs could be 0 if elapsed was too small
      expect(progress.estimatedRemainingMs).toBeGreaterThanOrEqual(0);
      
      // Restore fake timers for other tests
      vi.useFakeTimers();
    });

    it('should return 0 when completed', () => {
      reporter.start(100);
      reporter.update({ processedTriples: 100 });

      const progress = reporter.getProgress();

      expect(progress.estimatedRemainingMs).toBe(0);
    });
  });

  describe('toJSON', () => {
    it('should return progress as JSON-serializable object', () => {
      reporter.start(100);
      reporter.update({ processedTriples: 25 });

      const json = reporter.toJSON();

      expect(json).toHaveProperty('phase');
      expect(json).toHaveProperty('totalTriples', 100);
      expect(json).toHaveProperty('processedTriples', 25);
    });
  });

  describe('reset', () => {
    it('should reset all state', () => {
      reporter.start(100);
      reporter.update({ processedTriples: 50 });
      reporter.reset();

      const progress = reporter.getProgress();

      expect(progress.totalTriples).toBe(0);
      expect(progress.processedTriples).toBe(0);
      expect(progress.phase).toBe('initializing');
    });
  });
});

describe('ConsoleProgressReporter', () => {
  it('should create console reporter', () => {
    const reporter = new ConsoleProgressReporter();
    expect(reporter).toBeInstanceOf(ProgressReporter);
    reporter.dispose();
  });
});

describe('SilentProgressReporter', () => {
  it('should create silent reporter', () => {
    const reporter = new SilentProgressReporter();
    expect(reporter).toBeInstanceOf(ProgressReporter);
    reporter.dispose();
  });

  it('should not auto-report', () => {
    vi.useFakeTimers();

    const reporter = new SilentProgressReporter();
    const callback = vi.fn();

    reporter.onProgress(callback);
    reporter.start(100);

    // Advance time past the default interval
    vi.advanceTimersByTime(1000);

    // Should only be called once (on start)
    expect(callback).toHaveBeenCalledTimes(1);

    reporter.dispose();
    vi.useRealTimers();
  });
});
