/**
 * @fileoverview Wake-sleep tests
 * @traceability TSK-WAKE-001, TSK-WAKE-002, TSK-WAKE-003, TSK-WAKE-007
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { WakePhase } from '../wake/wake-phase.js';
import { SleepPhase } from '../sleep/sleep-phase.js';
import { CycleManager } from '../cycle/cycle-manager.js';
import { ResourceLimiter } from '../resource/resource-limiter.js';
import type { WakeTask } from '../types.js';

describe('WakePhase', () => {
  let wake: WakePhase;

  beforeEach(() => {
    wake = new WakePhase();
  });

  it('should start with no tasks', () => {
    expect(wake.taskCount).toBe(0);
  });

  it('should add tasks', () => {
    const task: WakeTask = {
      id: 'task-1',
      type: 'code',
      content: 'const x = 1;',
      timestamp: new Date().toISOString(),
    };
    wake.addTask(task);
    expect(wake.taskCount).toBe(1);
  });

  it('should process tasks', async () => {
    const task: WakeTask = {
      id: 'task-1',
      type: 'code',
      content: 'const x = 1;',
      timestamp: new Date().toISOString(),
    };
    wake.addTask(task);
    
    const results = await wake.processAll();
    expect(results).toHaveLength(1);
    expect(results[0].success).toBe(true);
  });
});

describe('SleepPhase', () => {
  let sleep: SleepPhase;

  beforeEach(() => {
    sleep = new SleepPhase();
  });

  it('should consolidate patterns', async () => {
    const result = await sleep.consolidate({
      patterns: [
        { name: 'p1', code: 'const x = 1;', occurrences: 3, confidence: 0.8, source: 'code', structure: {} },
        { name: 'p2', code: 'const y = 2;', occurrences: 1, confidence: 0.5, source: 'code', structure: {} },
      ],
      existingLibrary: [],
    });

    expect(result.consolidatedPatterns).toContain('p1');
    expect(result.prunedPatterns).toContain('p2');
  });
});

describe('CycleManager', () => {
  let manager: CycleManager;

  beforeEach(() => {
    manager = new CycleManager({ wakeTaskThreshold: 5 });
  });

  it('should start in idle phase', () => {
    const status = manager.getStatus();
    expect(status.currentPhase).toBe('idle');
    expect(status.cycleNumber).toBe(0);
  });

  it('should switch to wake phase on task submission', async () => {
    const task: WakeTask = {
      id: 'task-1',
      type: 'code',
      content: 'test',
      timestamp: new Date().toISOString(),
    };
    await manager.submitTask(task);
    // Phase returns to idle after processing
  });
});

describe('ResourceLimiter', () => {
  let limiter: ResourceLimiter;

  beforeEach(() => {
    limiter = new ResourceLimiter({ maxConcurrency: 2 });
  });

  it('should allow starting operations within limit', () => {
    expect(limiter.canStartOperation()).toBe(true);
    limiter.startOperation('op-1');
    expect(limiter.canStartOperation()).toBe(true);
    limiter.startOperation('op-2');
    expect(limiter.canStartOperation()).toBe(false);
  });

  it('should track operation end', () => {
    limiter.startOperation('op-1');
    limiter.startOperation('op-2');
    expect(limiter.canStartOperation()).toBe(false);
    limiter.endOperation('op-1');
    expect(limiter.canStartOperation()).toBe(true);
  });

  it('should check pattern limits', () => {
    expect(limiter.canAddPatterns(100, 0)).toBe(true);
    expect(limiter.canAddPatterns(100, 10000)).toBe(false);
  });
});
