/**
 * @fileoverview Wake-sleep cycle manager
 * @traceability TSK-WAKE-003, REQ-WAKE-001-F003
 */

import type { CycleConfig, CycleStatus, WakeTask } from '../types.js';
import { WakePhase } from '../wake/wake-phase.js';
import { SleepPhase } from '../sleep/sleep-phase.js';

/**
 * Manages the wake-sleep learning cycle
 * 
 * @description
 * Coordinates between wake and sleep phases:
 * - Wake: Collect patterns from tasks
 * - Sleep: Consolidate and abstract patterns
 * - Auto-triggers sleep when threshold reached
 */
export class CycleManager {
  private wake: WakePhase;
  private sleep: SleepPhase;
  private config: CycleConfig;
  private cycleNumber = 0;
  private lastCycleTime: string | null = null;
  private currentPhase: 'wake' | 'sleep' | 'idle' = 'idle';
  private consolidatedPatternCount = 0;

  constructor(config: Partial<CycleConfig> = {}) {
    this.config = {
      wakeTaskThreshold: config.wakeTaskThreshold ?? 10,
      maxCycleDuration: config.maxCycleDuration ?? 60000,
      minPatternFrequency: config.minPatternFrequency ?? 2,
      mdlThreshold: config.mdlThreshold ?? 0.5,
    };

    this.wake = new WakePhase();
    this.sleep = new SleepPhase({
      minFrequency: this.config.minPatternFrequency,
      mdlThreshold: this.config.mdlThreshold,
    });
  }

  /**
   * Submit task during wake phase
   */
  async submitTask(task: WakeTask): Promise<void> {
    this.currentPhase = 'wake';
    this.wake.addTask(task);

    // Auto-trigger sleep if threshold reached
    if (this.wake.taskCount >= this.config.wakeTaskThreshold) {
      await this.runSleepPhase();
    }
  }

  /**
   * Manually trigger sleep phase
   */
  async runSleepPhase(): Promise<void> {
    this.currentPhase = 'sleep';

    // Process all wake tasks
    const wakeResults = await this.wake.processAll();

    // Consolidate patterns during sleep
    if (wakeResults.length > 0) {
      const patternCandidates = wakeResults
        .flatMap(r => r.extractedPatterns)
        .map(p => ({
          name: p,
          code: p,
          structure: {},
          occurrences: 1,
          confidence: 0.5,
          source: 'code' as const,
        }));

      if (patternCandidates.length > 0) {
        const sleepResult = await this.sleep.consolidate({
          patterns: patternCandidates,
          existingLibrary: [],
        });
        this.consolidatedPatternCount += sleepResult.consolidatedPatterns.length;
      }
    }
    
    this.cycleNumber++;
    this.lastCycleTime = new Date().toISOString();
    this.currentPhase = 'idle';
  }

  /**
   * Get current cycle status
   */
  getStatus(): CycleStatus {
    return {
      currentPhase: this.currentPhase,
      taskCount: this.wake.taskCount,
      patternCount: this.consolidatedPatternCount,
      cycleNumber: this.cycleNumber,
      lastCycleTime: this.lastCycleTime,
    };
  }

  /**
   * Reset cycle manager
   */
  reset(): void {
    this.wake.reset();
    this.cycleNumber = 0;
    this.lastCycleTime = null;
    this.currentPhase = 'idle';
    this.consolidatedPatternCount = 0;
  }
}
