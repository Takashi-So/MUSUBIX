/**
 * @fileoverview Learning Scheduler - Automated Wake-Sleep Cycle Execution
 *
 * Schedules and runs wake-sleep learning cycles automatically
 *
 * @traceability TSK-WSL-004, REQ-WSL-004
 */

import { EventEmitter } from 'events';
import type { CycleConfig, CycleStatus } from '../types.js';
import { CycleManager } from './cycle-manager.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Scheduler configuration
 */
export interface LearningSchedulerConfig extends Partial<CycleConfig> {
  /** Interval between automatic cycles in ms (default: 1 hour) */
  intervalMs?: number;
  /** Enable automatic scheduling (default: false) */
  autoStart?: boolean;
  /** Maximum consecutive cycles before pause (default: 10) */
  maxConsecutiveCycles?: number;
  /** Pause duration after max cycles (ms) (default: 6 hours) */
  pauseDurationMs?: number;
  /** Minimum patterns required to run cycle (default: 5) */
  minPatternsToRun?: number;
  /** Cron expression (optional, takes precedence over intervalMs) */
  cronExpression?: string;
}

/**
 * Cycle result
 */
export interface CycleResult {
  /** Cycle number */
  cycleNumber: number;
  /** Wake phase result */
  wakeResult: {
    extractedPatterns: number;
    processedTasks: number;
  };
  /** Sleep phase result */
  sleepResult: {
    clusteredPatterns: number;
    consolidatedPatterns: number;
  };
  /** Duration in ms */
  durationMs: number;
  /** Timestamp */
  timestamp: Date;
  /** Whether triggered manually */
  manual: boolean;
}

/**
 * Scheduler status
 */
export interface SchedulerStatus {
  /** Whether scheduler is running */
  running: boolean;
  /** Whether scheduler is paused */
  paused: boolean;
  /** Current cycle status */
  cycleStatus: CycleStatus;
  /** Total cycles run */
  totalCycles: number;
  /** Consecutive cycles since last pause */
  consecutiveCycles: number;
  /** Next scheduled run (if running) */
  nextRun?: Date;
  /** Last run timestamp */
  lastRun?: Date;
  /** Last result */
  lastResult?: CycleResult;
}

/**
 * Default scheduler configuration
 */
export const DEFAULT_SCHEDULER_CONFIG: Required<LearningSchedulerConfig> = {
  intervalMs: 60 * 60 * 1000, // 1 hour
  autoStart: false,
  maxConsecutiveCycles: 10,
  pauseDurationMs: 6 * 60 * 60 * 1000, // 6 hours
  minPatternsToRun: 5,
  cronExpression: '',
  wakeTaskThreshold: 10,
  maxCycleDuration: 60000,
  minPatternFrequency: 2,
  mdlThreshold: 0.5,
};

// ============================================================================
// Cron Parser (Simple Implementation)
// ============================================================================

/**
 * Simple cron expression parser
 * Supports: minute hour day-of-month month day-of-week
 * Example: "0 2 * * *" = 2:00 AM every day
 */
export function parseCronExpression(expression: string): { nextRun: Date } | null {
  const parts = expression.trim().split(/\s+/);
  if (parts.length !== 5) {
    return null;
  }

  const [minute, hour, dayOfMonth, month, dayOfWeek] = parts;
  const now = new Date();
  let next = new Date(now);

  // Simple implementation - find next occurrence
  // This is a basic implementation and doesn't handle all cron features
  
  // Set minute
  if (minute !== '*') {
    const m = parseInt(minute, 10);
    if (!isNaN(m) && m >= 0 && m <= 59) {
      next.setMinutes(m);
    }
  }

  // Set hour
  if (hour !== '*') {
    const h = parseInt(hour, 10);
    if (!isNaN(h) && h >= 0 && h <= 23) {
      next.setHours(h);
    }
  }

  // Reset seconds
  next.setSeconds(0);
  next.setMilliseconds(0);

  // If the time has passed today, move to tomorrow
  if (next <= now) {
    next.setDate(next.getDate() + 1);
  }

  // Day of month
  if (dayOfMonth !== '*') {
    const d = parseInt(dayOfMonth, 10);
    if (!isNaN(d) && d >= 1 && d <= 31) {
      next.setDate(d);
      if (next <= now) {
        next.setMonth(next.getMonth() + 1);
      }
    }
  }

  // Month
  if (month !== '*') {
    const mo = parseInt(month, 10);
    if (!isNaN(mo) && mo >= 1 && mo <= 12) {
      next.setMonth(mo - 1);
      if (next <= now) {
        next.setFullYear(next.getFullYear() + 1);
      }
    }
  }

  // Day of week (0 = Sunday)
  if (dayOfWeek !== '*') {
    const dow = parseInt(dayOfWeek, 10);
    if (!isNaN(dow) && dow >= 0 && dow <= 6) {
      const currentDow = next.getDay();
      const daysUntil = (dow - currentDow + 7) % 7;
      if (daysUntil === 0 && next <= now) {
        next.setDate(next.getDate() + 7);
      } else {
        next.setDate(next.getDate() + daysUntil);
      }
    }
  }

  return { nextRun: next };
}

/**
 * Calculate ms until next cron run
 */
export function msUntilNextCronRun(expression: string): number | null {
  const parsed = parseCronExpression(expression);
  if (!parsed) {
    return null;
  }
  return parsed.nextRun.getTime() - Date.now();
}

// ============================================================================
// Learning Scheduler
// ============================================================================

/**
 * Learning Scheduler events
 */
export interface LearningSchedulerEvents {
  'scheduler:started': Record<string, never>;
  'scheduler:stopped': Record<string, never>;
  'scheduler:paused': { reason: string };
  'scheduler:resumed': Record<string, never>;
  'cycle:started': { cycleNumber: number; manual: boolean };
  'cycle:completed': { result: CycleResult };
  'cycle:failed': { error: Error; cycleNumber: number };
  'error': Error;
}

/**
 * Learning Scheduler
 *
 * Schedules and runs wake-sleep learning cycles automatically
 *
 * @example
 * ```typescript
 * const scheduler = new LearningScheduler({
 *   intervalMs: 30 * 60 * 1000, // 30 minutes
 * });
 *
 * scheduler.start();
 *
 * // Manual trigger
 * const result = await scheduler.runCycle();
 *
 * scheduler.stop();
 * ```
 */
export class LearningScheduler extends EventEmitter {
  private cycleManager: CycleManager;
  private config: Required<LearningSchedulerConfig>;
  
  private running = false;
  private paused = false;
  private timer: ReturnType<typeof setTimeout> | null = null;
  
  private totalCycles = 0;
  private consecutiveCycles = 0;
  private lastRun?: Date;
  private lastResult?: CycleResult;
  private nextRun?: Date;

  constructor(config: LearningSchedulerConfig = {}) {
    super();

    this.config = { ...DEFAULT_SCHEDULER_CONFIG, ...config };
    this.cycleManager = new CycleManager({
      wakeTaskThreshold: this.config.wakeTaskThreshold,
      maxCycleDuration: this.config.maxCycleDuration,
      minPatternFrequency: this.config.minPatternFrequency,
      mdlThreshold: this.config.mdlThreshold,
    });

    if (this.config.autoStart) {
      this.start();
    }
  }

  /**
   * Get underlying cycle manager
   */
  getCycleManager(): CycleManager {
    return this.cycleManager;
  }

  /**
   * Start the scheduler
   */
  start(): void {
    if (this.running) {
      return;
    }

    this.running = true;
    this.paused = false;
    this.scheduleNextRun();
    this.emit('scheduler:started', {});
  }

  /**
   * Stop the scheduler
   */
  stop(): void {
    if (!this.running) {
      return;
    }

    this.running = false;
    this.paused = false;
    
    if (this.timer) {
      clearTimeout(this.timer);
      this.timer = null;
    }
    
    this.nextRun = undefined;
    this.emit('scheduler:stopped', {});
  }

  /**
   * Pause the scheduler
   */
  pause(reason = 'Manual pause'): void {
    if (!this.running || this.paused) {
      return;
    }

    this.paused = true;
    
    if (this.timer) {
      clearTimeout(this.timer);
      this.timer = null;
    }
    
    this.nextRun = undefined;
    this.emit('scheduler:paused', { reason });
  }

  /**
   * Resume the scheduler
   */
  resume(): void {
    if (!this.running || !this.paused) {
      return;
    }

    this.paused = false;
    this.consecutiveCycles = 0;
    this.scheduleNextRun();
    this.emit('scheduler:resumed', {});
  }

  /**
   * Schedule the next automatic run
   */
  private scheduleNextRun(): void {
    if (!this.running || this.paused) {
      return;
    }

    let delayMs: number;

    // Use cron expression if provided
    if (this.config.cronExpression) {
      const cronDelay = msUntilNextCronRun(this.config.cronExpression);
      if (cronDelay !== null) {
        delayMs = cronDelay;
      } else {
        delayMs = this.config.intervalMs;
      }
    } else {
      delayMs = this.config.intervalMs;
    }

    this.nextRun = new Date(Date.now() + delayMs);

    this.timer = setTimeout(async () => {
      await this.runAutomaticCycle();
    }, delayMs);
  }

  /**
   * Run an automatic cycle
   */
  private async runAutomaticCycle(): Promise<void> {
    if (!this.running || this.paused) {
      return;
    }

    try {
      await this.executeCycle(false);
      
      this.consecutiveCycles++;
      
      // Check if we need to pause
      if (this.consecutiveCycles >= this.config.maxConsecutiveCycles) {
        this.pause(`Reached max consecutive cycles (${this.config.maxConsecutiveCycles})`);
        
        // Schedule resume after pause duration
        setTimeout(() => {
          if (this.running && this.paused) {
            this.resume();
          }
        }, this.config.pauseDurationMs);
      } else {
        // Schedule next run
        this.scheduleNextRun();
      }
    } catch {
      // Schedule next run despite error
      this.scheduleNextRun();
    }
  }

  /**
   * Run a cycle manually
   */
  async runCycle(): Promise<CycleResult> {
    return this.executeCycle(true);
  }

  /**
   * Execute a learning cycle
   */
  private async executeCycle(manual: boolean): Promise<CycleResult> {
    const startTime = Date.now();
    const cycleNumber = this.totalCycles + 1;

    this.emit('cycle:started', { cycleNumber, manual });

    try {
      // Get current status before cycle
      const statusBefore = this.cycleManager.getStatus();

      // Run the sleep phase (which processes wake tasks)
      await this.cycleManager.runSleepPhase();

      // Get status after cycle
      const statusAfter = this.cycleManager.getStatus();

      const result: CycleResult = {
        cycleNumber,
        wakeResult: {
          extractedPatterns: 0, // Would need to track from wake phase
          processedTasks: statusBefore.taskCount,
        },
        sleepResult: {
          clusteredPatterns: 0, // Would need to track from sleep phase
          consolidatedPatterns: statusAfter.patternCount - statusBefore.patternCount,
        },
        durationMs: Date.now() - startTime,
        timestamp: new Date(),
        manual,
      };

      this.totalCycles++;
      this.lastRun = result.timestamp;
      this.lastResult = result;

      this.emit('cycle:completed', { result });

      return result;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      this.emit('cycle:failed', { error: err, cycleNumber });
      this.emit('error', err);
      throw err;
    }
  }

  /**
   * Get scheduler status
   */
  getStatus(): SchedulerStatus {
    return {
      running: this.running,
      paused: this.paused,
      cycleStatus: this.cycleManager.getStatus(),
      totalCycles: this.totalCycles,
      consecutiveCycles: this.consecutiveCycles,
      nextRun: this.nextRun,
      lastRun: this.lastRun,
      lastResult: this.lastResult,
    };
  }

  /**
   * Check if scheduler is running
   */
  isRunning(): boolean {
    return this.running;
  }

  /**
   * Check if scheduler is paused
   */
  isPaused(): boolean {
    return this.paused;
  }

  /**
   * Reset the scheduler and cycle manager
   */
  reset(): void {
    this.stop();
    this.cycleManager.reset();
    this.totalCycles = 0;
    this.consecutiveCycles = 0;
    this.lastRun = undefined;
    this.lastResult = undefined;
    this.nextRun = undefined;
  }

  /**
   * Update configuration
   */
  updateConfig(config: Partial<LearningSchedulerConfig>): void {
    const wasRunning = this.running;
    
    if (wasRunning) {
      this.stop();
    }

    this.config = { ...this.config, ...config };

    // Recreate cycle manager with new config
    this.cycleManager = new CycleManager({
      wakeTaskThreshold: this.config.wakeTaskThreshold,
      maxCycleDuration: this.config.maxCycleDuration,
      minPatternFrequency: this.config.minPatternFrequency,
      mdlThreshold: this.config.mdlThreshold,
    });

    if (wasRunning) {
      this.start();
    }
  }

  /**
   * Get current configuration
   */
  getConfig(): Required<LearningSchedulerConfig> {
    return { ...this.config };
  }
}
