/**
 * Model Updater
 * @module @nahisaho/musubix-neural-search
 * @description Batched model updates
 */

import type { IModelUpdater, LearningUpdate } from '../types.js';

/**
 * Model updater configuration
 */
export interface ModelUpdaterConfig {
  batchSize: number;
  flushInterval: number;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: ModelUpdaterConfig = {
  batchSize: 10,
  flushInterval: 5000,
};

/**
 * Model updater implementation
 */
export class ModelUpdater implements IModelUpdater {
  private readonly config: ModelUpdaterConfig;
  private pendingUpdates: LearningUpdate[];
  private onFlush?: (updates: LearningUpdate[]) => Promise<void>;
  private flushTimer?: ReturnType<typeof setTimeout>;
  private totalFlushed: number;

  constructor(
    config: Partial<ModelUpdaterConfig> = {},
    onFlush?: (updates: LearningUpdate[]) => Promise<void>
  ) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.pendingUpdates = [];
    this.onFlush = onFlush;
    this.totalFlushed = 0;
  }

  /**
   * Queue an update
   */
  queueUpdate(update: LearningUpdate): void {
    this.pendingUpdates.push(update);

    // Auto-flush if batch size reached
    if (this.pendingUpdates.length >= this.config.batchSize) {
      void this.flushUpdates();
    } else {
      // Set timer for flush
      this.scheduleFlush();
    }
  }

  /**
   * Flush pending updates
   */
  async flushUpdates(): Promise<void> {
    if (this.pendingUpdates.length === 0) {
      return;
    }

    // Clear timer
    if (this.flushTimer) {
      clearTimeout(this.flushTimer);
      this.flushTimer = undefined;
    }

    // Get updates to flush
    const updates = [...this.pendingUpdates];
    this.pendingUpdates = [];
    this.totalFlushed += updates.length;

    // Call flush handler if provided
    if (this.onFlush) {
      await this.onFlush(updates);
    }
  }

  /**
   * Get pending update count
   */
  getPendingCount(): number {
    return this.pendingUpdates.length;
  }

  /**
   * Get total flushed count
   */
  getTotalFlushed(): number {
    return this.totalFlushed;
  }

  /**
   * Clear pending updates without flushing
   */
  clear(): void {
    if (this.flushTimer) {
      clearTimeout(this.flushTimer);
      this.flushTimer = undefined;
    }
    this.pendingUpdates = [];
  }

  /**
   * Schedule a flush
   */
  private scheduleFlush(): void {
    if (this.flushTimer) {
      return;
    }

    this.flushTimer = setTimeout(() => {
      this.flushTimer = undefined;
      void this.flushUpdates();
    }, this.config.flushInterval);
  }
}
