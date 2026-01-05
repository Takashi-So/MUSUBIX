/**
 * RealtimeLearningEngine - Orchestrates Real-time Learning
 *
 * Coordinates FileWatcher, StreamProcessor, FeedbackQueue, and EventStream
 * for real-time pattern learning.
 *
 * @see REQ-LEARN-010 - Real-time Pattern Learning
 * @see DES-LEARN-010 - Real-time Learning Architecture
 * @module @musubix/core/learning/realtime
 */

import { EventEmitter } from 'events';
import { FileWatcher } from './file-watcher.js';
import { StreamProcessor } from './stream-processor.js';
import { FeedbackQueue, createFeedback } from './feedback-queue.js';
import { EventStream, createPatternEvent } from './event-stream.js';
import { IncrementalUpdater, createUpdate } from './incremental-updater.js';
import {
  type FileChangeEvent,
  type RealtimeDetectedPattern,
  type RealtimeFeedback,
  type RealtimeMetrics,
  type FileWatcherConfig,
  type StreamProcessorConfig,
  type FeedbackQueueConfig,
  type EventStreamConfig,
} from './types.js';

/**
 * Engine configuration
 */
export interface RealtimeLearningConfig {
  /** FileWatcher configuration */
  fileWatcher?: Partial<FileWatcherConfig>;
  /** StreamProcessor configuration */
  streamProcessor?: Partial<StreamProcessorConfig>;
  /** FeedbackQueue configuration */
  feedbackQueue?: Partial<FeedbackQueueConfig>;
  /** EventStream configuration */
  eventStream?: Partial<EventStreamConfig>;
  /** Auto-start on creation */
  autoStart?: boolean;
}

/**
 * Engine events
 */
export interface EngineEvents {
  started: () => void;
  stopped: () => void;
  patternDetected: (pattern: RealtimeDetectedPattern) => void;
  feedbackReceived: (feedback: RealtimeFeedback) => void;
  error: (error: Error) => void;
}

/**
 * RealtimeLearningEngine - Main orchestrator
 *
 * @example
 * ```typescript
 * const engine = new RealtimeLearningEngine({
 *   fileWatcher: { paths: ['src'] },
 *   autoStart: true,
 * });
 *
 * engine.on('patternDetected', (pattern) => {
 *   console.log(`New pattern: ${pattern.name}`);
 * });
 *
 * // Submit feedback
 * engine.submitFeedback('accept', 'PAT-001');
 * ```
 */
export class RealtimeLearningEngine extends EventEmitter {
  private readonly fileWatcher: FileWatcher;
  private readonly streamProcessor: StreamProcessor;
  private readonly feedbackQueue: FeedbackQueue;
  private readonly eventStream: EventStream;
  private readonly updater: IncrementalUpdater;
  private _isRunning = false;
  private startTime: number | null = null;

  constructor(config: RealtimeLearningConfig = {}) {
    super();

    // Initialize components
    this.fileWatcher = new FileWatcher(config.fileWatcher);
    this.streamProcessor = new StreamProcessor(config.streamProcessor);
    this.feedbackQueue = new FeedbackQueue(config.feedbackQueue);
    this.eventStream = new EventStream(config.eventStream);
    this.updater = new IncrementalUpdater(this.eventStream);

    // Wire up event handlers
    this.setupEventHandlers();

    // Auto-start if configured
    if (config.autoStart) {
      this.start().catch((error) => {
        this.emit('error', error);
      });
    }
  }

  /**
   * Start the learning engine
   * @traceability REQ-LEARN-010
   */
  async start(): Promise<void> {
    if (this._isRunning) {
      return;
    }

    try {
      await this.fileWatcher.start();
      this._isRunning = true;
      this.startTime = Date.now();
      this.emit('started');
    } catch (error) {
      this.emit('error', error instanceof Error ? error : new Error(String(error)));
      throw error;
    }
  }

  /**
   * Stop the learning engine
   */
  stop(): void {
    if (!this._isRunning) {
      return;
    }

    this.fileWatcher.stop();
    this.eventStream.stop();
    this.feedbackQueue.clear();

    this._isRunning = false;
    this.emit('stopped');
  }

  /**
   * Check if engine is running
   */
  isRunning(): boolean {
    return this._isRunning;
  }

  /**
   * Watch additional paths
   * @traceability REQ-LEARN-010
   */
  async watch(paths: string[]): Promise<void> {
    await this.fileWatcher.watch(paths);
  }

  /**
   * Submit feedback for a pattern
   * @traceability REQ-LEARN-013 - Non-blocking
   */
  submitFeedback(
    type: 'accept' | 'reject' | 'modify',
    patternId: string,
    options?: {
      modification?: string;
      context?: Record<string, unknown>;
    }
  ): void {
    const feedback = createFeedback(type, patternId, options);
    this.feedbackQueue.enqueue(feedback);
  }

  /**
   * Get detected patterns
   */
  getPatterns(): RealtimeDetectedPattern[] {
    return this.updater.getAll();
  }

  /**
   * Get pattern by ID
   */
  getPattern(id: string): RealtimeDetectedPattern | undefined {
    return this.updater.get(id);
  }

  /**
   * Get patterns by category
   */
  getPatternsByCategory(category: 'code' | 'design' | 'test'): RealtimeDetectedPattern[] {
    return this.updater.getByCategory(category);
  }

  /**
   * Get engine metrics
   * @traceability REQ-LEARN-011, REQ-LEARN-014
   */
  getMetrics(): RealtimeMetrics {
    const queueMetrics = this.feedbackQueue.getMetrics();
    const streamMetrics = this.eventStream.getMetrics();
    const updateStats = this.updater.getStats();

    return {
      eventsProcessed: streamMetrics.totalEvents,
      avgLatencyMs: this.streamProcessor.getLatency(),
      maxLatencyMs: this.streamProcessor.getMaxLatency(),
      eventsPerSecond: streamMetrics.currentThroughput,
      patternsDetected: updateStats.added + updateStats.merged,
      feedbackProcessed: queueMetrics.totalDequeued,
      queueDepth: queueMetrics.currentDepth,
      uptimeMs: this.startTime ? Date.now() - this.startTime : 0,
    };
  }

  /**
   * Check if all SLAs are being met
   * @traceability REQ-LEARN-011, REQ-LEARN-013, REQ-LEARN-014
   */
  isMeetingAllSLAs(): boolean {
    return (
      this.streamProcessor.isMeetingSLA() &&
      this.feedbackQueue.isMeetingSLA() &&
      this.eventStream.isMeetingSLA()
    );
  }

  /**
   * Get component references for advanced usage
   */
  getComponents(): {
    fileWatcher: FileWatcher;
    streamProcessor: StreamProcessor;
    feedbackQueue: FeedbackQueue;
    eventStream: EventStream;
    updater: IncrementalUpdater;
  } {
    return {
      fileWatcher: this.fileWatcher,
      streamProcessor: this.streamProcessor,
      feedbackQueue: this.feedbackQueue,
      eventStream: this.eventStream,
      updater: this.updater,
    };
  }

  /**
   * Setup internal event handlers
   */
  private setupEventHandlers(): void {
    // File changes → Stream processing → Pattern updates
    this.fileWatcher.on('change', async (event: FileChangeEvent) => {
      try {
        const result = await this.streamProcessor.process(event);

        if (result.success) {
          for (const pattern of result.patterns) {
            this.updater.addPattern(pattern);
            this.emit('patternDetected', pattern);
          }

          // Emit analysis completed event
          this.eventStream.publish(
            createPatternEvent('analysis:completed', {
              file: event.path,
              patterns: result.patterns.length,
              latencyMs: result.latencyMs,
            })
          );
        }
      } catch (error) {
        this.emit('error', error instanceof Error ? error : new Error(String(error)));
      }
    });

    // File watcher errors
    this.fileWatcher.on('error', (error: Error) => {
      this.emit('error', error);
    });

    // Feedback processing
    this.feedbackQueue.on('batchReady', (batch: RealtimeFeedback[]) => {
      for (const feedback of batch) {
        this.processFeedback(feedback);
      }
    });
  }

  /**
   * Process feedback item
   */
  private processFeedback(feedback: RealtimeFeedback): void {
    this.emit('feedbackReceived', feedback);

    // Emit feedback event
    this.eventStream.publish(
      createPatternEvent('feedback:received', {
        feedbackId: feedback.id,
        patternId: feedback.patternId,
        type: feedback.type,
      })
    );

    // Apply feedback to pattern
    const pattern = this.updater.get(feedback.patternId);
    if (pattern) {
      if (feedback.type === 'reject') {
        // Lower confidence on rejection
        const updated: RealtimeDetectedPattern = {
          ...pattern,
          confidence: Math.max(0, pattern.confidence - 0.1),
        };
        this.updater.applyUpdate(createUpdate('update', pattern.id, updated));
      } else if (feedback.type === 'accept') {
        // Boost confidence on acceptance
        const updated: RealtimeDetectedPattern = {
          ...pattern,
          confidence: Math.min(1, pattern.confidence + 0.05),
        };
        this.updater.applyUpdate(createUpdate('update', pattern.id, updated));
      }
    }
  }
}

export { FileWatcher } from './file-watcher.js';
export { StreamProcessor } from './stream-processor.js';
export { FeedbackQueue, createFeedback } from './feedback-queue.js';
export { EventStream, createPatternEvent } from './event-stream.js';
export { IncrementalUpdater, createUpdate } from './incremental-updater.js';
export * from './types.js';
