/**
 * FeedbackQueue - Non-blocking Feedback Collection
 *
 * Queues feedback for asynchronous processing without blocking main thread.
 * Enqueue operation must complete within 100ms SLA.
 *
 * @see REQ-LEARN-013 - Non-blocking Feedback (100ms)
 * @see DES-LEARN-010 - FeedbackQueue Component
 * @module @musubix/core/learning/realtime
 */

import { EventEmitter } from 'events';
import {
  type RealtimeFeedback,
  type FeedbackQueueConfig,
  DEFAULT_FEEDBACK_QUEUE_CONFIG,
} from './types.js';

/**
 * FeedbackQueue events
 */
export interface FeedbackQueueEvents {
  enqueued: (feedback: RealtimeFeedback) => void;
  dequeued: (feedback: RealtimeFeedback) => void;
  batchReady: (batch: RealtimeFeedback[]) => void;
  overflow: (dropped: RealtimeFeedback) => void;
}

/**
 * Queue metrics for monitoring
 */
export interface QueueMetrics {
  /** Total items enqueued */
  totalEnqueued: number;
  /** Total items dequeued */
  totalDequeued: number;
  /** Items dropped due to overflow */
  dropped: number;
  /** Average enqueue latency (ms) */
  avgEnqueueLatencyMs: number;
  /** Maximum enqueue latency (ms) */
  maxEnqueueLatencyMs: number;
  /** Current queue depth */
  currentDepth: number;
}

/**
 * FeedbackQueue - Non-blocking feedback collection
 *
 * @example
 * ```typescript
 * const queue = new FeedbackQueue();
 * queue.on('batchReady', (batch) => {
 *   processBatch(batch);
 * });
 * queue.enqueue(feedback); // Non-blocking, < 100ms
 * ```
 */
export class FeedbackQueue extends EventEmitter {
  private readonly config: FeedbackQueueConfig;
  private readonly queue: RealtimeFeedback[] = [];
  private readonly metrics: QueueMetrics = {
    totalEnqueued: 0,
    totalDequeued: 0,
    dropped: 0,
    avgEnqueueLatencyMs: 0,
    maxEnqueueLatencyMs: 0,
    currentDepth: 0,
  };
  private latencyHistory: number[] = [];
  private batchTimer: NodeJS.Timeout | null = null;
  private readonly batchDelayMs = 50;

  constructor(config: Partial<FeedbackQueueConfig> = {}) {
    super();
    this.config = { ...DEFAULT_FEEDBACK_QUEUE_CONFIG, ...config };
  }

  /**
   * Enqueue feedback item (non-blocking)
   * @traceability REQ-LEARN-013 - Must complete within 100ms
   */
  enqueue(feedback: RealtimeFeedback): void {
    const startTime = performance.now();

    try {
      // Check queue capacity
      if (this.queue.length >= this.config.maxSize) {
        // Overflow: drop oldest or current based on priority
        const dropped = this.queue.shift();
        if (dropped) {
          this.metrics.dropped++;
          this.emit('overflow', dropped);
        }
      }

      // Add to queue
      this.queue.push(feedback);
      this.metrics.totalEnqueued++;
      this.metrics.currentDepth = this.queue.length;

      // Track latency
      const latency = performance.now() - startTime;
      this.trackLatency(latency);

      this.emit('enqueued', feedback);

      // Schedule batch processing
      this.scheduleBatch();
    } catch {
      // Ensure non-blocking even on error
    }
  }

  /**
   * Dequeue single feedback item
   */
  dequeue(): RealtimeFeedback | undefined {
    const feedback = this.queue.shift();

    if (feedback) {
      this.metrics.totalDequeued++;
      this.metrics.currentDepth = this.queue.length;
      this.emit('dequeued', feedback);
    }

    return feedback;
  }

  /**
   * Dequeue batch of feedback items
   */
  dequeueBatch(size?: number): RealtimeFeedback[] {
    const batchSize = size ?? this.config.batchSize;
    const batch: RealtimeFeedback[] = [];

    for (let i = 0; i < batchSize && this.queue.length > 0; i++) {
      const feedback = this.queue.shift();
      if (feedback) {
        batch.push(feedback);
        this.metrics.totalDequeued++;
      }
    }

    this.metrics.currentDepth = this.queue.length;
    return batch;
  }

  /**
   * Get current queue size
   */
  size(): number {
    return this.queue.length;
  }

  /**
   * Check if queue is empty
   */
  isEmpty(): boolean {
    return this.queue.length === 0;
  }

  /**
   * Get queue metrics
   */
  getMetrics(): QueueMetrics {
    return { ...this.metrics };
  }

  /**
   * Check if queue is meeting SLA
   * @traceability REQ-LEARN-013
   */
  isMeetingSLA(): boolean {
    return this.metrics.maxEnqueueLatencyMs <= this.config.maxEnqueueLatencyMs;
  }

  /**
   * Clear the queue
   */
  clear(): void {
    this.queue.length = 0;
    this.metrics.currentDepth = 0;

    if (this.batchTimer) {
      clearTimeout(this.batchTimer);
      this.batchTimer = null;
    }
  }

  /**
   * Peek at next item without removing
   */
  peek(): RealtimeFeedback | undefined {
    return this.queue[0];
  }

  /**
   * Track enqueue latency
   */
  private trackLatency(latency: number): void {
    this.latencyHistory.push(latency);

    // Keep last 100 measurements
    if (this.latencyHistory.length > 100) {
      this.latencyHistory.shift();
    }

    // Update metrics
    const sum = this.latencyHistory.reduce((a, b) => a + b, 0);
    this.metrics.avgEnqueueLatencyMs = sum / this.latencyHistory.length;
    this.metrics.maxEnqueueLatencyMs = Math.max(...this.latencyHistory);
  }

  /**
   * Schedule batch processing
   */
  private scheduleBatch(): void {
    // Check if batch is ready
    if (this.queue.length >= this.config.batchSize) {
      this.emitBatch();
      return;
    }

    // Schedule delayed batch
    if (!this.batchTimer) {
      this.batchTimer = setTimeout(() => {
        this.batchTimer = null;
        if (this.queue.length > 0) {
          this.emitBatch();
        }
      }, this.batchDelayMs);
    }
  }

  /**
   * Emit batch ready event
   */
  private emitBatch(): void {
    const batch = this.dequeueBatch();
    if (batch.length > 0) {
      this.emit('batchReady', batch);
    }
  }
}

/**
 * Create a feedback object
 */
export function createFeedback(
  type: 'accept' | 'reject' | 'modify',
  patternId: string,
  options?: {
    modification?: string;
    context?: Record<string, unknown>;
  }
): RealtimeFeedback {
  return {
    id: `FB-${Date.now()}-${Math.random().toString(36).substring(7)}`,
    patternId,
    type,
    timestamp: Date.now(),
    modification: options?.modification,
    context: options?.context,
  };
}
