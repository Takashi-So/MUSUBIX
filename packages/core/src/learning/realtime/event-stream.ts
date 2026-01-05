/**
 * EventStream - High-Throughput Event Distribution
 *
 * Distributes pattern events to subscribers with 1000+ events/sec throughput.
 *
 * @see REQ-LEARN-014 - Event Stream (1000 events/sec)
 * @see DES-LEARN-010 - EventStream Component
 * @module @musubix/core/learning/realtime
 */

import { EventEmitter } from 'events';
import {
  type PatternEvent,
  type PatternEventType,
  type Subscription,
  type EventStreamConfig,
  DEFAULT_EVENT_STREAM_CONFIG,
} from './types.js';

/**
 * Event handler function type
 */
type EventHandler = (event: PatternEvent) => void;

/**
 * Stream metrics for monitoring
 */
export interface StreamMetrics {
  /** Total events emitted */
  totalEvents: number;
  /** Events in last second */
  eventsLastSecond: number;
  /** Current throughput (events/sec) */
  currentThroughput: number;
  /** Peak throughput (events/sec) */
  peakThroughput: number;
  /** Active subscribers */
  activeSubscribers: number;
  /** Events dropped due to backpressure */
  droppedEvents: number;
  /** Buffer utilization (0-1) */
  bufferUtilization: number;
}

/**
 * Subscription implementation
 */
class SubscriptionImpl implements Subscription {
  private _isActive = true;
  private readonly unsubscribeCallback: () => void;

  constructor(unsubscribeCallback: () => void) {
    this.unsubscribeCallback = unsubscribeCallback;
  }

  unsubscribe(): void {
    if (this._isActive) {
      this._isActive = false;
      this.unsubscribeCallback();
    }
  }

  isActive(): boolean {
    return this._isActive;
  }
}

/**
 * EventStream - High-throughput event distribution
 *
 * @example
 * ```typescript
 * const stream = new EventStream();
 * const subscription = stream.subscribe((event) => {
 *   console.log(`Event: ${event.type}`);
 * });
 *
 * stream.emit(patternEvent);
 * console.log(`Throughput: ${stream.getThroughput()} events/sec`);
 * ```
 */
export class EventStream extends EventEmitter {
  private readonly config: EventStreamConfig;
  private readonly handlers: Map<string, EventHandler> = new Map();
  private readonly buffer: PatternEvent[] = [];
  private readonly timestampHistory: number[] = [];
  private handlerIdCounter = 0;
  private readonly metrics: StreamMetrics = {
    totalEvents: 0,
    eventsLastSecond: 0,
    currentThroughput: 0,
    peakThroughput: 0,
    activeSubscribers: 0,
    droppedEvents: 0,
    bufferUtilization: 0,
  };
  private throughputTimer: NodeJS.Timeout | null = null;
  private flushTimer: NodeJS.Timeout | null = null;

  constructor(config: Partial<EventStreamConfig> = {}) {
    super();
    this.config = { ...DEFAULT_EVENT_STREAM_CONFIG, ...config };
    this.startThroughputMonitoring();
  }

  /**
   * Publish a pattern event (alias for EventEmitter compatibility)
   * @traceability REQ-LEARN-014 - Must support 1000 events/sec
   */
  publish(event: PatternEvent): boolean {
    // Track timestamp for throughput calculation
    this.timestampHistory.push(Date.now());
    this.metrics.totalEvents++;

    // Apply backpressure if buffer is full
    if (this.config.enableBackpressure && this.buffer.length >= this.config.bufferSize) {
      this.metrics.droppedEvents++;
      return false;
    }

    // Buffer event
    this.buffer.push(event);
    this.metrics.bufferUtilization = this.buffer.length / this.config.bufferSize;

    // Schedule flush
    this.scheduleFlush();

    return true;
  }

  /**
   * Subscribe to pattern events
   */
  subscribe(handler: EventHandler): Subscription {
    const handlerId = `handler-${++this.handlerIdCounter}`;
    this.handlers.set(handlerId, handler);
    this.metrics.activeSubscribers = this.handlers.size;

    return new SubscriptionImpl(() => {
      this.handlers.delete(handlerId);
      this.metrics.activeSubscribers = this.handlers.size;
    });
  }

  /**
   * Subscribe to specific event types
   */
  subscribeToType(
    type: PatternEventType,
    handler: EventHandler
  ): Subscription {
    const wrappedHandler: EventHandler = (event) => {
      if (event.type === type) {
        handler(event);
      }
    };

    return this.subscribe(wrappedHandler);
  }

  /**
   * Get current throughput (events per second)
   * @traceability REQ-LEARN-014
   */
  getThroughput(): number {
    return this.metrics.currentThroughput;
  }

  /**
   * Check if meeting throughput SLA
   * @traceability REQ-LEARN-014
   */
  isMeetingSLA(): boolean {
    // SLA is met if we can handle at least target throughput
    return this.metrics.peakThroughput >= this.config.targetThroughput;
  }

  /**
   * Get stream metrics
   */
  getMetrics(): StreamMetrics {
    return { ...this.metrics };
  }

  /**
   * Stop the event stream
   */
  stop(): void {
    if (this.throughputTimer) {
      clearInterval(this.throughputTimer);
      this.throughputTimer = null;
    }

    if (this.flushTimer) {
      clearTimeout(this.flushTimer);
      this.flushTimer = null;
    }

    // Flush remaining events
    this.flush();

    this.handlers.clear();
    this.buffer.length = 0;
    this.timestampHistory.length = 0;
  }

  /**
   * Schedule buffer flush
   */
  private scheduleFlush(): void {
    if (!this.flushTimer) {
      // Flush every 10ms for low latency
      this.flushTimer = setTimeout(() => {
        this.flushTimer = null;
        this.flush();
      }, 10);
    }
  }

  /**
   * Flush buffered events to handlers
   */
  private flush(): void {
    const events = [...this.buffer];
    this.buffer.length = 0;
    this.metrics.bufferUtilization = 0;

    for (const event of events) {
      for (const handler of this.handlers.values()) {
        try {
          handler(event);
        } catch {
          // Don't let handler errors crash the stream
        }
      }
    }
  }

  /**
   * Start throughput monitoring
   */
  private startThroughputMonitoring(): void {
    this.throughputTimer = setInterval(() => {
      this.updateThroughputMetrics();
    }, 1000);
  }

  /**
   * Update throughput metrics
   */
  private updateThroughputMetrics(): void {
    const now = Date.now();
    const oneSecondAgo = now - 1000;

    // Filter timestamps from last second
    while (
      this.timestampHistory.length > 0 &&
      this.timestampHistory[0] < oneSecondAgo
    ) {
      this.timestampHistory.shift();
    }

    this.metrics.eventsLastSecond = this.timestampHistory.length;
    this.metrics.currentThroughput = this.timestampHistory.length;

    if (this.metrics.currentThroughput > this.metrics.peakThroughput) {
      this.metrics.peakThroughput = this.metrics.currentThroughput;
    }
  }
}

/**
 * Create a pattern event
 */
export function createPatternEvent(
  type: PatternEventType,
  payload: Record<string, unknown>
): PatternEvent {
  return {
    id: `EVT-${Date.now()}-${Math.random().toString(36).substring(7)}`,
    type,
    timestamp: Date.now(),
    payload,
  };
}
