/**
 * Real-time Learning Types
 *
 * Type definitions for real-time pattern learning system
 *
 * @see REQ-LEARN-010 - Real-time Pattern Learning
 * @see REQ-LEARN-011 - 500ms Analysis Latency
 * @see REQ-LEARN-012 - Incremental Updates
 * @see REQ-LEARN-013 - Non-blocking Feedback
 * @see REQ-LEARN-014 - Event Stream (1000 events/sec)
 * @see DES-LEARN-010 - Real-time Learning Architecture
 * @module @musubix/core/learning/realtime
 */

/**
 * File change event types
 */
export type FileChangeType = 'create' | 'modify' | 'delete';

/**
 * Pattern event types for the event stream
 */
export type PatternEventType =
  | 'pattern:detected'
  | 'pattern:updated'
  | 'pattern:removed'
  | 'feedback:received'
  | 'analysis:completed';

/**
 * File change event emitted by FileWatcher
 * @see REQ-LEARN-010 - Real-time monitoring
 */
export interface FileChangeEvent {
  /** Absolute path to the changed file */
  readonly path: string;
  /** Type of change */
  readonly type: FileChangeType;
  /** Timestamp of the change (Unix milliseconds) */
  readonly timestamp: number;
  /** File content (for create/modify) */
  readonly content?: string;
  /** Previous content (for modify) */
  readonly previousContent?: string;
}

/**
 * Result of stream processing
 * @see REQ-LEARN-011 - 500ms latency requirement
 */
export interface ProcessResult {
  /** Whether processing was successful */
  readonly success: boolean;
  /** Processing latency in milliseconds */
  readonly latencyMs: number;
  /** Detected patterns (if any) */
  readonly patterns: RealtimeDetectedPattern[];
  /** Error message (if failed) */
  readonly error?: string;
}

/**
 * Pattern detected during real-time analysis
 */
export interface RealtimeDetectedPattern {
  /** Pattern identifier */
  readonly id: string;
  /** Pattern name */
  readonly name: string;
  /** Pattern category */
  readonly category: 'code' | 'design' | 'test';
  /** Confidence score (0-1) */
  readonly confidence: number;
  /** Source file path */
  readonly sourcePath: string;
  /** Line range in source */
  readonly lineRange: { start: number; end: number };
  /** Pattern template */
  readonly template: string;
  /** Detection timestamp */
  readonly detectedAt: number;
}

/**
 * Feedback for real-time learning
 * @see REQ-LEARN-013 - Non-blocking feedback
 */
export interface RealtimeFeedback {
  /** Feedback identifier */
  readonly id: string;
  /** Target pattern ID */
  readonly patternId: string;
  /** Feedback type */
  readonly type: 'accept' | 'reject' | 'modify';
  /** Timestamp */
  readonly timestamp: number;
  /** Optional modification */
  readonly modification?: string;
  /** User context */
  readonly context?: Record<string, unknown>;
}

/**
 * Pattern event for the event stream
 * @see REQ-LEARN-014 - Event stream throughput
 */
export interface PatternEvent {
  /** Event identifier */
  readonly id: string;
  /** Event type */
  readonly type: PatternEventType;
  /** Event timestamp */
  readonly timestamp: number;
  /** Event payload */
  readonly payload: Record<string, unknown>;
}

/**
 * Event subscription handle
 */
export interface Subscription {
  /** Unsubscribe from events */
  unsubscribe(): void;
  /** Check if still subscribed */
  isActive(): boolean;
}

/**
 * Incremental update operation
 * @see REQ-LEARN-012 - Delta updates
 */
export interface IncrementalUpdate {
  /** Update type */
  readonly type: 'add' | 'update' | 'remove';
  /** Target pattern ID */
  readonly patternId: string;
  /** Pattern data (for add/update) */
  readonly pattern?: RealtimeDetectedPattern;
  /** Timestamp */
  readonly timestamp: number;
}

/**
 * FileWatcher configuration
 */
export interface FileWatcherConfig {
  /** Paths to watch */
  readonly paths: string[];
  /** File extensions to include */
  readonly extensions: string[];
  /** Paths to ignore (glob patterns) */
  readonly ignore: string[];
  /** Debounce delay in milliseconds */
  readonly debounceMs: number;
}

/**
 * StreamProcessor configuration
 */
export interface StreamProcessorConfig {
  /** Maximum latency in milliseconds (default: 500) */
  readonly maxLatencyMs: number;
  /** Enable AST analysis */
  readonly enableAstAnalysis: boolean;
  /** Minimum confidence threshold */
  readonly minConfidence: number;
}

/**
 * FeedbackQueue configuration
 */
export interface FeedbackQueueConfig {
  /** Maximum queue size */
  readonly maxSize: number;
  /** Maximum enqueue latency in milliseconds (default: 100) */
  readonly maxEnqueueLatencyMs: number;
  /** Batch processing size */
  readonly batchSize: number;
}

/**
 * EventStream configuration
 */
export interface EventStreamConfig {
  /** Target throughput (events per second) */
  readonly targetThroughput: number;
  /** Buffer size */
  readonly bufferSize: number;
  /** Enable backpressure handling */
  readonly enableBackpressure: boolean;
}

/**
 * Real-time learning metrics
 */
export interface RealtimeMetrics {
  /** Total events processed */
  readonly eventsProcessed: number;
  /** Average processing latency (ms) */
  readonly avgLatencyMs: number;
  /** Maximum processing latency (ms) */
  readonly maxLatencyMs: number;
  /** Events per second (throughput) */
  readonly eventsPerSecond: number;
  /** Patterns detected */
  readonly patternsDetected: number;
  /** Feedback items processed */
  readonly feedbackProcessed: number;
  /** Queue depth */
  readonly queueDepth: number;
  /** Uptime in milliseconds */
  readonly uptimeMs: number;
}

/**
 * Default configurations
 */
export const DEFAULT_FILE_WATCHER_CONFIG: FileWatcherConfig = {
  paths: ['.'],
  extensions: ['.ts', '.tsx', '.js', '.jsx'],
  ignore: ['node_modules/**', 'dist/**', '*.test.ts', '*.spec.ts'],
  debounceMs: 100,
};

export const DEFAULT_STREAM_PROCESSOR_CONFIG: StreamProcessorConfig = {
  maxLatencyMs: 500,
  enableAstAnalysis: true,
  minConfidence: 0.7,
};

export const DEFAULT_FEEDBACK_QUEUE_CONFIG: FeedbackQueueConfig = {
  maxSize: 10000,
  maxEnqueueLatencyMs: 100,
  batchSize: 100,
};

export const DEFAULT_EVENT_STREAM_CONFIG: EventStreamConfig = {
  targetThroughput: 1000,
  bufferSize: 10000,
  enableBackpressure: true,
};
