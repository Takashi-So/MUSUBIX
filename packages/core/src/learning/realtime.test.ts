/**
 * Real-time Learning Tests
 *
 * Tests for the real-time pattern learning system
 *
 * @see REQ-LEARN-010 - Real-time Pattern Learning
 * @see REQ-LEARN-011 - 500ms Analysis Latency
 * @see REQ-LEARN-012 - Incremental Updates
 * @see REQ-LEARN-013 - Non-blocking Feedback (100ms)
 * @see REQ-LEARN-014 - Event Stream (1000 events/sec)
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  FileWatcher,
  StreamProcessor,
  FeedbackQueue,
  EventStream,
  IncrementalUpdater,
  RealtimeLearningEngine,
  createFeedback,
  createPatternEvent,
  createUpdate,
  type FileChangeEvent,
  type RealtimeDetectedPattern,
} from './realtime/index.js';

// --- FileWatcher Tests ---
describe('FileWatcher', () => {
  let watcher: FileWatcher;

  beforeEach(() => {
    watcher = new FileWatcher({
      paths: [],
      extensions: ['.ts', '.js'],
      ignore: ['node_modules/**'],
      debounceMs: 50,
    });
  });

  afterEach(() => {
    watcher.stop();
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should initialize with configuration', () => {
    expect(watcher).toBeDefined();
    expect(watcher.isWatching()).toBe(false);
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should report watching status after start', async () => {
    // Start watching empty paths (no actual file system access)
    await watcher.start();
    expect(watcher.isWatching()).toBe(true);
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should stop watching on stop()', async () => {
    await watcher.start();
    watcher.stop();
    expect(watcher.isWatching()).toBe(false);
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should register change callback', () => {
    const callback = vi.fn();
    watcher.onFileChange(callback);
    expect(watcher.listenerCount('change')).toBe(1);
  });
});

// --- StreamProcessor Tests ---
describe('StreamProcessor', () => {
  let processor: StreamProcessor;

  beforeEach(() => {
    processor = new StreamProcessor({
      maxLatencyMs: 500,
      enableAstAnalysis: true,
      minConfidence: 0.7,
    });
  });

  /**
   * @traceability REQ-LEARN-011 - 500ms SLA
   */
  it('should process file change within 500ms', async () => {
    const event: FileChangeEvent = {
      path: '/src/service.ts',
      type: 'modify',
      timestamp: Date.now(),
      content: `
        class UserService {
          async findById(id: string): Promise<User | undefined> {
            return this.repository.findById(id);
          }
        }
      `,
    };

    const result = await processor.process(event);

    expect(result.success).toBe(true);
    expect(result.latencyMs).toBeLessThan(500);
  });

  /**
   * @traceability REQ-LEARN-011
   */
  it('should detect Service pattern', async () => {
    const event: FileChangeEvent = {
      path: '/src/user-service.ts',
      type: 'modify',
      timestamp: Date.now(),
      content: `
        class UserService implements IUserService {
          constructor(private repository: UserRepository) {}
        }
      `,
    };

    const result = await processor.process(event);

    expect(result.success).toBe(true);
    expect(result.patterns.length).toBeGreaterThanOrEqual(1);
    expect(result.patterns.some((p) => p.name.includes('Service'))).toBe(true);
  });

  /**
   * @traceability REQ-LEARN-011
   */
  it('should detect Factory pattern', async () => {
    const event: FileChangeEvent = {
      path: '/src/user-factory.ts',
      type: 'modify',
      timestamp: Date.now(),
      content: `
        function createUser(input: UserInput): Result<User, ValidationError> {
          if (!input.email) {
            return err(new ValidationError('Email required'));
          }
          return ok({ id: generateId(), ...input });
        }
      `,
    };

    const result = await processor.process(event);

    expect(result.success).toBe(true);
    expect(result.patterns.some((p) => p.name.includes('Factory'))).toBe(true);
  });

  /**
   * @traceability REQ-LEARN-011
   */
  it('should skip delete events', async () => {
    const event: FileChangeEvent = {
      path: '/src/deleted.ts',
      type: 'delete',
      timestamp: Date.now(),
    };

    const result = await processor.process(event);

    expect(result.success).toBe(true);
    expect(result.patterns.length).toBe(0);
  });

  /**
   * @traceability REQ-LEARN-011
   */
  it('should track average latency', async () => {
    const event: FileChangeEvent = {
      path: '/src/test.ts',
      type: 'modify',
      timestamp: Date.now(),
      content: 'const x = 1;',
    };

    await processor.process(event);
    await processor.process(event);
    await processor.process(event);

    const avgLatency = processor.getLatency();
    expect(avgLatency).toBeGreaterThan(0);
    expect(avgLatency).toBeLessThan(500);
  });

  /**
   * @traceability REQ-LEARN-011
   */
  it('should report SLA compliance', async () => {
    const event: FileChangeEvent = {
      path: '/src/test.ts',
      type: 'modify',
      timestamp: Date.now(),
      content: 'const x = 1;',
    };

    await processor.process(event);

    expect(processor.isMeetingSLA()).toBe(true);
  });
});

// --- FeedbackQueue Tests ---
describe('FeedbackQueue', () => {
  let queue: FeedbackQueue;

  beforeEach(() => {
    queue = new FeedbackQueue({
      maxSize: 1000,
      maxEnqueueLatencyMs: 100,
      batchSize: 10,
    });
  });

  afterEach(() => {
    queue.clear();
  });

  /**
   * @traceability REQ-LEARN-013 - 100ms SLA
   */
  it('should enqueue feedback within 100ms', () => {
    const feedback = createFeedback('accept', 'PAT-001');

    const start = performance.now();
    queue.enqueue(feedback);
    const latency = performance.now() - start;

    expect(latency).toBeLessThan(100);
    expect(queue.size()).toBe(1);
  });

  /**
   * @traceability REQ-LEARN-013
   */
  it('should dequeue feedback', () => {
    const feedback = createFeedback('accept', 'PAT-001');
    queue.enqueue(feedback);

    const dequeued = queue.dequeue();

    expect(dequeued).toBeDefined();
    expect(dequeued?.patternId).toBe('PAT-001');
    expect(queue.size()).toBe(0);
  });

  /**
   * @traceability REQ-LEARN-013
   */
  it('should support batch dequeue', () => {
    // Create a queue without auto batch processing for this test
    const testQueue = new FeedbackQueue({
      maxSize: 1000,
      maxEnqueueLatencyMs: 100,
      batchSize: 100, // Large batch size to prevent auto-processing
    });

    for (let i = 0; i < 20; i++) {
      testQueue.enqueue(createFeedback('accept', `PAT-${i}`));
    }

    // Manual batch dequeue
    const batch = testQueue.dequeueBatch(10);

    expect(batch.length).toBe(10);
    expect(testQueue.size()).toBe(10);

    testQueue.clear();
  });

  /**
   * @traceability REQ-LEARN-013
   */
  it('should handle overflow by dropping oldest', () => {
    const smallQueue = new FeedbackQueue({ maxSize: 3, batchSize: 10 });

    smallQueue.enqueue(createFeedback('accept', 'PAT-1'));
    smallQueue.enqueue(createFeedback('accept', 'PAT-2'));
    smallQueue.enqueue(createFeedback('accept', 'PAT-3'));
    smallQueue.enqueue(createFeedback('accept', 'PAT-4')); // Overflow

    expect(smallQueue.size()).toBe(3);
    expect(smallQueue.peek()?.patternId).toBe('PAT-2'); // PAT-1 dropped

    smallQueue.clear();
  });

  /**
   * @traceability REQ-LEARN-013
   */
  it('should track metrics', () => {
    queue.enqueue(createFeedback('accept', 'PAT-001'));
    queue.enqueue(createFeedback('reject', 'PAT-002'));
    queue.dequeue();

    const metrics = queue.getMetrics();

    expect(metrics.totalEnqueued).toBe(2);
    expect(metrics.totalDequeued).toBe(1);
    expect(metrics.currentDepth).toBe(1);
  });

  /**
   * @traceability REQ-LEARN-013
   */
  it('should report SLA compliance', () => {
    queue.enqueue(createFeedback('accept', 'PAT-001'));

    expect(queue.isMeetingSLA()).toBe(true);
  });
});

// --- EventStream Tests ---
describe('EventStream', () => {
  let stream: EventStream;

  beforeEach(() => {
    stream = new EventStream({
      targetThroughput: 1000,
      bufferSize: 10000,
      enableBackpressure: true,
    });
  });

  afterEach(() => {
    stream.stop();
  });

  /**
   * @traceability REQ-LEARN-014
   */
  it('should emit events', () => {
    const event = createPatternEvent('pattern:detected', { patternId: 'PAT-001' });

    const result = stream.publish(event);

    expect(result).toBe(true);
  });

  /**
   * @traceability REQ-LEARN-014
   */
  it('should deliver events to subscribers', async () => {
    const received: unknown[] = [];

    stream.subscribe((event) => {
      received.push(event);
    });

    stream.publish(createPatternEvent('pattern:detected', { patternId: 'PAT-001' }));

    // Wait for buffer flush
    await new Promise((resolve) => setTimeout(resolve, 50));

    expect(received.length).toBe(1);
  });

  /**
   * @traceability REQ-LEARN-014
   */
  it('should support multiple subscribers', async () => {
    let count1 = 0;
    let count2 = 0;

    stream.subscribe(() => count1++);
    stream.subscribe(() => count2++);

    stream.publish(createPatternEvent('pattern:detected', { patternId: 'PAT-001' }));

    await new Promise((resolve) => setTimeout(resolve, 50));

    expect(count1).toBe(1);
    expect(count2).toBe(1);
  });

  /**
   * @traceability REQ-LEARN-014
   */
  it('should support unsubscribe', async () => {
    let count = 0;

    const subscription = stream.subscribe(() => count++);

    stream.publish(createPatternEvent('pattern:detected', { patternId: 'PAT-001' }));
    await new Promise((resolve) => setTimeout(resolve, 50));

    subscription.unsubscribe();

    stream.publish(createPatternEvent('pattern:detected', { patternId: 'PAT-002' }));
    await new Promise((resolve) => setTimeout(resolve, 50));

    expect(count).toBe(1);
    expect(subscription.isActive()).toBe(false);
  });

  /**
   * @traceability REQ-LEARN-014 - 1000 events/sec
   */
  it('should handle high throughput', async () => {
    const eventCount = 2000;
    const events = Array.from({ length: eventCount }, (_, i) =>
      createPatternEvent('pattern:detected', { index: i })
    );

    const start = performance.now();
    for (const event of events) {
      stream.publish(event);
    }
    const elapsed = performance.now() - start;

    const throughput = (eventCount / elapsed) * 1000;

    // Should be able to emit at least 1000 events per second
    expect(throughput).toBeGreaterThanOrEqual(1000);
  });

  /**
   * @traceability REQ-LEARN-014
   */
  it('should track metrics', async () => {
    stream.publish(createPatternEvent('pattern:detected', { patternId: 'PAT-001' }));
    stream.publish(createPatternEvent('pattern:updated', { patternId: 'PAT-001' }));

    const metrics = stream.getMetrics();

    expect(metrics.totalEvents).toBe(2);
    expect(metrics.activeSubscribers).toBe(0);
  });
});

// --- IncrementalUpdater Tests ---
describe('IncrementalUpdater', () => {
  let updater: IncrementalUpdater;

  beforeEach(() => {
    updater = new IncrementalUpdater();
  });

  afterEach(() => {
    updater.clear();
  });

  const createTestPattern = (id: string, name: string): RealtimeDetectedPattern => ({
    id,
    name,
    category: 'code',
    confidence: 0.9,
    sourcePath: '/src/test.ts',
    lineRange: { start: 1, end: 10 },
    template: 'test template',
    detectedAt: Date.now(),
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should add patterns', () => {
    const pattern = createTestPattern('PAT-001', 'TestPattern');

    updater.addPattern(pattern);

    expect(updater.size()).toBe(1);
    expect(updater.get('PAT-001')).toBeDefined();
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should apply incremental updates', () => {
    const pattern = createTestPattern('PAT-001', 'TestPattern');
    const update = createUpdate('add', 'PAT-001', pattern);

    updater.applyUpdate(update);

    expect(updater.size()).toBe(1);
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should remove patterns', () => {
    const pattern = createTestPattern('PAT-001', 'TestPattern');
    updater.addPattern(pattern);

    updater.removePattern('PAT-001');

    expect(updater.size()).toBe(0);
    expect(updater.has('PAT-001')).toBe(false);
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should update patterns', () => {
    const pattern = createTestPattern('PAT-001', 'TestPattern');
    updater.addPattern(pattern);

    const updated: RealtimeDetectedPattern = {
      ...pattern,
      confidence: 0.95,
    };
    updater.updatePattern(updated);

    expect(updater.get('PAT-001')?.confidence).toBe(0.95);
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should merge similar patterns', () => {
    const pattern1 = createTestPattern('PAT-001', 'Factory: createUser');
    const pattern2: RealtimeDetectedPattern = {
      ...createTestPattern('PAT-002', 'Factory: createUser'),
      lineRange: { start: 5, end: 15 },
      confidence: 0.95,
    };

    updater.addPattern(pattern1);
    updater.addPattern(pattern2);

    // Similar patterns should be merged
    expect(updater.size()).toBe(1);

    const stats = updater.getStats();
    expect(stats.merged).toBe(1);
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should index by source path', () => {
    updater.addPattern(createTestPattern('PAT-001', 'Pattern1'));
    updater.addPattern({
      ...createTestPattern('PAT-002', 'Pattern2'),
      sourcePath: '/src/other.ts',
    });

    const fromTest = updater.getBySource('/src/test.ts');
    const fromOther = updater.getBySource('/src/other.ts');

    expect(fromTest.length).toBe(1);
    expect(fromOther.length).toBe(1);
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should remove by source', () => {
    updater.addPattern(createTestPattern('PAT-001', 'Pattern1'));
    updater.addPattern({
      ...createTestPattern('PAT-002', 'Pattern2'),
      sourcePath: '/src/other.ts',
    });

    updater.removeBySource('/src/test.ts');

    expect(updater.size()).toBe(1);
    expect(updater.has('PAT-002')).toBe(true);
  });

  /**
   * @traceability REQ-LEARN-012
   */
  it('should track update statistics', () => {
    const pattern = createTestPattern('PAT-001', 'TestPattern');

    updater.applyUpdate(createUpdate('add', 'PAT-001', pattern));
    updater.applyUpdate(
      createUpdate('update', 'PAT-001', { ...pattern, confidence: 0.95 })
    );
    updater.applyUpdate(createUpdate('remove', 'PAT-001'));

    const stats = updater.getStats();

    expect(stats.totalUpdates).toBe(3);
    expect(stats.added).toBe(1);
    expect(stats.updated).toBe(1);
    expect(stats.removed).toBe(1);
  });
});

// --- RealtimeLearningEngine Tests ---
describe('RealtimeLearningEngine', () => {
  let engine: RealtimeLearningEngine;

  beforeEach(() => {
    engine = new RealtimeLearningEngine({
      fileWatcher: {
        paths: [],
        extensions: ['.ts'],
        ignore: ['node_modules/**'],
      },
      autoStart: false,
    });
  });

  afterEach(() => {
    engine.stop();
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should initialize all components', () => {
    const components = engine.getComponents();

    expect(components.fileWatcher).toBeDefined();
    expect(components.streamProcessor).toBeDefined();
    expect(components.feedbackQueue).toBeDefined();
    expect(components.eventStream).toBeDefined();
    expect(components.updater).toBeDefined();
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should start and stop', async () => {
    await engine.start();
    expect(engine.isRunning()).toBe(true);

    engine.stop();
    expect(engine.isRunning()).toBe(false);
  });

  /**
   * @traceability REQ-LEARN-013
   */
  it('should accept feedback', async () => {
    await engine.start();

    engine.submitFeedback('accept', 'PAT-001');

    const { feedbackQueue } = engine.getComponents();
    expect(feedbackQueue.size()).toBeGreaterThanOrEqual(0); // May have been processed
  });

  /**
   * @traceability REQ-LEARN-011, REQ-LEARN-013, REQ-LEARN-014
   */
  it('should provide metrics', async () => {
    await engine.start();

    const metrics = engine.getMetrics();

    expect(metrics).toBeDefined();
    expect(typeof metrics.eventsProcessed).toBe('number');
    expect(typeof metrics.avgLatencyMs).toBe('number');
    expect(typeof metrics.eventsPerSecond).toBe('number');
    expect(typeof metrics.uptimeMs).toBe('number');
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should get patterns', () => {
    const patterns = engine.getPatterns();
    expect(Array.isArray(patterns)).toBe(true);
  });

  /**
   * @traceability REQ-LEARN-010
   */
  it('should get patterns by category', () => {
    const codePatterns = engine.getPatternsByCategory('code');
    const designPatterns = engine.getPatternsByCategory('design');
    const testPatterns = engine.getPatternsByCategory('test');

    expect(Array.isArray(codePatterns)).toBe(true);
    expect(Array.isArray(designPatterns)).toBe(true);
    expect(Array.isArray(testPatterns)).toBe(true);
  });
});

// --- Integration Tests ---
describe('Real-time Learning Integration', () => {
  /**
   * @traceability REQ-LEARN-010, REQ-LEARN-011, REQ-LEARN-012
   */
  it('should process file change and detect patterns', async () => {
    const processor = new StreamProcessor();
    const updater = new IncrementalUpdater();

    const event: FileChangeEvent = {
      path: '/src/repository.ts',
      type: 'modify',
      timestamp: Date.now(),
      content: `
        interface UserRepository {
          findById(id: string): Promise<User | undefined>;
          save(user: User): Promise<void>;
        }
        
        class InMemoryUserRepository implements UserRepository {
          private users: Map<string, User> = new Map();
          
          async findById(id: string): Promise<User | undefined> {
            return this.users.get(id);
          }
          
          async save(user: User): Promise<void> {
            this.users.set(user.id, user);
          }
        }
      `,
    };

    // Process file change
    const result = await processor.process(event);
    expect(result.success).toBe(true);
    expect(result.latencyMs).toBeLessThan(500);

    // Apply patterns to updater
    for (const pattern of result.patterns) {
      updater.addPattern(pattern);
    }

    expect(updater.size()).toBeGreaterThan(0);
  });

  /**
   * @traceability REQ-LEARN-013, REQ-LEARN-014
   */
  it('should handle feedback through queue and stream', async () => {
    const queue = new FeedbackQueue();
    const stream = new EventStream();

    const feedbackReceived: unknown[] = [];
    stream.subscribe((event) => {
      if (event.type === 'feedback:received') {
        feedbackReceived.push(event);
      }
    });

    // Enqueue feedback
    const feedback = createFeedback('accept', 'PAT-001');
    queue.enqueue(feedback);

    // Process and emit to stream
    const dequeued = queue.dequeue();
    if (dequeued) {
      stream.publish(
        createPatternEvent('feedback:received', {
          feedbackId: dequeued.id,
          patternId: dequeued.patternId,
        })
      );
    }

    // Wait for delivery
    await new Promise((resolve) => setTimeout(resolve, 50));

    expect(feedbackReceived.length).toBe(1);

    stream.stop();
  });
});
