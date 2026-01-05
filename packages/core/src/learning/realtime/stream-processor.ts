/**
 * StreamProcessor - Real-time Event Processing
 *
 * Processes file change events and extracts patterns within 500ms SLA.
 *
 * @see REQ-LEARN-011 - 500ms Analysis Latency
 * @see DES-LEARN-010 - StreamProcessor Component
 * @module @musubix/core/learning/realtime
 */

import {
  type FileChangeEvent,
  type ProcessResult,
  type RealtimeDetectedPattern,
  type StreamProcessorConfig,
  DEFAULT_STREAM_PROCESSOR_CONFIG,
} from './types.js';

/**
 * Pattern matcher function type
 */
type PatternMatcher = (content: string, filePath: string) => RealtimeDetectedPattern[];

/**
 * Built-in pattern matchers
 */
const BUILTIN_MATCHERS: PatternMatcher[] = [
  // Factory Pattern Matcher
  (content: string, filePath: string): RealtimeDetectedPattern[] => {
    const patterns: RealtimeDetectedPattern[] = [];
    const factoryRegex =
      /(?:function|const)\s+create(\w+)\s*(?:=\s*)?(?:\([^)]*\))?[^{]*\{/g;
    let match;

    while ((match = factoryRegex.exec(content)) !== null) {
      const lineNumber = content.substring(0, match.index).split('\n').length;
      patterns.push({
        id: `PAT-${Date.now()}-${Math.random().toString(36).substring(7)}`,
        name: `Factory: create${match[1]}`,
        category: 'code',
        confidence: 0.85,
        sourcePath: filePath,
        lineRange: { start: lineNumber, end: lineNumber + 10 },
        template: match[0],
        detectedAt: Date.now(),
      });
    }

    return patterns;
  },

  // Repository Pattern Matcher
  (content: string, filePath: string): RealtimeDetectedPattern[] => {
    const patterns: RealtimeDetectedPattern[] = [];
    const repoRegex =
      /(?:class|interface)\s+(\w*Repository)\s*(?:implements|extends)?[^{]*\{/g;
    let match;

    while ((match = repoRegex.exec(content)) !== null) {
      const lineNumber = content.substring(0, match.index).split('\n').length;
      patterns.push({
        id: `PAT-${Date.now()}-${Math.random().toString(36).substring(7)}`,
        name: `Repository: ${match[1]}`,
        category: 'design',
        confidence: 0.9,
        sourcePath: filePath,
        lineRange: { start: lineNumber, end: lineNumber + 20 },
        template: match[0],
        detectedAt: Date.now(),
      });
    }

    return patterns;
  },

  // Service Pattern Matcher
  (content: string, filePath: string): RealtimeDetectedPattern[] => {
    const patterns: RealtimeDetectedPattern[] = [];
    const serviceRegex =
      /(?:class|interface)\s+(\w*Service)\s*(?:implements|extends)?[^{]*\{/g;
    let match;

    while ((match = serviceRegex.exec(content)) !== null) {
      const lineNumber = content.substring(0, match.index).split('\n').length;
      patterns.push({
        id: `PAT-${Date.now()}-${Math.random().toString(36).substring(7)}`,
        name: `Service: ${match[1]}`,
        category: 'design',
        confidence: 0.88,
        sourcePath: filePath,
        lineRange: { start: lineNumber, end: lineNumber + 20 },
        template: match[0],
        detectedAt: Date.now(),
      });
    }

    return patterns;
  },

  // Result Type Pattern Matcher
  (content: string, filePath: string): RealtimeDetectedPattern[] => {
    const patterns: RealtimeDetectedPattern[] = [];
    const resultRegex = /Result<\s*(\w+)\s*,\s*(\w+)\s*>/g;
    let match;

    while ((match = resultRegex.exec(content)) !== null) {
      const lineNumber = content.substring(0, match.index).split('\n').length;
      patterns.push({
        id: `PAT-${Date.now()}-${Math.random().toString(36).substring(7)}`,
        name: `Result Type: Result<${match[1]}, ${match[2]}>`,
        category: 'code',
        confidence: 0.92,
        sourcePath: filePath,
        lineRange: { start: lineNumber, end: lineNumber },
        template: match[0],
        detectedAt: Date.now(),
      });
    }

    return patterns;
  },

  // Test Pattern Matcher
  (content: string, filePath: string): RealtimeDetectedPattern[] => {
    const patterns: RealtimeDetectedPattern[] = [];

    // Only match in test files
    if (!filePath.includes('.test.') && !filePath.includes('.spec.')) {
      return patterns;
    }

    const testRegex = /describe\s*\(\s*['"`]([^'"`]+)['"`]/g;
    let match;

    while ((match = testRegex.exec(content)) !== null) {
      const lineNumber = content.substring(0, match.index).split('\n').length;
      patterns.push({
        id: `PAT-${Date.now()}-${Math.random().toString(36).substring(7)}`,
        name: `Test Suite: ${match[1]}`,
        category: 'test',
        confidence: 0.95,
        sourcePath: filePath,
        lineRange: { start: lineNumber, end: lineNumber + 50 },
        template: match[0],
        detectedAt: Date.now(),
      });
    }

    return patterns;
  },
];

/**
 * StreamProcessor - Processes file changes and extracts patterns
 *
 * @example
 * ```typescript
 * const processor = new StreamProcessor();
 * const result = await processor.process(fileChangeEvent);
 * console.log(`Processed in ${result.latencyMs}ms`);
 * ```
 */
export class StreamProcessor {
  private readonly config: StreamProcessorConfig;
  private readonly matchers: PatternMatcher[];
  private latencyHistory: number[] = [];
  private readonly maxHistorySize = 100;

  constructor(
    config: Partial<StreamProcessorConfig> = {},
    additionalMatchers: PatternMatcher[] = []
  ) {
    this.config = { ...DEFAULT_STREAM_PROCESSOR_CONFIG, ...config };
    this.matchers = [...BUILTIN_MATCHERS, ...additionalMatchers];
  }

  /**
   * Process a file change event
   * @traceability REQ-LEARN-011 - Must complete within 500ms
   */
  async process(event: FileChangeEvent): Promise<ProcessResult> {
    const startTime = performance.now();

    try {
      // Skip delete events
      if (event.type === 'delete' || !event.content) {
        return this.createResult(startTime, true, []);
      }

      // Extract patterns
      const patterns = await this.extractPatterns(event);

      // Filter by confidence
      const filteredPatterns = patterns.filter(
        (p) => p.confidence >= this.config.minConfidence
      );

      return this.createResult(startTime, true, filteredPatterns);
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      return this.createResult(startTime, false, [], errorMessage);
    }
  }

  /**
   * Get current average latency
   */
  getLatency(): number {
    if (this.latencyHistory.length === 0) {
      return 0;
    }
    const sum = this.latencyHistory.reduce((a, b) => a + b, 0);
    return sum / this.latencyHistory.length;
  }

  /**
   * Get maximum latency from history
   */
  getMaxLatency(): number {
    if (this.latencyHistory.length === 0) {
      return 0;
    }
    return Math.max(...this.latencyHistory);
  }

  /**
   * Check if processor is meeting SLA
   * @traceability REQ-LEARN-011
   */
  isMeetingSLA(): boolean {
    return this.getMaxLatency() <= this.config.maxLatencyMs;
  }

  /**
   * Extract patterns from file content
   */
  private async extractPatterns(event: FileChangeEvent): Promise<RealtimeDetectedPattern[]> {
    const content = event.content!;
    const patterns: RealtimeDetectedPattern[] = [];

    // Run all matchers (could be parallelized for larger files)
    for (const matcher of this.matchers) {
      try {
        const matched = matcher(content, event.path);
        patterns.push(...matched);
      } catch {
        // Skip failed matchers
      }
    }

    // Deduplicate patterns by similar template
    return this.deduplicatePatterns(patterns);
  }

  /**
   * Deduplicate similar patterns
   */
  private deduplicatePatterns(patterns: RealtimeDetectedPattern[]): RealtimeDetectedPattern[] {
    const seen = new Set<string>();
    const unique: RealtimeDetectedPattern[] = [];

    for (const pattern of patterns) {
      const key = `${pattern.name}-${pattern.lineRange.start}`;
      if (!seen.has(key)) {
        seen.add(key);
        unique.push(pattern);
      }
    }

    return unique;
  }

  /**
   * Create process result and track latency
   */
  private createResult(
    startTime: number,
    success: boolean,
    patterns: RealtimeDetectedPattern[],
    error?: string
  ): ProcessResult {
    const latencyMs = performance.now() - startTime;

    // Track latency
    this.latencyHistory.push(latencyMs);
    if (this.latencyHistory.length > this.maxHistorySize) {
      this.latencyHistory.shift();
    }

    return {
      success,
      latencyMs,
      patterns,
      error,
    };
  }
}
