/**
 * Performance Profiler
 * 
 * Profiles and measures system performance
 * 
 * @packageDocumentation
 * @module utils/performance-profiler
 * 
 * @see REQ-PER-001 - Performance Monitoring
 * @see Article VI - Decision Transparency
 */

/**
 * Profile entry type
 */
export type ProfileEntryType = 'function' | 'api' | 'query' | 'io' | 'custom';

/**
 * Profile entry
 */
export interface ProfileEntry {
  /** Entry ID */
  id: string;
  /** Name */
  name: string;
  /** Type */
  type: ProfileEntryType;
  /** Start time */
  startTime: number;
  /** End time */
  endTime?: number;
  /** Duration (ms) */
  duration?: number;
  /** Parent entry ID */
  parentId?: string;
  /** Child entry IDs */
  children: string[];
  /** Metadata */
  metadata?: Record<string, unknown>;
  /** Memory usage */
  memoryUsage?: {
    heapUsed: number;
    heapTotal: number;
    external: number;
  };
}

/**
 * Profile statistics
 */
export interface ProfileStats {
  /** Name */
  name: string;
  /** Call count */
  count: number;
  /** Total duration (ms) */
  totalDuration: number;
  /** Average duration (ms) */
  avgDuration: number;
  /** Min duration (ms) */
  minDuration: number;
  /** Max duration (ms) */
  maxDuration: number;
  /** Standard deviation */
  stdDev: number;
  /** Median */
  median: number;
  /** 95th percentile */
  p95: number;
  /** 99th percentile */
  p99: number;
}

/**
 * Memory snapshot
 */
export interface MemorySnapshot {
  /** Timestamp */
  timestamp: number;
  /** Heap used */
  heapUsed: number;
  /** Heap total */
  heapTotal: number;
  /** External */
  external: number;
  /** Array buffers */
  arrayBuffers: number;
  /** RSS */
  rss: number;
}

/**
 * Performance report
 */
export interface PerformanceReport {
  /** Report ID */
  id: string;
  /** Timestamp */
  timestamp: Date;
  /** Duration (ms) */
  duration: number;
  /** Total entries */
  totalEntries: number;
  /** Entries by type */
  byType: Record<ProfileEntryType, number>;
  /** Top slowest */
  slowest: Array<{ name: string; duration: number }>;
  /** Statistics */
  stats: ProfileStats[];
  /** Memory snapshots */
  memorySnapshots: MemorySnapshot[];
  /** Hotspots */
  hotspots: Array<{
    name: string;
    percentage: number;
    duration: number;
  }>;
  /** Recommendations */
  recommendations: string[];
}

/**
 * Profiler config
 */
export interface ProfilerConfig {
  /** Enabled */
  enabled: boolean;
  /** Sample rate (0-1) */
  sampleRate: number;
  /** Max entries */
  maxEntries: number;
  /** Capture memory */
  captureMemory: boolean;
  /** Memory snapshot interval (ms) */
  memoryInterval: number;
  /** Slow threshold (ms) */
  slowThreshold: number;
}

/**
 * Default configuration
 */
export const DEFAULT_PROFILER_CONFIG: ProfilerConfig = {
  enabled: true,
  sampleRate: 1.0,
  maxEntries: 10000,
  captureMemory: true,
  memoryInterval: 1000,
  slowThreshold: 100,
};

/**
 * Performance Profiler
 */
export class PerformanceProfiler {
  private config: ProfilerConfig;
  private entries: Map<string, ProfileEntry> = new Map();
  private entryStack: string[] = [];
  private memorySnapshots: MemorySnapshot[] = [];
  private memoryTimer?: ReturnType<typeof setInterval>;
  private startTime = 0;
  private entryCounter = 0;

  constructor(config?: Partial<ProfilerConfig>) {
    this.config = { ...DEFAULT_PROFILER_CONFIG, ...config };
  }

  /**
   * Start profiling session
   */
  start(): void {
    if (!this.config.enabled) return;

    this.entries.clear();
    this.entryStack = [];
    this.memorySnapshots = [];
    this.startTime = this.now();
    this.entryCounter = 0;

    if (this.config.captureMemory) {
      this.startMemoryCapture();
    }
  }

  /**
   * Stop profiling session
   */
  stop(): PerformanceReport {
    if (this.memoryTimer) {
      clearInterval(this.memoryTimer);
      this.memoryTimer = undefined;
    }

    // Close any remaining entries
    while (this.entryStack.length > 0) {
      this.end();
    }

    return this.generateReport();
  }

  /**
   * Begin profiling an operation
   */
  begin(name: string, type: ProfileEntryType = 'function', metadata?: Record<string, unknown>): string {
    if (!this.config.enabled) return '';
    if (Math.random() > this.config.sampleRate) return '';
    if (this.entries.size >= this.config.maxEntries) return '';

    const id = `profile-${++this.entryCounter}-${Date.now()}`;
    const parentId = this.entryStack.length > 0 ? this.entryStack[this.entryStack.length - 1] : undefined;

    const entry: ProfileEntry = {
      id,
      name,
      type,
      startTime: this.now(),
      children: [],
      metadata,
    };

    if (this.config.captureMemory) {
      entry.memoryUsage = this.captureMemory();
    }

    if (parentId) {
      entry.parentId = parentId;
      const parent = this.entries.get(parentId);
      if (parent) {
        parent.children.push(id);
      }
    }

    this.entries.set(id, entry);
    this.entryStack.push(id);

    return id;
  }

  /**
   * End profiling current operation
   */
  end(id?: string): void {
    if (!this.config.enabled) return;

    const entryId = id ?? this.entryStack.pop();
    if (!entryId) return;

    const entry = this.entries.get(entryId);
    if (entry && !entry.endTime) {
      entry.endTime = this.now();
      entry.duration = entry.endTime - entry.startTime;
    }

    // Remove from stack if specified ID
    if (id) {
      const index = this.entryStack.indexOf(id);
      if (index > -1) {
        this.entryStack.splice(index, 1);
      }
    }
  }

  /**
   * Profile a function
   */
  profile<T>(name: string, fn: () => T, type: ProfileEntryType = 'function'): T {
    const id = this.begin(name, type);
    try {
      return fn();
    } finally {
      this.end(id);
    }
  }

  /**
   * Profile an async function
   */
  async profileAsync<T>(
    name: string, 
    fn: () => Promise<T>, 
    type: ProfileEntryType = 'function'
  ): Promise<T> {
    const id = this.begin(name, type);
    try {
      return await fn();
    } finally {
      this.end(id);
    }
  }

  /**
   * Create a timer for measuring duration
   */
  createTimer(name: string, type: ProfileEntryType = 'custom'): {
    stop: () => number;
  } {
    const start = this.now();
    const id = this.begin(name, type);

    return {
      stop: () => {
        this.end(id);
        return this.now() - start;
      },
    };
  }

  /**
   * Mark a point in time
   */
  mark(name: string, metadata?: Record<string, unknown>): void {
    const id = this.begin(name, 'custom', metadata);
    this.end(id);
  }

  /**
   * Get current entry
   */
  getCurrentEntry(): ProfileEntry | undefined {
    if (this.entryStack.length === 0) return undefined;
    return this.entries.get(this.entryStack[this.entryStack.length - 1]);
  }

  /**
   * Get all entries
   */
  getEntries(): ProfileEntry[] {
    return Array.from(this.entries.values());
  }

  /**
   * Get entries by type
   */
  getEntriesByType(type: ProfileEntryType): ProfileEntry[] {
    return this.getEntries().filter((e) => e.type === type);
  }

  /**
   * Get slow entries
   */
  getSlowEntries(): ProfileEntry[] {
    return this.getEntries()
      .filter((e) => e.duration && e.duration >= this.config.slowThreshold)
      .sort((a, b) => (b.duration ?? 0) - (a.duration ?? 0));
  }

  /**
   * Calculate statistics for a name
   */
  getStats(name: string): ProfileStats | null {
    const entries = this.getEntries().filter((e) => e.name === name && e.duration !== undefined);
    if (entries.length === 0) return null;

    const durations = entries.map((e) => e.duration!).sort((a, b) => a - b);
    const totalDuration = durations.reduce((sum, d) => sum + d, 0);
    const avgDuration = totalDuration / durations.length;
    
    // Calculate standard deviation
    const variance = durations.reduce((sum, d) => sum + Math.pow(d - avgDuration, 2), 0) / durations.length;
    const stdDev = Math.sqrt(variance);

    return {
      name,
      count: entries.length,
      totalDuration,
      avgDuration,
      minDuration: durations[0],
      maxDuration: durations[durations.length - 1],
      stdDev,
      median: this.percentile(durations, 50),
      p95: this.percentile(durations, 95),
      p99: this.percentile(durations, 99),
    };
  }

  /**
   * Generate performance report
   */
  generateReport(): PerformanceReport {
    const entries = this.getEntries().filter((e) => e.duration !== undefined);
    const duration = this.now() - this.startTime;

    // Count by type
    const byType: Record<ProfileEntryType, number> = {
      function: 0,
      api: 0,
      query: 0,
      io: 0,
      custom: 0,
    };

    for (const entry of entries) {
      byType[entry.type]++;
    }

    // Get unique names
    const uniqueNames = [...new Set(entries.map((e) => e.name))];
    const stats: ProfileStats[] = [];

    for (const name of uniqueNames) {
      const stat = this.getStats(name);
      if (stat) {
        stats.push(stat);
      }
    }

    // Sort by total duration
    stats.sort((a, b) => b.totalDuration - a.totalDuration);

    // Calculate hotspots
    const totalTime = stats.reduce((sum, s) => sum + s.totalDuration, 0);
    const hotspots = stats.slice(0, 10).map((s) => ({
      name: s.name,
      percentage: totalTime > 0 ? (s.totalDuration / totalTime) * 100 : 0,
      duration: s.totalDuration,
    }));

    // Get slowest entries
    const slowest = this.getSlowEntries().slice(0, 10).map((e) => ({
      name: e.name,
      duration: e.duration ?? 0,
    }));

    // Generate recommendations
    const recommendations = this.generateRecommendations(stats, hotspots);

    return {
      id: `report-${Date.now()}`,
      timestamp: new Date(),
      duration,
      totalEntries: entries.length,
      byType,
      slowest,
      stats: stats.slice(0, 20),
      memorySnapshots: this.memorySnapshots,
      hotspots,
      recommendations,
    };
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(
    stats: ProfileStats[],
    hotspots: Array<{ name: string; percentage: number; duration: number }>
  ): string[] {
    const recommendations: string[] = [];

    // High percentage hotspots
    const highHotspots = hotspots.filter((h) => h.percentage > 20);
    for (const hotspot of highHotspots) {
      recommendations.push(
        `"${hotspot.name}" accounts for ${hotspot.percentage.toFixed(1)}% of execution time. Consider optimizing.`
      );
    }

    // High variance
    const highVariance = stats.filter((s) => s.stdDev > s.avgDuration * 0.5 && s.count > 5);
    for (const stat of highVariance.slice(0, 3)) {
      recommendations.push(
        `"${stat.name}" has high variance (stdDev: ${stat.stdDev.toFixed(1)}ms). Performance may be inconsistent.`
      );
    }

    // High p99
    const highP99 = stats.filter((s) => s.p99 > s.avgDuration * 3 && s.count > 10);
    for (const stat of highP99.slice(0, 3)) {
      recommendations.push(
        `"${stat.name}" has high p99 (${stat.p99.toFixed(1)}ms vs avg ${stat.avgDuration.toFixed(1)}ms). Check for outliers.`
      );
    }

    // Memory growth
    if (this.memorySnapshots.length > 1) {
      const first = this.memorySnapshots[0];
      const last = this.memorySnapshots[this.memorySnapshots.length - 1];
      const growth = ((last.heapUsed - first.heapUsed) / first.heapUsed) * 100;

      if (growth > 50) {
        recommendations.push(
          `Memory grew by ${growth.toFixed(1)}% during profiling. Check for memory leaks.`
        );
      }
    }

    if (recommendations.length === 0) {
      recommendations.push('Performance looks good! No critical issues detected.');
    }

    return recommendations;
  }

  /**
   * Start memory capture
   */
  private startMemoryCapture(): void {
    this.captureMemorySnapshot();

    this.memoryTimer = setInterval(() => {
      this.captureMemorySnapshot();
    }, this.config.memoryInterval);
  }

  /**
   * Capture memory snapshot
   */
  private captureMemorySnapshot(): void {
    const snapshot = this.captureMemory();
    this.memorySnapshots.push({
      timestamp: this.now(),
      ...snapshot,
      arrayBuffers: 0,
      rss: 0,
    });
  }

  /**
   * Capture memory usage
   */
  private captureMemory(): { heapUsed: number; heapTotal: number; external: number } {
    // In Node.js environment
    if (typeof process !== 'undefined' && process.memoryUsage) {
      const usage = process.memoryUsage();
      return {
        heapUsed: usage.heapUsed,
        heapTotal: usage.heapTotal,
        external: usage.external,
      };
    }

    // In browser environment
    if (typeof performance !== 'undefined' && (performance as any).memory) {
      const memory = (performance as any).memory;
      return {
        heapUsed: memory.usedJSHeapSize,
        heapTotal: memory.totalJSHeapSize,
        external: 0,
      };
    }

    return { heapUsed: 0, heapTotal: 0, external: 0 };
  }

  /**
   * Get current time (high resolution)
   */
  private now(): number {
    if (typeof performance !== 'undefined') {
      return performance.now();
    }
    return Date.now();
  }

  /**
   * Calculate percentile
   */
  private percentile(sorted: number[], p: number): number {
    if (sorted.length === 0) return 0;
    const index = Math.ceil((p / 100) * sorted.length) - 1;
    return sorted[Math.max(0, Math.min(index, sorted.length - 1))];
  }

  /**
   * Format report as string
   */
  formatReport(report: PerformanceReport): string {
    const lines: string[] = [];

    lines.push('# Performance Report');
    lines.push('');
    lines.push(`**Generated:** ${report.timestamp.toISOString()}`);
    lines.push(`**Duration:** ${report.duration.toFixed(2)}ms`);
    lines.push(`**Total Entries:** ${report.totalEntries}`);
    lines.push('');

    // By type
    lines.push('## Entries by Type');
    lines.push('');
    lines.push('| Type | Count |');
    lines.push('|------|-------|');
    for (const [type, count] of Object.entries(report.byType)) {
      if (count > 0) {
        lines.push(`| ${type} | ${count} |`);
      }
    }
    lines.push('');

    // Hotspots
    lines.push('## Hotspots');
    lines.push('');
    lines.push('| Name | % Time | Duration |');
    lines.push('|------|--------|----------|');
    for (const hotspot of report.hotspots) {
      lines.push(`| ${hotspot.name} | ${hotspot.percentage.toFixed(1)}% | ${hotspot.duration.toFixed(2)}ms |`);
    }
    lines.push('');

    // Top slowest
    if (report.slowest.length > 0) {
      lines.push('## Slowest Operations');
      lines.push('');
      lines.push('| Name | Duration |');
      lines.push('|------|----------|');
      for (const slow of report.slowest) {
        lines.push(`| ${slow.name} | ${slow.duration.toFixed(2)}ms |`);
      }
      lines.push('');
    }

    // Statistics
    lines.push('## Statistics');
    lines.push('');
    lines.push('| Name | Count | Avg | Min | Max | p95 | p99 |');
    lines.push('|------|-------|-----|-----|-----|-----|-----|');
    for (const stat of report.stats.slice(0, 10)) {
      lines.push(
        `| ${stat.name} | ${stat.count} | ${stat.avgDuration.toFixed(1)}ms | ` +
        `${stat.minDuration.toFixed(1)}ms | ${stat.maxDuration.toFixed(1)}ms | ` +
        `${stat.p95.toFixed(1)}ms | ${stat.p99.toFixed(1)}ms |`
      );
    }
    lines.push('');

    // Recommendations
    lines.push('## Recommendations');
    lines.push('');
    for (const rec of report.recommendations) {
      lines.push(`- ${rec}`);
    }
    lines.push('');

    return lines.join('\n');
  }
}

/**
 * Create decorator for profiling methods
 */
export function profiled(
  profiler: PerformanceProfiler,
  type: ProfileEntryType = 'function'
): MethodDecorator {
  return function (
    _target: object,
    propertyKey: string | symbol,
    descriptor: PropertyDescriptor
  ): PropertyDescriptor {
    const originalMethod = descriptor.value;
    const name = String(propertyKey);

    descriptor.value = function (...args: unknown[]) {
      return profiler.profile(name, () => originalMethod.apply(this, args), type);
    };

    return descriptor;
  };
}

/**
 * Create performance profiler instance
 */
export function createPerformanceProfiler(config?: Partial<ProfilerConfig>): PerformanceProfiler {
  return new PerformanceProfiler(config);
}

/**
 * Global profiler instance
 */
export const globalProfiler = new PerformanceProfiler();
