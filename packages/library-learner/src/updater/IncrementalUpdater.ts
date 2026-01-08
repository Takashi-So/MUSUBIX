/**
 * IncrementalUpdater - Fast Incremental Pattern Updates
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-107
 * @see DES-LL-107
 * @see REQ-PERF-002 (5秒/500LOC目標)
 *
 * ファイル変更時のインクリメンタル更新により、
 * 500LOCの変更を5秒以内で処理することを目標とする
 */

// =============================================================================
// Types
// =============================================================================

/**
 * Types of file changes
 */
export type ChangeType = 'added' | 'modified' | 'deleted';

/**
 * File change descriptor
 */
export interface FileChange {
  /** Absolute file path */
  filePath: string;
  /** Type of change */
  changeType: ChangeType;
  /** Affected line numbers */
  affectedLines: number[];
  /** Change timestamp */
  timestamp: number;
  /** Optional: previous content hash */
  previousHash?: string;
  /** Optional: new content hash */
  newHash?: string;
}

/**
 * Result of processing a single change
 */
export interface UpdateResult {
  /** Was processing successful */
  success: boolean;
  /** Type of change processed */
  changeType: ChangeType;
  /** Processing time in ms */
  processingTimeMs: number;
  /** Patterns affected by this change */
  affectedPatterns: string[];
  /** Files that depend on the changed file */
  dependentFiles: string[];
  /** Was cache hit used */
  cacheHit: boolean;
  /** Error message if failed */
  error?: string;
}

/**
 * Updater configuration
 */
export interface UpdaterConfig {
  /** Maximum cache size (entries) */
  maxCacheSize?: number;
  /** Enable parallel processing */
  enableParallelProcessing?: boolean;
  /** Batch size for parallel processing */
  batchSize?: number;
  /** Debounce time for rapid changes (ms) */
  debounceMs?: number;
}

/**
 * Update statistics
 */
export interface UpdateStatistics {
  /** Total changes processed */
  totalChangesProcessed: number;
  /** Cache hits */
  cacheHits: number;
  /** Cache misses */
  cacheMisses: number;
  /** Current cache size */
  cacheSize: number;
  /** Average processing time in ms */
  averageProcessingTimeMs: number;
  /** Total processing time in ms */
  totalProcessingTimeMs: number;
}

/**
 * Cached file info
 */
interface CachedFileInfo {
  filePath: string;
  hash: string;
  patterns: string[];
  dependencies: string[];
  lastProcessed: number;
}

/**
 * IncrementalUpdater interface
 */
export interface IncrementalUpdater {
  /**
   * Process a single file change
   */
  processChange(change: FileChange): Promise<UpdateResult>;

  /**
   * Process multiple changes in batch
   */
  processBatch(changes: FileChange[]): Promise<UpdateResult[]>;

  /**
   * Get dependencies for a file
   */
  getDependencies(filePath: string): string[];

  /**
   * Get statistics
   */
  getStatistics(): UpdateStatistics;

  /**
   * Reset all state
   */
  reset(): void;

  /**
   * Clear only cache
   */
  clearCache(): void;

  /**
   * Serialize state
   */
  toJSON(): string;

  /**
   * Restore state
   */
  fromJSON(json: string): void;
}

// =============================================================================
// Default Implementation
// =============================================================================

/**
 * Default implementation of IncrementalUpdater
 */
class DefaultIncrementalUpdater implements IncrementalUpdater {
  private config: Required<UpdaterConfig>;
  private cache: Map<string, CachedFileInfo>;
  private dependencies: Map<string, Set<string>>;
  private statistics: UpdateStatistics;

  constructor(config: UpdaterConfig = {}) {
    this.config = {
      maxCacheSize: config.maxCacheSize ?? 1000,
      enableParallelProcessing: config.enableParallelProcessing ?? true,
      batchSize: config.batchSize ?? 50,
      debounceMs: config.debounceMs ?? 100,
    };

    this.cache = new Map();
    this.dependencies = new Map();
    this.statistics = this.createInitialStatistics();
  }

  async processChange(change: FileChange): Promise<UpdateResult> {
    const startTime = Date.now();

    try {
      // Check cache
      const cached = this.cache.get(change.filePath);
      const isCacheHit = this.checkCacheValid(cached, change);

      if (isCacheHit && cached) {
        // Cache hit - minimal processing
        this.statistics.cacheHits++;
        const processingTime = Date.now() - startTime;
        this.updateProcessingStats(processingTime);

        return {
          success: true,
          changeType: change.changeType,
          processingTimeMs: processingTime,
          affectedPatterns: cached.patterns,
          dependentFiles: this.getReverseDependencies(change.filePath),
          cacheHit: true,
        };
      }

      // Cache miss - full processing
      this.statistics.cacheMisses++;

      // Process based on change type
      const result = await this.processChangeInternal(change);

      // Update cache
      this.updateCache(change, result);

      const processingTime = Date.now() - startTime;
      this.updateProcessingStats(processingTime);

      return {
        success: true,
        changeType: change.changeType,
        processingTimeMs: processingTime,
        affectedPatterns: result.patterns,
        dependentFiles: this.getReverseDependencies(change.filePath),
        cacheHit: false,
      };
    } catch (error) {
      const processingTime = Date.now() - startTime;
      this.updateProcessingStats(processingTime);

      return {
        success: false,
        changeType: change.changeType,
        processingTimeMs: processingTime,
        affectedPatterns: [],
        dependentFiles: [],
        cacheHit: false,
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  async processBatch(changes: FileChange[]): Promise<UpdateResult[]> {
    if (changes.length === 0) {
      return [];
    }

    if (this.config.enableParallelProcessing) {
      // Process in parallel batches
      const results: UpdateResult[] = [];

      for (let i = 0; i < changes.length; i += this.config.batchSize) {
        const batch = changes.slice(i, i + this.config.batchSize);
        const batchResults = await Promise.all(
          batch.map((change) => this.processChange(change))
        );
        results.push(...batchResults);
      }

      return results;
    } else {
      // Process sequentially
      const results: UpdateResult[] = [];
      for (const change of changes) {
        results.push(await this.processChange(change));
      }
      return results;
    }
  }

  getDependencies(filePath: string): string[] {
    const deps = this.dependencies.get(filePath);
    return deps ? Array.from(deps) : [];
  }

  getStatistics(): UpdateStatistics {
    return {
      ...this.statistics,
      cacheSize: this.cache.size,
    };
  }

  reset(): void {
    this.cache.clear();
    this.dependencies.clear();
    this.statistics = this.createInitialStatistics();
  }

  clearCache(): void {
    this.cache.clear();
  }

  toJSON(): string {
    return JSON.stringify({
      config: this.config,
      statistics: this.statistics,
      cacheEntries: Array.from(this.cache.entries()).map(([k, v]) => ({
        key: k,
        value: v,
      })),
      dependencyEntries: Array.from(this.dependencies.entries()).map(
        ([k, v]) => ({ key: k, value: Array.from(v) })
      ),
    });
  }

  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.statistics) {
      this.statistics = { ...this.statistics, ...data.statistics };
    }

    if (data.cacheEntries) {
      this.cache.clear();
      for (const entry of data.cacheEntries) {
        this.cache.set(entry.key, entry.value);
      }
    }

    if (data.dependencyEntries) {
      this.dependencies.clear();
      for (const entry of data.dependencyEntries) {
        this.dependencies.set(entry.key, new Set(entry.value));
      }
    }
  }

  // =========================================================================
  // Private Methods
  // =========================================================================

  private createInitialStatistics(): UpdateStatistics {
    return {
      totalChangesProcessed: 0,
      cacheHits: 0,
      cacheMisses: 0,
      cacheSize: 0,
      averageProcessingTimeMs: 0,
      totalProcessingTimeMs: 0,
    };
  }

  private checkCacheValid(
    cached: CachedFileInfo | undefined,
    change: FileChange
  ): boolean {
    if (!cached) return false;
    if (change.changeType === 'deleted') return false;

    // Check if hash changed
    if (change.newHash && cached.hash !== change.newHash) {
      return false;
    }

    // Check if affected lines overlap with previous processing
    // If timestamp is newer, cache is invalid
    if (change.timestamp > cached.lastProcessed) {
      return false;
    }

    return true;
  }

  private async processChangeInternal(
    change: FileChange
  ): Promise<{ patterns: string[]; dependencies: string[] }> {
    // Simulate pattern extraction based on change type and size
    const patterns: string[] = [];
    const dependencies: string[] = [];

    // Extract patterns from affected lines (simplified simulation)
    const lineCount = change.affectedLines.length;

    // Pattern detection heuristics
    if (lineCount > 0) {
      // Detect common patterns based on file path and change characteristics
      if (change.filePath.includes('repository')) {
        patterns.push('repository-pattern');
      }
      if (change.filePath.includes('service')) {
        patterns.push('service-pattern');
      }
      if (change.filePath.includes('factory')) {
        patterns.push('factory-pattern');
      }

      // Large changes might indicate structural patterns
      if (lineCount > 50) {
        patterns.push('large-module-pattern');
      }
    }

    // Track file for dependencies
    this.trackDependency(change.filePath);

    return { patterns, dependencies };
  }

  private updateCache(
    change: FileChange,
    result: { patterns: string[]; dependencies: string[] }
  ): void {
    // Evict if at capacity
    if (this.cache.size >= this.config.maxCacheSize) {
      // LRU eviction - remove oldest entry
      const oldestKey = this.findOldestCacheEntry();
      if (oldestKey) {
        this.cache.delete(oldestKey);
      }
    }

    // Handle deletion
    if (change.changeType === 'deleted') {
      this.cache.delete(change.filePath);
      this.dependencies.delete(change.filePath);
      return;
    }

    // Add/update cache entry
    this.cache.set(change.filePath, {
      filePath: change.filePath,
      hash: change.newHash ?? this.generateHash(change),
      patterns: result.patterns,
      dependencies: result.dependencies,
      lastProcessed: Date.now(),
    });
  }

  private findOldestCacheEntry(): string | undefined {
    let oldest: { key: string; time: number } | undefined;

    for (const [key, value] of this.cache.entries()) {
      if (!oldest || value.lastProcessed < oldest.time) {
        oldest = { key, time: value.lastProcessed };
      }
    }

    return oldest?.key;
  }

  private generateHash(change: FileChange): string {
    // Simple hash based on file path and timestamp
    return `${change.filePath}-${change.timestamp}-${change.affectedLines.length}`;
  }

  private trackDependency(filePath: string): void {
    if (!this.dependencies.has(filePath)) {
      this.dependencies.set(filePath, new Set());
    }
  }

  private getReverseDependencies(filePath: string): string[] {
    const dependents: string[] = [];

    for (const [file, deps] of this.dependencies.entries()) {
      if (deps.has(filePath)) {
        dependents.push(file);
      }
    }

    return dependents;
  }

  private updateProcessingStats(processingTimeMs: number): void {
    const prevTotal = this.statistics.totalChangesProcessed;
    const prevAvg = this.statistics.averageProcessingTimeMs;

    this.statistics.totalChangesProcessed++;
    this.statistics.totalProcessingTimeMs += processingTimeMs;
    this.statistics.averageProcessingTimeMs =
      (prevAvg * prevTotal + processingTimeMs) /
      this.statistics.totalChangesProcessed;
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create an IncrementalUpdater instance
 * @param config - Optional configuration
 * @returns IncrementalUpdater instance
 */
export function createIncrementalUpdater(
  config: UpdaterConfig = {}
): IncrementalUpdater {
  return new DefaultIncrementalUpdater(config);
}

export { DefaultIncrementalUpdater };
