/**
 * @fileoverview Wake-Sleep Learning Cycle Manager for YATA Local
 * @module @nahisaho/yata-local/wake-sleep
 * @version 0.1.0
 * @license MIT
 * 
 * Trace: REQ-WSL-001, REQ-WSL-002, REQ-WSL-003, REQ-WSL-005
 */

import type { YataDatabase } from '../database.js';
import { LocalWakePhase, createLocalWakePhase } from './wake-phase.js';
import { LocalSleepPhase, createLocalSleepPhase } from './sleep-phase.js';
import { LocalPatternCompressor, createLocalPatternCompressor } from './pattern-compressor.js';
import type {
  WakeSleepConfig,
  LocalLearningCycleResult,
  LocalConsolidatedPattern,
  WakeObserveResult,
  SleepClusterResult,
} from './types.js';

/**
 * Wake-Sleep Learning Cycle Manager
 * 
 * Orchestrates the complete learning cycle:
 * 1. Wake Phase: Observe code and extract patterns
 * 2. Sleep Phase: Cluster and consolidate patterns
 * 3. Storage: Persist patterns to local database
 */
export class LocalWakeSleepCycle {
  private readonly wakePhase: LocalWakePhase;
  private readonly sleepPhase: LocalSleepPhase;
  private readonly compressor: LocalPatternCompressor;
  private readonly db: YataDatabase;
  private readonly config: WakeSleepConfig;
  private autoRunTimer: ReturnType<typeof setInterval> | null = null;

  constructor(db: YataDatabase, config?: Partial<WakeSleepConfig>) {
    this.db = db;
    this.config = {
      autoRunInterval: config?.autoRunInterval ?? 0,
      wakeOptions: {
        extensions: config?.wakeOptions?.extensions ?? ['.ts', '.tsx', '.js', '.jsx'],
        excludeDirs: config?.wakeOptions?.excludeDirs ?? ['node_modules', 'dist', 'build', '.git'],
        minConfidence: config?.wakeOptions?.minConfidence ?? 0.3,
        maxCandidates: config?.wakeOptions?.maxCandidates ?? 1000,
        includePrivate: config?.wakeOptions?.includePrivate ?? false,
      },
      sleepOptions: {
        similarityThreshold: config?.sleepOptions?.similarityThreshold ?? 0.8,
        minClusterSize: config?.sleepOptions?.minClusterSize ?? 2,
        maxClusters: config?.sleepOptions?.maxClusters ?? 100,
      },
      compressOptions: {
        level: config?.compressOptions?.level ?? 5,
        preserveNames: config?.compressOptions?.preserveNames ?? false,
        includeTypes: config?.compressOptions?.includeTypes ?? true,
      },
      similarityMethod: config?.similarityMethod ?? 'jaccard',
      decayRate: config?.decayRate ?? 0.01,
      minConfidenceThreshold: config?.minConfidenceThreshold ?? 0.1,
    };

    this.wakePhase = createLocalWakePhase(this.config.wakeOptions);
    this.sleepPhase = createLocalSleepPhase(
      this.config.sleepOptions,
      this.config.similarityMethod
    );
    this.compressor = createLocalPatternCompressor(this.config.compressOptions);
  }

  /**
   * Run a complete wake-sleep cycle on a directory
   */
  async runCycle(directoryPath: string): Promise<LocalLearningCycleResult> {
    const startedAt = new Date();

    // Wake Phase: Extract patterns
    const wakeResult = await this.wakePhase.observeDirectory(directoryPath);

    // Sleep Phase: Cluster patterns
    const sleepResult = await this.sleepPhase.cluster(wakeResult.candidates);

    // Compress and store patterns
    const { newPatterns, updatedPatterns } = await this.storePatterns(
      sleepResult
    );

    // Decay unused patterns
    const decayedPatterns = await this.decayUnusedPatterns();

    const completedAt = new Date();
    const durationMs = completedAt.getTime() - startedAt.getTime();

    // Log cycle completion
    const cycle = this.db.logLearningCycle({
      wakeExtracted: wakeResult.stats.candidatesFound,
      wakeObservedFiles: wakeResult.stats.filesScanned,
      sleepClustered: sleepResult.stats.clustersFormed,
      sleepDecayed: decayedPatterns,
      durationMs,
      metadata: {
        wakeStats: wakeResult.stats,
        sleepStats: sleepResult.stats,
        newPatterns,
        updatedPatterns,
        decayedPatterns,
      },
    });

    return {
      cycleId: cycle.id,
      phase: 'complete',
      wakeResult,
      sleepResult,
      newPatterns,
      updatedPatterns,
      decayedPatterns,
      startedAt,
      completedAt,
      durationMs,
    };
  }

  /**
   * Run only the wake phase
   */
  async runWakePhase(directoryPath: string): Promise<WakeObserveResult> {
    return this.wakePhase.observeDirectory(directoryPath);
  }

  /**
   * Run only the sleep phase on existing candidates
   */
  async runSleepPhase(
    candidates: WakeObserveResult['candidates']
  ): Promise<SleepClusterResult> {
    return this.sleepPhase.cluster(candidates);
  }

  /**
   * Store consolidated patterns in the database
   */
  private async storePatterns(
    sleepResult: SleepClusterResult
  ): Promise<{ newPatterns: number; updatedPatterns: number }> {
    let newPatterns = 0;
    let updatedPatterns = 0;

    for (const cluster of sleepResult.clusters) {
      const consolidated = this.compressor.compress(cluster);

      // Check if similar pattern already exists
      const existing = this.findSimilarPattern(consolidated);

      if (existing) {
        // Update existing pattern
        const now = new Date();
        this.db.updatePattern({
          ...existing,
          confidence: Math.max(existing.confidence, consolidated.confidence),
          usageCount: existing.usageCount + 1,
          lastUsedAt: now,
          occurrences: existing.occurrences + consolidated.sourceCount,
          updatedAt: now,
        });
        updatedPatterns++;
      } else {
        // Insert new pattern
        const now = new Date();
        this.db.insertPattern({
          id: consolidated.id,
          name: consolidated.name,
          category: this.mapTypeToCategory(consolidated.type),
          content: consolidated.template,
          ast: undefined,
          confidence: consolidated.confidence,
          occurrences: consolidated.sourceCount,
          usageCount: consolidated.usageCount,
          source: consolidated.sources[0],
          metadata: {
            type: consolidated.type,
            compressed: consolidated.compressed,
            sources: consolidated.sources,
          },
          createdAt: now,
          updatedAt: now,
        });
        newPatterns++;
      }
    }

    return { newPatterns, updatedPatterns };
  }

  /**
   * Map local pattern type to PatternCategory
   */
  private mapTypeToCategory(type: LocalConsolidatedPattern['type']): import('../types.js').PatternCategory {
    const mapping: Record<string, import('../types.js').PatternCategory> = {
      function_signature: 'code',
      class_structure: 'design',
      interface_definition: 'design',
      type_definition: 'design',
      import_pattern: 'code',
      export_pattern: 'code',
      error_handling: 'code',
      async_pattern: 'code',
      factory_pattern: 'design',
      repository_pattern: 'design',
      service_pattern: 'design',
      value_object: 'design',
      entity: 'design',
      aggregate: 'architecture',
      event_handler: 'design',
      middleware: 'code',
      decorator: 'code',
      hook: 'code',
      test_pattern: 'test',
      other: 'code',
    };
    return mapping[type] ?? 'code';
  }

  /**
   * Find a similar existing pattern
   */
  private findSimilarPattern(
    pattern: LocalConsolidatedPattern
  ): import('../types.js').LearnedPattern | null {
    // Get patterns of the same category
    const category = this.mapTypeToCategory(pattern.type);
    const existingPatterns = this.db.queryPatterns({ category });

    for (const existing of existingPatterns) {
      const existingCompressed = (existing.metadata as Record<string, unknown>)?.compressed as string | undefined;
      if (!existingCompressed) continue;

      const similarity = this.sleepPhase.calculateSimilarity(
        pattern.compressed,
        existingCompressed
      );

      const threshold = this.config.sleepOptions.similarityThreshold ?? 0.8;
      if (similarity >= threshold) {
        return existing;
      }
    }

    return null;
  }

  /**
   * Decay confidence of unused patterns
   */
  private async decayUnusedPatterns(): Promise<number> {
    const allPatterns = this.db.queryPatterns();
    let decayedCount = 0;

    for (const pattern of allPatterns) {
      const metadata = pattern.metadata as Record<string, unknown>;
      const consolidated: LocalConsolidatedPattern = {
        id: pattern.id,
        name: pattern.name,
        type: (metadata?.type as LocalConsolidatedPattern['type']) ?? 'other',
        template: pattern.content,
        compressed: (metadata?.compressed as string) ?? '',
        confidence: pattern.confidence,
        sourceCount: pattern.occurrences,
        usageCount: pattern.usageCount,
        createdAt: pattern.createdAt,
        lastUsedAt: pattern.lastUsedAt ?? null,
        sources: (metadata?.sources as string[]) ?? [],
      };

      const decayed = this.sleepPhase.decay(
        consolidated,
        this.config.decayRate
      );

      if (decayed.confidence < pattern.confidence) {
        if (decayed.confidence < this.config.minConfidenceThreshold) {
          // Remove pattern if below threshold
          this.db.deletePattern(pattern.id);
        } else {
          // Update with decayed confidence
          this.db.decayPatternConfidence(pattern.id, this.config.decayRate);
        }
        decayedCount++;
      }
    }

    return decayedCount;
  }

  /**
   * Start automatic learning cycles
   */
  startAutoRun(directoryPath: string): void {
    if (this.config.autoRunInterval <= 0) {
      throw new Error('Auto-run interval must be greater than 0');
    }

    if (this.autoRunTimer) {
      this.stopAutoRun();
    }

    this.autoRunTimer = setInterval(async () => {
      try {
        await this.runCycle(directoryPath);
      } catch (error) {
        // Log error but don't stop auto-run
        console.error('Auto-run cycle failed:', error);
      }
    }, this.config.autoRunInterval);
  }

  /**
   * Stop automatic learning cycles
   */
  stopAutoRun(): void {
    if (this.autoRunTimer) {
      clearInterval(this.autoRunTimer);
      this.autoRunTimer = null;
    }
  }

  /**
   * Get recent learning cycle history
   */
  getRecentCycles(limit: number = 10): import('../types.js').LearningCycle[] {
    return this.db.getRecentLearningCycles(limit);
  }

  /**
   * Get configuration
   */
  getConfig(): WakeSleepConfig {
    return { ...this.config };
  }
}

/**
 * Factory function to create a LocalWakeSleepCycle instance
 */
export function createLocalWakeSleepCycle(
  db: YataDatabase,
  config?: Partial<WakeSleepConfig>
): LocalWakeSleepCycle {
  return new LocalWakeSleepCycle(db, config);
}
