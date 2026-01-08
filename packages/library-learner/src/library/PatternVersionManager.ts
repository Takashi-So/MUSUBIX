/**
 * PatternVersionManager - Pattern Version History Management
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-105
 * @see DES-LL-105
 * @see REQ-LL-105 Pattern versioning with rollback capability
 */

import type { LearnedPattern } from '../types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * PatternVersionManager configuration
 */
export interface PatternVersionManagerConfig {
  /** Maximum versions to keep per pattern (default: 50) */
  maxVersionsPerPattern: number;
  /** Auto cleanup old versions when limit exceeded */
  autoCleanup: boolean;
}

/**
 * Version metadata
 */
export interface VersionMetadata {
  /** Reason for the change */
  reason?: string;
  /** Author of the change */
  author?: string;
  /** Additional metadata */
  [key: string]: unknown;
}

/**
 * Version history entry
 */
export interface VersionEntry {
  /** Version identifier */
  versionId: string;
  /** Version number (sequential) */
  versionNumber: number;
  /** Timestamp of version creation */
  timestamp: Date;
  /** Pattern snapshot */
  snapshot: LearnedPattern;
  /** Version metadata */
  metadata?: VersionMetadata;
}

/**
 * Version comparison result
 */
export interface VersionDiff {
  /** From version */
  fromVersion: string;
  /** To version */
  toVersion: string;
  /** List of changes */
  changes: VersionChange[];
}

/**
 * Individual change in a version diff
 */
export interface VersionChange {
  /** Field that changed */
  field: string;
  /** Old value */
  oldValue: unknown;
  /** New value */
  newValue: unknown;
}

/**
 * Version statistics
 */
export interface VersionStatistics {
  /** Total versions across all patterns */
  totalVersions: number;
  /** Total patterns with versions */
  totalPatterns: number;
  /** Average versions per pattern */
  averageVersionsPerPattern: number;
}

/**
 * PatternVersionManager interface
 */
export interface PatternVersionManager {
  /**
   * Record a new version of a pattern
   */
  recordVersion(pattern: LearnedPattern, metadata?: VersionMetadata): string;

  /**
   * Get version history for a pattern
   */
  getHistory(patternId: string): VersionEntry[];

  /**
   * Get specific version
   */
  getVersion(patternId: string, versionId: string): LearnedPattern | undefined;

  /**
   * Get latest version
   */
  getLatestVersion(patternId: string): LearnedPattern | undefined;

  /**
   * Rollback to specific version
   */
  rollback(patternId: string, versionId: string): Promise<LearnedPattern>;

  /**
   * Compare two versions
   */
  compareVersions(
    patternId: string,
    versionId1: string,
    versionId2: string
  ): VersionDiff;

  /**
   * Get statistics
   */
  getStatistics(): VersionStatistics;

  /**
   * Serialize to JSON
   */
  toJSON(): string;

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void;
}

// ============================================================================
// Default Implementation
// ============================================================================

/**
 * Default PatternVersionManager implementation
 */
export class DefaultPatternVersionManager implements PatternVersionManager {
  private config: PatternVersionManagerConfig;
  private versions: Map<string, VersionEntry[]>;
  private versionCounter: Map<string, number>;

  constructor(config?: Partial<PatternVersionManagerConfig>) {
    this.config = {
      maxVersionsPerPattern: config?.maxVersionsPerPattern ?? 50,
      autoCleanup: config?.autoCleanup ?? true,
    };

    this.versions = new Map();
    this.versionCounter = new Map();
  }

  /**
   * Record a new version of a pattern
   */
  recordVersion(pattern: LearnedPattern, metadata?: VersionMetadata): string {
    const patternId = pattern.id;

    // Get or initialize version list
    if (!this.versions.has(patternId)) {
      this.versions.set(patternId, []);
      this.versionCounter.set(patternId, 0);
    }

    // Increment version counter
    const versionNumber = (this.versionCounter.get(patternId) ?? 0) + 1;
    this.versionCounter.set(patternId, versionNumber);

    // Generate version ID
    const versionId = `v${versionNumber}-${Date.now()}`;

    // Create version entry
    const entry: VersionEntry = {
      versionId,
      versionNumber,
      timestamp: new Date(),
      snapshot: this.deepClone(pattern),
      metadata,
    };

    // Add to history
    const history = this.versions.get(patternId)!;
    history.push(entry);

    // Cleanup if needed
    if (this.config.autoCleanup && history.length > this.config.maxVersionsPerPattern) {
      this.cleanupOldVersions(patternId);
    }

    return versionId;
  }

  /**
   * Get version history for a pattern
   */
  getHistory(patternId: string): VersionEntry[] {
    return this.versions.get(patternId) ?? [];
  }

  /**
   * Get specific version
   */
  getVersion(patternId: string, versionId: string): LearnedPattern | undefined {
    const history = this.versions.get(patternId);
    if (!history) return undefined;

    const entry = history.find((e) => e.versionId === versionId);
    return entry ? this.deepClone(entry.snapshot) : undefined;
  }

  /**
   * Get latest version
   */
  getLatestVersion(patternId: string): LearnedPattern | undefined {
    const history = this.versions.get(patternId);
    if (!history || history.length === 0) return undefined;

    return this.deepClone(history[history.length - 1].snapshot);
  }

  /**
   * Rollback to specific version
   */
  async rollback(patternId: string, versionId: string): Promise<LearnedPattern> {
    const history = this.versions.get(patternId);
    if (!history) {
      throw new Error(`Pattern ${patternId} not found`);
    }

    const entry = history.find((e) => e.versionId === versionId);
    if (!entry) {
      throw new Error(`Version ${versionId} not found for pattern ${patternId}`);
    }

    // Create a new version with rolled back content
    const rolledBackPattern = this.deepClone(entry.snapshot);
    rolledBackPattern.lastUsedAt = new Date();

    // Record the rollback as a new version
    this.recordVersion(rolledBackPattern, {
      reason: `Rollback to version ${versionId}`,
      rollbackFrom: versionId,
    });

    return rolledBackPattern;
  }

  /**
   * Compare two versions
   */
  compareVersions(
    patternId: string,
    versionId1: string,
    versionId2: string
  ): VersionDiff {
    const v1 = this.getVersion(patternId, versionId1);
    const v2 = this.getVersion(patternId, versionId2);

    const changes: VersionChange[] = [];

    if (!v1 || !v2) {
      return { fromVersion: versionId1, toVersion: versionId2, changes };
    }

    // Compare fields
    const fieldsToCompare = ['name', 'usageCount', 'confidence', 'tags'];

    for (const field of fieldsToCompare) {
      const val1 = (v1 as unknown as Record<string, unknown>)[field];
      const val2 = (v2 as unknown as Record<string, unknown>)[field];

      if (JSON.stringify(val1) !== JSON.stringify(val2)) {
        changes.push({
          field,
          oldValue: val1,
          newValue: val2,
        });
      }
    }

    return {
      fromVersion: versionId1,
      toVersion: versionId2,
      changes,
    };
  }

  /**
   * Get statistics
   */
  getStatistics(): VersionStatistics {
    let totalVersions = 0;
    const totalPatterns = this.versions.size;

    for (const history of this.versions.values()) {
      totalVersions += history.length;
    }

    return {
      totalVersions,
      totalPatterns,
      averageVersionsPerPattern:
        totalPatterns > 0 ? totalVersions / totalPatterns : 0,
    };
  }

  /**
   * Cleanup old versions for a pattern
   */
  private cleanupOldVersions(patternId: string): void {
    const history = this.versions.get(patternId);
    if (!history) return;

    const maxToKeep = this.config.maxVersionsPerPattern;
    if (history.length > maxToKeep) {
      // Keep only the most recent versions
      const toRemove = history.length - maxToKeep;
      history.splice(0, toRemove);
    }
  }

  /**
   * Deep clone an object
   */
  private deepClone<T>(obj: T): T {
    return JSON.parse(JSON.stringify(obj));
  }

  /**
   * Serialize to JSON
   */
  toJSON(): string {
    const data: Record<string, VersionEntry[]> = {};

    for (const [patternId, history] of this.versions.entries()) {
      data[patternId] = history.map((entry) => ({
        ...entry,
        timestamp: entry.timestamp,
      }));
    }

    return JSON.stringify({
      config: this.config,
      patterns: data,
      counters: Object.fromEntries(this.versionCounter),
    });
  }

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.config) {
      this.config = { ...this.config, ...data.config };
    }

    if (data.patterns) {
      this.versions.clear();
      for (const [patternId, history] of Object.entries(data.patterns)) {
        const entries = (history as VersionEntry[]).map((entry) => ({
          ...entry,
          timestamp: new Date(entry.timestamp),
        }));
        this.versions.set(patternId, entries);
      }
    }

    if (data.counters) {
      this.versionCounter.clear();
      for (const [patternId, count] of Object.entries(data.counters)) {
        this.versionCounter.set(patternId, count as number);
      }
    }
  }
}

// ============================================================================
// Factory Function
// ============================================================================

/**
 * Create a PatternVersionManager instance
 * @param config - Optional configuration
 * @returns PatternVersionManager instance
 */
export function createPatternVersionManager(
  config?: Partial<PatternVersionManagerConfig>
): PatternVersionManager {
  return new DefaultPatternVersionManager(config);
}
