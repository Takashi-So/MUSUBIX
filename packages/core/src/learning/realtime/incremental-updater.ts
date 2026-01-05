/**
 * IncrementalUpdater - Delta Pattern Updates
 *
 * Performs incremental updates to pattern knowledge without full reprocessing.
 *
 * @see REQ-LEARN-012 - Incremental Updates
 * @see DES-LEARN-010 - IncrementalUpdater Component
 * @module @musubix/core/learning/realtime
 */

import { EventEmitter } from 'events';
import {
  type RealtimeDetectedPattern,
  type IncrementalUpdate,
  type PatternEvent,
} from './types.js';
import { EventStream, createPatternEvent } from './event-stream.js';

/**
 * Pattern store interface
 */
export interface PatternStore {
  /** Get pattern by ID */
  get(id: string): RealtimeDetectedPattern | undefined;
  /** Check if pattern exists */
  has(id: string): boolean;
  /** Get all patterns */
  getAll(): RealtimeDetectedPattern[];
  /** Get patterns by category */
  getByCategory(category: string): RealtimeDetectedPattern[];
  /** Get patterns by source file */
  getBySource(sourcePath: string): RealtimeDetectedPattern[];
  /** Pattern count */
  size(): number;
}

/**
 * Updater events
 */
export interface UpdaterEvents {
  updated: (update: IncrementalUpdate) => void;
  patternAdded: (pattern: RealtimeDetectedPattern) => void;
  patternUpdated: (pattern: RealtimeDetectedPattern) => void;
  patternRemoved: (patternId: string) => void;
}

/**
 * Update statistics
 */
export interface UpdateStats {
  /** Total updates applied */
  totalUpdates: number;
  /** Patterns added */
  added: number;
  /** Patterns updated */
  updated: number;
  /** Patterns removed */
  removed: number;
  /** Similar patterns merged */
  merged: number;
  /** Last update timestamp */
  lastUpdateAt: number;
}

/**
 * IncrementalUpdater - Applies delta updates to pattern store
 *
 * @example
 * ```typescript
 * const updater = new IncrementalUpdater(eventStream);
 * updater.on('patternAdded', (pattern) => {
 *   console.log(`New pattern: ${pattern.name}`);
 * });
 * updater.applyUpdate(update);
 * ```
 */
export class IncrementalUpdater extends EventEmitter implements PatternStore {
  private readonly patterns: Map<string, RealtimeDetectedPattern> = new Map();
  private readonly sourceIndex: Map<string, Set<string>> = new Map();
  private readonly categoryIndex: Map<string, Set<string>> = new Map();
  private readonly eventStream: EventStream | null;
  private readonly stats: UpdateStats = {
    totalUpdates: 0,
    added: 0,
    updated: 0,
    removed: 0,
    merged: 0,
    lastUpdateAt: 0,
  };

  constructor(eventStream?: EventStream) {
    super();
    this.eventStream = eventStream ?? null;
  }

  /**
   * Apply an incremental update
   * @traceability REQ-LEARN-012 - Delta updates only
   */
  applyUpdate(update: IncrementalUpdate): void {
    this.stats.totalUpdates++;
    this.stats.lastUpdateAt = Date.now();

    switch (update.type) {
      case 'add':
        if (update.pattern) {
          this.addPattern(update.pattern);
        }
        break;
      case 'update':
        if (update.pattern) {
          this.updatePattern(update.pattern);
        }
        break;
      case 'remove':
        this.removePattern(update.patternId);
        break;
    }

    this.emit('updated', update);
  }

  /**
   * Apply multiple updates
   * @traceability REQ-LEARN-012
   */
  applyUpdates(updates: IncrementalUpdate[]): void {
    for (const update of updates) {
      this.applyUpdate(update);
    }
  }

  /**
   * Add new pattern (or update if exists)
   * @traceability REQ-LEARN-012
   */
  addPattern(pattern: RealtimeDetectedPattern): void {
    // Check for similar existing pattern
    const existing = this.findSimilarPattern(pattern);

    if (existing) {
      // Merge with existing pattern
      const merged = this.mergePatterns(existing, pattern);
      this.patterns.set(merged.id, merged);
      this.stats.merged++;
      this.emitEvent('pattern:updated', { pattern: merged });
      this.emit('patternUpdated', merged);
    } else {
      // Add new pattern
      this.patterns.set(pattern.id, pattern);
      this.indexPattern(pattern);
      this.stats.added++;
      this.emitEvent('pattern:detected', { pattern });
      this.emit('patternAdded', pattern);
    }
  }

  /**
   * Update existing pattern
   */
  updatePattern(pattern: RealtimeDetectedPattern): void {
    const existing = this.patterns.get(pattern.id);

    if (existing) {
      // Remove from old indexes
      this.unindexPattern(existing);
    }

    // Update pattern
    this.patterns.set(pattern.id, pattern);
    this.indexPattern(pattern);
    this.stats.updated++;

    this.emitEvent('pattern:updated', { pattern });
    this.emit('patternUpdated', pattern);
  }

  /**
   * Remove pattern
   */
  removePattern(patternId: string): void {
    const pattern = this.patterns.get(patternId);

    if (pattern) {
      this.unindexPattern(pattern);
      this.patterns.delete(patternId);
      this.stats.removed++;

      this.emitEvent('pattern:removed', { patternId });
      this.emit('patternRemoved', patternId);
    }
  }

  /**
   * Remove all patterns from a source file
   * @traceability REQ-LEARN-012 - Efficient removal
   */
  removeBySource(sourcePath: string): void {
    const patternIds = this.sourceIndex.get(sourcePath);

    if (patternIds) {
      for (const id of patternIds) {
        this.removePattern(id);
      }
    }
  }

  // PatternStore implementation

  get(id: string): RealtimeDetectedPattern | undefined {
    return this.patterns.get(id);
  }

  has(id: string): boolean {
    return this.patterns.has(id);
  }

  getAll(): RealtimeDetectedPattern[] {
    return Array.from(this.patterns.values());
  }

  getByCategory(category: string): RealtimeDetectedPattern[] {
    const ids = this.categoryIndex.get(category);
    if (!ids) return [];

    return Array.from(ids)
      .map((id) => this.patterns.get(id))
      .filter((p): p is RealtimeDetectedPattern => p !== undefined);
  }

  getBySource(sourcePath: string): RealtimeDetectedPattern[] {
    const ids = this.sourceIndex.get(sourcePath);
    if (!ids) return [];

    return Array.from(ids)
      .map((id) => this.patterns.get(id))
      .filter((p): p is RealtimeDetectedPattern => p !== undefined);
  }

  size(): number {
    return this.patterns.size;
  }

  /**
   * Get update statistics
   */
  getStats(): UpdateStats {
    return { ...this.stats };
  }

  /**
   * Clear all patterns
   */
  clear(): void {
    this.patterns.clear();
    this.sourceIndex.clear();
    this.categoryIndex.clear();
  }

  /**
   * Find similar existing pattern
   */
  private findSimilarPattern(pattern: RealtimeDetectedPattern): RealtimeDetectedPattern | undefined {
    // First check same source file
    const sameSource = this.getBySource(pattern.sourcePath);

    for (const existing of sameSource) {
      if (this.isSimilar(existing, pattern)) {
        return existing;
      }
    }

    return undefined;
  }

  /**
   * Check if two patterns are similar
   */
  private isSimilar(a: RealtimeDetectedPattern, b: RealtimeDetectedPattern): boolean {
    // Same category
    if (a.category !== b.category) return false;

    // Overlapping line ranges
    const overlap =
      (a.lineRange.start <= b.lineRange.end && a.lineRange.end >= b.lineRange.start) ||
      (b.lineRange.start <= a.lineRange.end && b.lineRange.end >= a.lineRange.start);

    if (!overlap) return false;

    // Similar name
    const nameA = a.name.toLowerCase();
    const nameB = b.name.toLowerCase();

    return (
      nameA === nameB ||
      nameA.includes(nameB) ||
      nameB.includes(nameA)
    );
  }

  /**
   * Merge two similar patterns
   */
  private mergePatterns(
    existing: RealtimeDetectedPattern,
    newPattern: RealtimeDetectedPattern
  ): RealtimeDetectedPattern {
    return {
      ...existing,
      confidence: Math.max(existing.confidence, newPattern.confidence),
      lineRange: {
        start: Math.min(existing.lineRange.start, newPattern.lineRange.start),
        end: Math.max(existing.lineRange.end, newPattern.lineRange.end),
      },
      template: newPattern.template,
      detectedAt: newPattern.detectedAt,
    };
  }

  /**
   * Index pattern for fast lookup
   */
  private indexPattern(pattern: RealtimeDetectedPattern): void {
    // Source index
    if (!this.sourceIndex.has(pattern.sourcePath)) {
      this.sourceIndex.set(pattern.sourcePath, new Set());
    }
    this.sourceIndex.get(pattern.sourcePath)!.add(pattern.id);

    // Category index
    if (!this.categoryIndex.has(pattern.category)) {
      this.categoryIndex.set(pattern.category, new Set());
    }
    this.categoryIndex.get(pattern.category)!.add(pattern.id);
  }

  /**
   * Remove pattern from indexes
   */
  private unindexPattern(pattern: RealtimeDetectedPattern): void {
    // Source index
    this.sourceIndex.get(pattern.sourcePath)?.delete(pattern.id);

    // Category index
    this.categoryIndex.get(pattern.category)?.delete(pattern.id);
  }

  /**
   * Emit event to event stream
   */
  private emitEvent(type: PatternEvent['type'], payload: Record<string, unknown>): void {
    if (this.eventStream) {
      this.eventStream.publish(createPatternEvent(type, payload));
    }
  }
}

/**
 * Create an incremental update
 */
export function createUpdate(
  type: IncrementalUpdate['type'],
  patternId: string,
  pattern?: RealtimeDetectedPattern
): IncrementalUpdate {
  return {
    type,
    patternId,
    pattern,
    timestamp: Date.now(),
  };
}
