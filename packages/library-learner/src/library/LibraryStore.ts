/**
 * LibraryStore - Pattern library storage
 *
 * REQ-LL-002: ライブラリ成長
 * DES-PHASE2-001: Library Manager / LibraryStore
 *
 * @stub This is a stub implementation. Full implementation in M3.
 */

import type {
  LearnedPattern,
  PatternId,
  PatternQuery,
} from '../types.js';

/**
 * LibraryStore interface
 */
export interface LibraryStore {
  /** Add a pattern to the library */
  add(pattern: LearnedPattern): Promise<void>;

  /** Get a pattern by ID */
  get(id: PatternId): Promise<LearnedPattern | null>;

  /** Search patterns by query */
  search(query: PatternQuery): Promise<LearnedPattern[]>;

  /** Get all patterns */
  getAll(): Promise<LearnedPattern[]>;

  /** Update a pattern */
  update(id: PatternId, updates: Partial<LearnedPattern>): Promise<void>;

  /** Delete a pattern */
  delete(id: PatternId): Promise<void>;

  /** Get pattern count */
  count(): Promise<number>;
}

/**
 * In-memory LibraryStore implementation (stub)
 */
class InMemoryLibraryStore implements LibraryStore {
  private patterns = new Map<PatternId, LearnedPattern>();

  async add(pattern: LearnedPattern): Promise<void> {
    this.patterns.set(pattern.id, pattern);
  }

  async get(id: PatternId): Promise<LearnedPattern | null> {
    return this.patterns.get(id) ?? null;
  }

  async search(query: PatternQuery): Promise<LearnedPattern[]> {
    let results = Array.from(this.patterns.values());

    if (query.level !== undefined) {
      results = results.filter((p) => p.level === query.level);
    }

    if (query.tags && query.tags.length > 0) {
      results = results.filter((p) =>
        query.tags!.some((t) => p.tags.includes(t))
      );
    }

    if (query.minConfidence !== undefined) {
      results = results.filter((p) => p.confidence >= query.minConfidence!);
    }

    if (query.minUsageCount !== undefined) {
      results = results.filter((p) => p.usageCount >= query.minUsageCount!);
    }

    if (query.limit !== undefined) {
      results = results.slice(0, query.limit);
    }

    return results;
  }

  async getAll(): Promise<LearnedPattern[]> {
    return Array.from(this.patterns.values());
  }

  async update(id: PatternId, updates: Partial<LearnedPattern>): Promise<void> {
    const pattern = this.patterns.get(id);
    if (pattern) {
      this.patterns.set(id, { ...pattern, ...updates });
    }
  }

  async delete(id: PatternId): Promise<void> {
    this.patterns.delete(id);
  }

  async count(): Promise<number> {
    return this.patterns.size;
  }
}

/**
 * Factory function to create a LibraryStore
 */
export function createLibraryStore(): LibraryStore {
  return new InMemoryLibraryStore();
}
