/**
 * Pruner - Prune unused patterns
 *
 * REQ-LL-002: ライブラリ成長
 * DES-PHASE2-001: Library Manager / Pruner
 *
 * @stub This is a stub implementation. Full implementation in M3.
 */

import type { PruneReport } from '../types.js';
import type { LibraryStore } from './LibraryStore.js';

/**
 * Pruner interface
 */
export interface Pruner {
  /** Apply decay to all patterns */
  applyDecay(store: LibraryStore, decayRate: number): Promise<void>;

  /** Prune patterns below threshold */
  prune(store: LibraryStore, threshold: number): Promise<PruneReport>;
}

/**
 * Default Pruner implementation (stub)
 */
class PrunerImpl implements Pruner {
  async applyDecay(store: LibraryStore, decayRate: number): Promise<void> {
    const patterns = await store.getAll();

    for (const pattern of patterns) {
      await store.update(pattern.id, {
        confidence: pattern.confidence * decayRate,
      });
    }
  }

  async prune(store: LibraryStore, threshold: number): Promise<PruneReport> {
    const startTime = Date.now();
    const patterns = await store.getAll();
    const toPrune = patterns.filter((p) => p.confidence < threshold);

    for (const pattern of toPrune) {
      await store.delete(pattern.id);
    }

    return {
      patternsPruned: toPrune.length,
      prunedIds: toPrune.map((p) => p.id),
      duration: Date.now() - startTime,
    };
  }
}

/**
 * Factory function to create a Pruner
 */
export function createPruner(): Pruner {
  return new PrunerImpl();
}
