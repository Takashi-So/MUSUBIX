/**
 * IncrementalUpdater Test Suite
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-107
 * @see DES-LL-107
 * @see REQ-PERF-002 (5秒/500LOC目標)
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  IncrementalUpdater,
  createIncrementalUpdater,
  type UpdaterConfig,
  type FileChange,
  type ChangeType,
  type UpdateResult,
  type UpdateStatistics,
} from '../../src/updater/IncrementalUpdater.js';

// =============================================================================
// Test Fixtures
// =============================================================================

function createMockConfig(): UpdaterConfig {
  return {
    maxCacheSize: 1000,
    enableParallelProcessing: true,
    batchSize: 50,
    debounceMs: 100,
  };
}

function createMockFileChange(overrides: Partial<FileChange> = {}): FileChange {
  return {
    filePath: '/test/file.ts',
    changeType: 'modified' as ChangeType,
    affectedLines: [1, 2, 3, 4, 5],
    timestamp: Date.now(),
    ...overrides,
  };
}

function generateLargeFile(lines: number): string {
  const code: string[] = [];
  for (let i = 0; i < lines; i++) {
    code.push(`const x${i} = ${i}; // Line ${i + 1}`);
  }
  return code.join('\n');
}

// =============================================================================
// Tests
// =============================================================================

describe('IncrementalUpdater', () => {
  let updater: IncrementalUpdater;

  beforeEach(() => {
    updater = createIncrementalUpdater();
  });

  describe('Factory Function', () => {
    it('should create updater with default config', () => {
      const u = createIncrementalUpdater();
      expect(u).toBeDefined();
      expect(u.processChange).toBeDefined();
    });

    it('should create updater with custom config', () => {
      const config = createMockConfig();
      const u = createIncrementalUpdater(config);
      expect(u).toBeDefined();
    });
  });

  describe('processChange', () => {
    it('should handle file addition', async () => {
      const change = createMockFileChange({ changeType: 'added' });
      const result = await updater.processChange(change);
      
      expect(result).toBeDefined();
      expect(result.success).toBe(true);
      expect(result.changeType).toBe('added');
    });

    it('should handle file modification', async () => {
      const change = createMockFileChange({ changeType: 'modified' });
      const result = await updater.processChange(change);
      
      expect(result).toBeDefined();
      expect(result.success).toBe(true);
    });

    it('should handle file deletion', async () => {
      const change = createMockFileChange({ changeType: 'deleted' });
      const result = await updater.processChange(change);
      
      expect(result).toBeDefined();
      expect(result.success).toBe(true);
    });

    it('should track processing time', async () => {
      const change = createMockFileChange();
      const result = await updater.processChange(change);
      
      expect(result.processingTimeMs).toBeGreaterThanOrEqual(0);
    });

    it('should identify affected patterns', async () => {
      const change = createMockFileChange();
      const result = await updater.processChange(change);
      
      expect(result.affectedPatterns).toBeDefined();
      expect(Array.isArray(result.affectedPatterns)).toBe(true);
    });
  });

  describe('processBatch', () => {
    it('should process multiple changes in batch', async () => {
      const changes = [
        createMockFileChange({ filePath: '/test/file1.ts' }),
        createMockFileChange({ filePath: '/test/file2.ts' }),
        createMockFileChange({ filePath: '/test/file3.ts' }),
      ];
      
      const results = await updater.processBatch(changes);
      
      expect(results).toBeDefined();
      expect(results.length).toBe(3);
      expect(results.every(r => r.success)).toBe(true);
    });

    it('should handle empty batch', async () => {
      const results = await updater.processBatch([]);
      expect(results).toEqual([]);
    });

    it('should process in parallel when enabled', async () => {
      const config: UpdaterConfig = {
        ...createMockConfig(),
        enableParallelProcessing: true,
      };
      const u = createIncrementalUpdater(config);
      
      const changes = Array.from({ length: 10 }, (_, i) =>
        createMockFileChange({ filePath: `/test/file${i}.ts` })
      );
      
      const start = Date.now();
      const results = await u.processBatch(changes);
      const duration = Date.now() - start;
      
      expect(results.length).toBe(10);
      // Parallel processing should be reasonably fast
      expect(duration).toBeLessThan(1000);
    });
  });

  describe('Performance Target: 5秒/500LOC', () => {
    it('should process 500 LOC changes within 5 seconds', async () => {
      // Create a change representing 500 LOC modification
      const change = createMockFileChange({
        affectedLines: Array.from({ length: 500 }, (_, i) => i + 1),
      });
      
      const start = Date.now();
      const result = await updater.processChange(change);
      const duration = Date.now() - start;
      
      expect(result.success).toBe(true);
      expect(duration).toBeLessThan(5000); // 5 second target
    });

    it('should maintain performance with large batch of small changes', async () => {
      // 50 files x 10 LOC each = 500 LOC total
      const changes = Array.from({ length: 50 }, (_, i) =>
        createMockFileChange({
          filePath: `/test/file${i}.ts`,
          affectedLines: Array.from({ length: 10 }, (_, j) => j + 1),
        })
      );
      
      const start = Date.now();
      const results = await updater.processBatch(changes);
      const duration = Date.now() - start;
      
      expect(results.every(r => r.success)).toBe(true);
      expect(duration).toBeLessThan(5000); // 5 second target
    });
  });

  describe('Caching', () => {
    it('should cache processed file information', async () => {
      const change = createMockFileChange();
      
      // First process
      await updater.processChange(change);
      
      // Second process should use cache
      const start = Date.now();
      const result = await updater.processChange(change);
      const duration = Date.now() - start;
      
      expect(result.success).toBe(true);
      expect(result.cacheHit).toBe(true);
    });

    it('should invalidate cache on file modification', async () => {
      const filePath = '/test/cached-file.ts';
      
      // First process
      await updater.processChange(createMockFileChange({ 
        filePath, 
        changeType: 'added' 
      }));
      
      // Modify same file with different lines
      const result = await updater.processChange(createMockFileChange({
        filePath,
        changeType: 'modified',
        affectedLines: [10, 11, 12],
        timestamp: Date.now() + 1000,
      }));
      
      expect(result.cacheHit).toBe(false);
    });

    it('should respect cache size limits', async () => {
      const config: UpdaterConfig = {
        ...createMockConfig(),
        maxCacheSize: 5,
      };
      const u = createIncrementalUpdater(config);
      
      // Process more files than cache can hold
      for (let i = 0; i < 10; i++) {
        await u.processChange(createMockFileChange({
          filePath: `/test/file${i}.ts`,
        }));
      }
      
      const stats = u.getStatistics();
      expect(stats.cacheSize).toBeLessThanOrEqual(5);
    });
  });

  describe('Dependency Tracking', () => {
    it('should track file dependencies', async () => {
      // Process a file that imports another
      await updater.processChange(createMockFileChange({
        filePath: '/test/module.ts',
      }));
      
      const deps = updater.getDependencies('/test/module.ts');
      expect(deps).toBeDefined();
    });

    it('should identify dependent files on change', async () => {
      // Setup dependency relationship
      await updater.processChange(createMockFileChange({
        filePath: '/test/base.ts',
      }));
      
      const result = await updater.processChange(createMockFileChange({
        filePath: '/test/base.ts',
        changeType: 'modified',
      }));
      
      expect(result.dependentFiles).toBeDefined();
    });
  });

  describe('Statistics', () => {
    it('should return initial statistics', () => {
      const stats = updater.getStatistics();
      
      expect(stats).toBeDefined();
      expect(stats.totalChangesProcessed).toBe(0);
      expect(stats.cacheHits).toBe(0);
      expect(stats.cacheMisses).toBe(0);
    });

    it('should update statistics after processing', async () => {
      await updater.processChange(createMockFileChange());
      
      const stats = updater.getStatistics();
      expect(stats.totalChangesProcessed).toBe(1);
    });

    it('should track average processing time', async () => {
      await updater.processChange(createMockFileChange());
      await updater.processChange(createMockFileChange({
        filePath: '/test/other.ts',
      }));
      
      const stats = updater.getStatistics();
      expect(stats.averageProcessingTimeMs).toBeGreaterThanOrEqual(0);
    });
  });

  describe('reset', () => {
    it('should reset all state', async () => {
      await updater.processChange(createMockFileChange());
      
      updater.reset();
      
      const stats = updater.getStatistics();
      expect(stats.totalChangesProcessed).toBe(0);
      expect(stats.cacheSize).toBe(0);
    });
  });

  describe('clearCache', () => {
    it('should clear only cache, keeping statistics', async () => {
      await updater.processChange(createMockFileChange());
      
      const statsBefore = updater.getStatistics();
      updater.clearCache();
      const statsAfter = updater.getStatistics();
      
      expect(statsAfter.cacheSize).toBe(0);
      expect(statsAfter.totalChangesProcessed).toBe(statsBefore.totalChangesProcessed);
    });
  });

  describe('toJSON / fromJSON', () => {
    it('should serialize state', async () => {
      await updater.processChange(createMockFileChange());
      
      const json = updater.toJSON();
      expect(json).toBeDefined();
      expect(typeof json).toBe('string');
    });

    it('should restore state', async () => {
      await updater.processChange(createMockFileChange());
      const json = updater.toJSON();
      
      const newUpdater = createIncrementalUpdater();
      newUpdater.fromJSON(json);
      
      const origStats = updater.getStatistics();
      const newStats = newUpdater.getStatistics();
      
      expect(newStats.totalChangesProcessed).toBe(origStats.totalChangesProcessed);
    });
  });
});
