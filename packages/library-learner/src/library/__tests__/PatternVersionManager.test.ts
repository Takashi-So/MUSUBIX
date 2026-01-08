/**
 * PatternVersionManager Tests
 * @module @nahisaho/musubix-library-learner
 * @see TSK-LL-105
 * @see DES-LL-105
 * @see REQ-LL-105 Pattern version management with rollback
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createPatternVersionManager,
  type PatternVersionManager,
} from '../PatternVersionManager.js';
import type { LearnedPattern, ConcretePattern } from '../../types.js';

describe('PatternVersionManager', () => {
  let manager: PatternVersionManager;

  // Helper to create mock patterns
  const createPattern = (id: string, version: number): LearnedPattern => ({
    id,
    name: `Pattern-${id}-v${version}`,
    level: 1,
    content: {
      id,
      ast: { type: 'Expression', value: version },
      occurrenceCount: 5 + version,
      locations: [],
    } as ConcretePattern,
    usageCount: 10 * version,
    confidence: 0.7 + version * 0.1,
    createdAt: new Date(),
    lastUsedAt: new Date(),
    tags: ['test', `v${version}`],
  });

  beforeEach(() => {
    manager = createPatternVersionManager();
  });

  describe('Factory Function', () => {
    it('should create a PatternVersionManager instance', () => {
      const instance = createPatternVersionManager();
      expect(instance).toBeDefined();
      expect(typeof instance.recordVersion).toBe('function');
    });

    it('should create with custom config', () => {
      const instance = createPatternVersionManager({
        maxVersionsPerPattern: 100,
        autoCleanup: false,
      });
      expect(instance).toBeDefined();
    });
  });

  describe('recordVersion', () => {
    it('should record a new pattern version', () => {
      const pattern = createPattern('PAT-001', 1);

      const versionId = manager.recordVersion(pattern);

      expect(versionId).toBeDefined();
      expect(typeof versionId).toBe('string');
    });

    it('should assign incremental version numbers', () => {
      const pattern1 = createPattern('PAT-001', 1);
      const pattern2 = createPattern('PAT-001', 2);

      const version1 = manager.recordVersion(pattern1);
      const version2 = manager.recordVersion(pattern2);

      expect(version1).not.toBe(version2);
    });

    it('should store pattern snapshot', () => {
      const pattern = createPattern('PAT-001', 1);
      const versionId = manager.recordVersion(pattern);

      const retrieved = manager.getVersion(pattern.id, versionId);

      expect(retrieved).toBeDefined();
      expect(retrieved?.name).toBe(pattern.name);
    });

    it('should record metadata with version', () => {
      const pattern = createPattern('PAT-001', 1);

      manager.recordVersion(pattern, {
        reason: 'Initial version',
        author: 'test-user',
      });

      const history = manager.getHistory(pattern.id);
      expect(history[0].metadata?.reason).toBe('Initial version');
    });
  });

  describe('getHistory', () => {
    it('should return empty array for unknown pattern', () => {
      const history = manager.getHistory('unknown-pattern');
      expect(history).toEqual([]);
    });

    it('should return version history in chronological order', () => {
      const patternId = 'PAT-001';

      manager.recordVersion(createPattern(patternId, 1));
      manager.recordVersion(createPattern(patternId, 2));
      manager.recordVersion(createPattern(patternId, 3));

      const history = manager.getHistory(patternId);

      expect(history).toHaveLength(3);
      expect(history[0].versionNumber).toBeLessThan(history[1].versionNumber);
      expect(history[1].versionNumber).toBeLessThan(history[2].versionNumber);
    });

    it('should include timestamps', () => {
      const pattern = createPattern('PAT-001', 1);
      manager.recordVersion(pattern);

      const history = manager.getHistory(pattern.id);

      expect(history[0].timestamp).toBeInstanceOf(Date);
    });
  });

  describe('getVersion', () => {
    it('should retrieve specific version', () => {
      const patternId = 'PAT-001';
      const v1 = manager.recordVersion(createPattern(patternId, 1));
      manager.recordVersion(createPattern(patternId, 2));
      manager.recordVersion(createPattern(patternId, 3));

      const retrieved = manager.getVersion(patternId, v1);

      expect(retrieved?.name).toContain('v1');
    });

    it('should return undefined for non-existent version', () => {
      const pattern = createPattern('PAT-001', 1);
      manager.recordVersion(pattern);

      const retrieved = manager.getVersion(pattern.id, 'non-existent');

      expect(retrieved).toBeUndefined();
    });
  });

  describe('rollback', () => {
    it('should rollback to specific version', async () => {
      const patternId = 'PAT-001';
      const v1 = manager.recordVersion(createPattern(patternId, 1));
      manager.recordVersion(createPattern(patternId, 2));
      manager.recordVersion(createPattern(patternId, 3));

      const rolledBack = await manager.rollback(patternId, v1);

      expect(rolledBack).toBeDefined();
      expect(rolledBack?.name).toContain('v1');
    });

    it('should create new version after rollback', async () => {
      const patternId = 'PAT-ROLLBACK-NEW';
      const v1 = manager.recordVersion(createPattern(patternId, 1));
      manager.recordVersion(createPattern(patternId, 2));

      const historyBefore = manager.getHistory(patternId);
      expect(historyBefore.length).toBe(2); // Verify initial state
      
      await manager.rollback(patternId, v1);
      const historyAfter = manager.getHistory(patternId);

      // Rollback should create a new version
      expect(historyAfter.length).toBe(3);
    });

    it('should throw for unknown pattern', async () => {
      await expect(
        manager.rollback('unknown', 'v1')
      ).rejects.toThrow();
    });

    it('should throw for unknown version', async () => {
      const pattern = createPattern('PAT-001', 1);
      manager.recordVersion(pattern);

      await expect(
        manager.rollback(pattern.id, 'non-existent')
      ).rejects.toThrow();
    });
  });

  describe('getLatestVersion', () => {
    it('should return latest version', () => {
      const patternId = 'PAT-001';
      manager.recordVersion(createPattern(patternId, 1));
      manager.recordVersion(createPattern(patternId, 2));
      manager.recordVersion(createPattern(patternId, 3));

      const latest = manager.getLatestVersion(patternId);

      expect(latest?.name).toContain('v3');
    });

    it('should return undefined for unknown pattern', () => {
      const latest = manager.getLatestVersion('unknown');
      expect(latest).toBeUndefined();
    });
  });

  describe('compareVersions', () => {
    it('should compare two versions', () => {
      const patternId = 'PAT-001';
      const v1 = manager.recordVersion(createPattern(patternId, 1));
      const v2 = manager.recordVersion(createPattern(patternId, 2));

      const diff = manager.compareVersions(patternId, v1, v2);

      expect(diff).toBeDefined();
      expect(diff.changes).toBeDefined();
    });

    it('should detect no changes for same version', () => {
      const patternId = 'PAT-001';
      const v1 = manager.recordVersion(createPattern(patternId, 1));

      const diff = manager.compareVersions(patternId, v1, v1);

      expect(diff.changes).toHaveLength(0);
    });
  });

  describe('Version Limits', () => {
    it('should respect max versions per pattern', () => {
      const customManager = createPatternVersionManager({
        maxVersionsPerPattern: 3,
        autoCleanup: true,
      });

      const patternId = 'PAT-001';
      for (let i = 1; i <= 5; i++) {
        customManager.recordVersion(createPattern(patternId, i));
      }

      const history = customManager.getHistory(patternId);
      expect(history.length).toBeLessThanOrEqual(3);
    });
  });

  describe('Statistics', () => {
    it('should track version statistics', () => {
      manager.recordVersion(createPattern('PAT-001', 1));
      manager.recordVersion(createPattern('PAT-001', 2));
      manager.recordVersion(createPattern('PAT-002', 1));

      const stats = manager.getStatistics();

      expect(stats.totalVersions).toBe(3);
      expect(stats.totalPatterns).toBe(2);
    });
  });

  describe('Serialization', () => {
    it('should serialize to JSON', () => {
      manager.recordVersion(createPattern('PAT-001', 1));
      manager.recordVersion(createPattern('PAT-001', 2));

      const json = manager.toJSON();
      expect(typeof json).toBe('string');

      const parsed = JSON.parse(json);
      expect(parsed.patterns).toBeDefined();
    });

    it('should deserialize from JSON', () => {
      manager.recordVersion(createPattern('PAT-001', 1));
      const json = manager.toJSON();

      const newManager = createPatternVersionManager();
      newManager.fromJSON(json);

      const history = newManager.getHistory('PAT-001');
      expect(history.length).toBe(1);
    });
  });
});
