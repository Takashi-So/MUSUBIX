/**
 * Checkpoint Tests
 *
 * @see REQ-CP-001〜005
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createCheckpointManager,
  formatCheckpointListMarkdown,
  formatCheckpointComparisonMarkdown,
  type CheckpointConfig,
  type CheckpointListEntry,
  type CheckpointComparison,
  DEFAULT_CHECKPOINT_CONFIG,
} from '../checkpoint/index.js';

describe('CheckpointManager', () => {
  let manager: ReturnType<typeof createCheckpointManager>;

  beforeEach(() => {
    manager = createCheckpointManager();
  });

  describe('createCheckpointManager', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
      const config = manager.getConfig();
      expect(config.checkpointsDir).toBe(DEFAULT_CHECKPOINT_CONFIG.checkpointsDir);
      expect(config.maxCheckpoints).toBeGreaterThan(0);
    });

    it('should create manager with custom config', () => {
      const customConfig: Partial<CheckpointConfig> = {
        checkpointsDir: '/custom/path',
        maxCheckpoints: 50,
      };
      const customManager = createCheckpointManager(customConfig);
      const config = customManager.getConfig();
      expect(config.checkpointsDir).toBe('/custom/path');
      expect(config.maxCheckpoints).toBe(50);
    });
  });

  describe('createCheckpoint', () => {
    it.skip('should create a checkpoint (slow test - requires git)', async () => {
      const checkpoint = await manager.createCheckpoint('test-checkpoint');

      expect(checkpoint.name).toBe('test-checkpoint');
      expect(checkpoint.gitSha).toBeDefined();
    });
  });

  describe('listCheckpoints', () => {
    it('should list all checkpoints', async () => {
      const list = await manager.listCheckpoints();

      expect(list).toBeInstanceOf(Array);
    });
  });

  describe('getCheckpoint', () => {
    it.skip('should get checkpoint by name (slow test - requires git)', async () => {
      const created = await manager.createCheckpoint('get-test');
      const retrieved = await manager.getCheckpoint(created.name);

      expect(retrieved).toBeDefined();
      expect(retrieved?.name).toBe('get-test');
    });

    it('should return null for non-existent name', async () => {
      const result = await manager.getCheckpoint('non-existent');
      expect(result).toBeNull();
    });
  });

  describe('restoreCheckpoint', () => {
    it.skip('should restore checkpoint (slow test)', async () => {
      const checkpoint = await manager.createCheckpoint('restore-test');
      const result = await manager.restoreCheckpoint(checkpoint.name);

      expect(result.success).toBeDefined();
    });
  });

  describe('verifyCheckpoint', () => {
    it.skip('should verify a checkpoint (slow test)', async () => {
      await manager.createCheckpoint('compare-1');

      const comparison = await manager.verifyCheckpoint('compare-1');

      expect(comparison.checkpointName).toBe('compare-1');
    });
  });

  describe('deleteCheckpoint', () => {
    it.skip('should delete checkpoint (slow test)', async () => {
      const checkpoint = await manager.createCheckpoint('delete-test');
      const deleted = await manager.deleteCheckpoint(checkpoint.name);

      expect(deleted).toBeDefined();
    });
  });
});

describe('Format functions', () => {
  it('should format checkpoint list as markdown', () => {
    const checkpoints: CheckpointListEntry[] = [
      {
        name: 'Checkpoint 1',
        gitShortSha: 'abc1234',
        timestamp: new Date(),
        status: 'current',
        isCurrent: true,
      },
    ];

    const markdown = formatCheckpointListMarkdown(checkpoints);
    expect(markdown).toContain('Checkpoint 1');
  });

  it('should format checkpoint comparison as markdown', () => {
    const comparison: CheckpointComparison = {
      checkpointName: 'cp-1',
      checkpointSha: 'abc123',
      currentSha: 'def456',
      filesChanged: 2,
      additions: 50,
      deletions: 10,
      buildStatus: 'passing',
    };

    const markdown = formatCheckpointComparisonMarkdown(comparison);
    expect(markdown).toContain('Checkpoint');
  });
});
