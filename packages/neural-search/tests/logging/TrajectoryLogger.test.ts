/**
 * TrajectoryLogger Tests
 * 
 * @see TSK-NS-107 - TrajectoryLogger実装
 * @see REQ-NS-107 - 探索軌跡ログ要件
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  TrajectoryLogger,
  createTrajectoryLogger,
  type BranchRecord,
  type TrajectoryExportFormat,
} from '../../src/logging/TrajectoryLogger.js';

describe('TrajectoryLogger', () => {
  let logger: TrajectoryLogger;

  beforeEach(() => {
    logger = createTrajectoryLogger();
  });

  describe('Interface Definition', () => {
    it('should have logBranch method', () => {
      expect(typeof logger.logBranch).toBe('function');
    });

    it('should have export method', () => {
      expect(typeof logger.export).toBe('function');
    });

    it('should have getTrajectory method', () => {
      expect(typeof logger.getTrajectory).toBe('function');
    });

    it('should have clear method', () => {
      expect(typeof logger.clear).toBe('function');
    });
  });

  describe('Branch Logging', () => {
    it('should log a branch record', () => {
      const branch: BranchRecord = {
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: { query: 'test' },
      };

      logger.logBranch(branch);
      const trajectory = logger.getTrajectory();

      expect(trajectory.branches).toHaveLength(1);
      expect(trajectory.branches[0].id).toBe('branch-001');
    });

    it('should log multiple branches', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      logger.logBranch({
        id: 'branch-002',
        parentId: 'branch-001',
        depth: 1,
        score: 0.90,
        timestamp: new Date(),
        state: {},
      });

      const trajectory = logger.getTrajectory();
      expect(trajectory.branches).toHaveLength(2);
    });

    it('should maintain parent-child relationships', () => {
      logger.logBranch({
        id: 'parent',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      logger.logBranch({
        id: 'child',
        parentId: 'parent',
        depth: 1,
        score: 0.90,
        timestamp: new Date(),
        state: {},
      });

      const trajectory = logger.getTrajectory();
      const child = trajectory.branches.find(b => b.id === 'child');
      expect(child?.parentId).toBe('parent');
    });

    it('should track maximum depth', () => {
      logger.logBranch({ id: 'b1', parentId: null, depth: 0, score: 0.5, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b2', parentId: 'b1', depth: 1, score: 0.6, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b3', parentId: 'b2', depth: 2, score: 0.7, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b4', parentId: 'b3', depth: 3, score: 0.8, timestamp: new Date(), state: {} });

      const trajectory = logger.getTrajectory();
      expect(trajectory.maxDepth).toBe(3);
    });

    it('should track best score', () => {
      logger.logBranch({ id: 'b1', parentId: null, depth: 0, score: 0.5, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b2', parentId: 'b1', depth: 1, score: 0.9, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b3', parentId: 'b2', depth: 2, score: 0.7, timestamp: new Date(), state: {} });

      const trajectory = logger.getTrajectory();
      expect(trajectory.bestScore).toBe(0.9);
    });
  });

  describe('JSON Export', () => {
    it('should export trajectory as JSON', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date('2026-01-08T12:00:00Z'),
        state: { query: 'test' },
      });

      const result = logger.export('json');

      expect(typeof result).toBe('string');
      const parsed = JSON.parse(result);
      expect(parsed.branches).toHaveLength(1);
      expect(parsed.branches[0].id).toBe('branch-001');
    });

    it('should include metadata in JSON export', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      const result = logger.export('json');
      const parsed = JSON.parse(result);

      expect(parsed).toHaveProperty('branches');
      expect(parsed).toHaveProperty('totalBranches');
      expect(parsed).toHaveProperty('maxDepth');
      expect(parsed).toHaveProperty('bestScore');
    });

    it('should format JSON with indentation', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      const result = logger.export('json');
      expect(result).toContain('\n');
      expect(result).toContain('  ');
    });
  });

  describe('Parquet Export', () => {
    it('should export trajectory as Parquet-compatible format', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date('2026-01-08T12:00:00Z'),
        state: { query: 'test' },
      });

      const result = logger.export('parquet');

      // Parquet export returns a base64-encoded string or schema descriptor
      expect(typeof result).toBe('string');
      expect(result.length).toBeGreaterThan(0);
    });

    it('should include schema information for Parquet', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      const result = logger.export('parquet');
      // Schema should be present as JSON descriptor for Parquet
      const parsed = JSON.parse(result);
      expect(parsed).toHaveProperty('schema');
      expect(parsed).toHaveProperty('data');
    });
  });

  describe('Clear', () => {
    it('should clear all logged branches', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      logger.clear();
      const trajectory = logger.getTrajectory();

      expect(trajectory.branches).toHaveLength(0);
      expect(trajectory.totalBranches).toBe(0);
    });

    it('should reset statistics after clear', () => {
      logger.logBranch({ id: 'b1', parentId: null, depth: 0, score: 0.9, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b2', parentId: 'b1', depth: 3, score: 0.5, timestamp: new Date(), state: {} });

      logger.clear();
      const trajectory = logger.getTrajectory();

      expect(trajectory.maxDepth).toBe(0);
      expect(trajectory.bestScore).toBe(0);
    });
  });

  describe('Export Format Validation', () => {
    it('should accept json format', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      expect(() => logger.export('json')).not.toThrow();
    });

    it('should accept parquet format', () => {
      logger.logBranch({
        id: 'branch-001',
        parentId: null,
        depth: 0,
        score: 0.85,
        timestamp: new Date(),
        state: {},
      });

      expect(() => logger.export('parquet')).not.toThrow();
    });

    it('should throw for invalid format', () => {
      expect(() => logger.export('invalid' as TrajectoryExportFormat)).toThrow();
    });
  });

  describe('Statistics', () => {
    it('should calculate average score', () => {
      logger.logBranch({ id: 'b1', parentId: null, depth: 0, score: 0.6, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b2', parentId: 'b1', depth: 1, score: 0.8, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b3', parentId: 'b2', depth: 2, score: 1.0, timestamp: new Date(), state: {} });

      const trajectory = logger.getTrajectory();
      expect(trajectory.averageScore).toBeCloseTo(0.8, 2);
    });

    it('should count branches by depth', () => {
      logger.logBranch({ id: 'b1', parentId: null, depth: 0, score: 0.5, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b2', parentId: 'b1', depth: 1, score: 0.6, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b3', parentId: 'b1', depth: 1, score: 0.7, timestamp: new Date(), state: {} });
      logger.logBranch({ id: 'b4', parentId: 'b2', depth: 2, score: 0.8, timestamp: new Date(), state: {} });

      const trajectory = logger.getTrajectory();
      expect(trajectory.branchesByDepth[0]).toBe(1);
      expect(trajectory.branchesByDepth[1]).toBe(2);
      expect(trajectory.branchesByDepth[2]).toBe(1);
    });
  });
});
