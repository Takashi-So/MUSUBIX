/**
 * TriageEngine Tests
 *
 * @see TSK-FR-027 - TriageEngineユニットテスト
 */
import { describe, it, expect } from 'vitest';

import {
  type TriageTask,
  type TriageConfig,
  blocksNewWork,
  comparePriority,
  createTriageResult,
  PRIORITY_LEVELS,
} from '../../value-objects/PriorityLevel.js';

import {
  createTriageEngine,
} from '../TriageEngine.js';

describe('TriageEngine', () => {
  // ============================================================
  // Value Object Tests
  // ============================================================
  describe('PriorityLevel Value Objects', () => {
    describe('PRIORITY_LEVELS', () => {
      it('should have all priority levels defined', () => {
        expect(PRIORITY_LEVELS.has('P0')).toBe(true);
        expect(PRIORITY_LEVELS.has('P1')).toBe(true);
        expect(PRIORITY_LEVELS.has('P2')).toBe(true);
        expect(PRIORITY_LEVELS.has('P3')).toBe(true);
      });

      it('should mark P0 and P1 as blocking', () => {
        expect(PRIORITY_LEVELS.get('P0')?.blocksNewWork).toBe(true);
        expect(PRIORITY_LEVELS.get('P1')?.blocksNewWork).toBe(true);
        expect(PRIORITY_LEVELS.get('P2')?.blocksNewWork).toBe(false);
        expect(PRIORITY_LEVELS.get('P3')?.blocksNewWork).toBe(false);
      });
    });

    describe('blocksNewWork', () => {
      it('should return true for P0', () => {
        expect(blocksNewWork('P0')).toBe(true);
      });

      it('should return true for P1', () => {
        expect(blocksNewWork('P1')).toBe(true);
      });

      it('should return false for P2', () => {
        expect(blocksNewWork('P2')).toBe(false);
      });

      it('should return false for P3', () => {
        expect(blocksNewWork('P3')).toBe(false);
      });
    });

    describe('comparePriority', () => {
      it('should return negative for higher priority', () => {
        expect(comparePriority('P0', 'P1')).toBeLessThan(0);
        expect(comparePriority('P1', 'P2')).toBeLessThan(0);
      });

      it('should return positive for lower priority', () => {
        expect(comparePriority('P2', 'P1')).toBeGreaterThan(0);
        expect(comparePriority('P3', 'P0')).toBeGreaterThan(0);
      });

      it('should return 0 for same priority', () => {
        expect(comparePriority('P1', 'P1')).toBe(0);
      });
    });

    describe('createTriageResult', () => {
      it('should create an immutable triage result', () => {
        const result = createTriageResult({
          taskId: 'TSK-001',
          priority: 'P0',
          reason: 'Critical bug',
          suggestedAction: 'Fix immediately',
        });

        expect(result.taskId).toBe('TSK-001');
        expect(result.priority).toBe('P0');
        expect(() => {
          (result as any).priority = 'P3';
        }).toThrow();
      });
    });
  });

  // ============================================================
  // TriageEngine Tests
  // ============================================================
  describe('checkPriorityBlocking', () => {
    it('should pass when no blocking tasks exist', async () => {
      const engine = createTriageEngine();

      const result = await engine.checkPriorityBlocking();

      expect(result.passed).toBe(true);
      expect(result.blockingTasks).toHaveLength(0);
    });

    it('should fail when P0 task exists', async () => {
      const engine = createTriageEngine();
      const task: TriageTask = {
        id: 'TSK-001',
        title: 'Critical Bug',
        priority: 'P0',
        status: 'open',
        type: 'bug',
        createdAt: new Date(),
      };
      engine.addTask(task);

      const result = await engine.checkPriorityBlocking();

      expect(result.passed).toBe(false);
      expect(result.blockingTasks).toHaveLength(1);
      expect(result.blockingTasks[0].priority).toBe('P0');
      expect(result.severity).toBe('error');
    });

    it('should fail when P1 task exists', async () => {
      const engine = createTriageEngine();
      const task: TriageTask = {
        id: 'TSK-002',
        title: 'High Priority Issue',
        priority: 'P1',
        status: 'open',
        type: 'bug',
        createdAt: new Date(),
      };
      engine.addTask(task);

      const result = await engine.checkPriorityBlocking();

      expect(result.passed).toBe(false);
      expect(result.blockingTasks).toHaveLength(1);
    });

    it('should pass when only P2/P3 tasks exist', async () => {
      const engine = createTriageEngine();
      engine.addTask({
        id: 'TSK-003',
        title: 'Normal Task',
        priority: 'P2',
        status: 'open',
        type: 'task',
        createdAt: new Date(),
      });
      engine.addTask({
        id: 'TSK-004',
        title: 'Low Priority',
        priority: 'P3',
        status: 'open',
        type: 'improvement',
        createdAt: new Date(),
      });

      const result = await engine.checkPriorityBlocking();

      expect(result.passed).toBe(true);
    });

    it('should ignore resolved tasks', async () => {
      const engine = createTriageEngine();
      engine.addTask({
        id: 'TSK-005',
        title: 'Resolved Critical',
        priority: 'P0',
        status: 'resolved',
        type: 'bug',
        createdAt: new Date(),
      });

      const result = await engine.checkPriorityBlocking();

      expect(result.passed).toBe(true);
    });

    it('should respect custom configuration', async () => {
      const config: TriageConfig = {
        blockingPriorities: ['P0'], // Only P0 blocks
        activeStatuses: ['open'],
        includeInProgress: false,
        maxBlockingAgeDays: 30,
      };
      const engine = createTriageEngine(config);
      engine.addTask({
        id: 'TSK-006',
        title: 'P1 Task',
        priority: 'P1',
        status: 'open',
        type: 'bug',
        createdAt: new Date(),
      });

      const result = await engine.checkPriorityBlocking();

      expect(result.passed).toBe(true); // P1 doesn't block with custom config
    });
  });

  describe('triageTask', () => {
    it('should triage a bug as high priority', async () => {
      const engine = createTriageEngine();
      const task: TriageTask = {
        id: 'TSK-007',
        title: 'Application Crash',
        type: 'bug',
        status: 'open',
        createdAt: new Date(),
      };

      const result = await engine.triageTask(task);

      expect(result.taskId).toBe('TSK-007');
      expect(['P0', 'P1']).toContain(result.priority);
    });

    it('should triage a feature as normal priority', async () => {
      const engine = createTriageEngine();
      const task: TriageTask = {
        id: 'TSK-008',
        title: 'Add Dark Mode',
        type: 'feature',
        status: 'open',
        createdAt: new Date(),
      };

      const result = await engine.triageTask(task);

      expect(result.taskId).toBe('TSK-008');
      expect(['P2', 'P3']).toContain(result.priority);
    });

    it('should preserve existing priority if set', async () => {
      const engine = createTriageEngine();
      const task: TriageTask = {
        id: 'TSK-009',
        title: 'Pre-triaged Task',
        type: 'task',
        priority: 'P1',
        status: 'open',
        createdAt: new Date(),
      };

      const result = await engine.triageTask(task);

      expect(result.priority).toBe('P1');
    });
  });

  describe('getBlockingTasks', () => {
    it('should return all blocking tasks sorted by priority', async () => {
      const engine = createTriageEngine();
      engine.addTask({
        id: 'TSK-010',
        title: 'P1 Task',
        priority: 'P1',
        status: 'open',
        type: 'bug',
        createdAt: new Date(),
      });
      engine.addTask({
        id: 'TSK-011',
        title: 'P0 Task',
        priority: 'P0',
        status: 'open',
        type: 'bug',
        createdAt: new Date(),
      });

      const blockingTasks = await engine.getBlockingTasks();

      expect(blockingTasks).toHaveLength(2);
      expect(blockingTasks[0].priority).toBe('P0'); // P0 first
      expect(blockingTasks[1].priority).toBe('P1');
    });
  });

  describe('addTask / removeTask', () => {
    it('should add and remove tasks', () => {
      const engine = createTriageEngine();
      const task: TriageTask = {
        id: 'TSK-012',
        title: 'Test Task',
        priority: 'P2',
        status: 'open',
        type: 'task',
        createdAt: new Date(),
      };

      engine.addTask(task);
      expect(engine.getTasks()).toHaveLength(1);

      engine.removeTask('TSK-012');
      expect(engine.getTasks()).toHaveLength(0);
    });
  });

  describe('updateTask', () => {
    it('should update task status', () => {
      const engine = createTriageEngine();
      engine.addTask({
        id: 'TSK-013',
        title: 'Task to Update',
        priority: 'P0',
        status: 'open',
        type: 'bug',
        createdAt: new Date(),
      });

      engine.updateTask('TSK-013', { status: 'resolved' });

      const task = engine.getTasks().find(t => t.id === 'TSK-013');
      expect(task?.status).toBe('resolved');
    });
  });

  describe('clear', () => {
    it('should clear all tasks', () => {
      const engine = createTriageEngine();
      engine.addTask({
        id: 'TSK-014',
        title: 'Task 1',
        priority: 'P2',
        status: 'open',
        type: 'task',
        createdAt: new Date(),
      });
      engine.addTask({
        id: 'TSK-015',
        title: 'Task 2',
        priority: 'P3',
        status: 'open',
        type: 'task',
        createdAt: new Date(),
      });

      engine.clear();

      expect(engine.getTasks()).toHaveLength(0);
    });
  });
});
