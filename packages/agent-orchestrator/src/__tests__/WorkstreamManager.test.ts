/**
 * WorkstreamManager Tests
 *
 * @see TSK-FR-047 - WorkstreamManagerユニットテスト
 */
import { describe, it, expect, beforeEach, vi } from 'vitest';

import {
  type Workstream,
  type WorkstreamTask,
  type WorkstreamStatus,
  type WorkstreamTaskStatus,
  type WorkstreamConfig,
  createWorkstream,
  createWorkstreamTask,
  resetWorkstreamCounters,
  calculateWorkstreamStats,
  DEFAULT_WORKSTREAM_CONFIG,
} from '../domain/value-objects/Workstream.js';

import {
  type IWorkstreamManager,
  WorkstreamManager,
  createWorkstreamManager,
} from '../domain/entities/WorkstreamManager.js';

describe('WorkstreamManager', () => {
  beforeEach(() => {
    resetWorkstreamCounters();
  });

  // ============================================================
  // Type Tests
  // ============================================================
  describe('createWorkstreamTask', () => {
    it('should create a task with auto-generated ID', () => {
      const task = createWorkstreamTask({
        name: 'Test Task',
      });

      expect(task.id).toBe('WST-00001');
      expect(task.name).toBe('Test Task');
      expect(task.status).toBe('queued');
    });

    it('should be immutable', () => {
      const task = createWorkstreamTask({ name: 'Test' });

      expect(() => {
        (task as any).status = 'running';
      }).toThrow();
    });

    it('should include dependencies', () => {
      const task = createWorkstreamTask({
        name: 'Dependent Task',
        dependencies: ['WST-00001', 'WST-00002'],
      });

      expect(task.dependencies).toHaveLength(2);
    });
  });

  describe('createWorkstream', () => {
    it('should create a workstream with auto-generated ID', () => {
      const ws = createWorkstream({
        name: 'Test Workstream',
      });

      expect(ws.id).toBe('WS-00001');
      expect(ws.name).toBe('Test Workstream');
      expect(ws.status).toBe('pending');
    });

    it('should include tasks', () => {
      const ws = createWorkstream({
        name: 'With Tasks',
        tasks: [
          { name: 'Task 1' },
          { name: 'Task 2' },
        ],
      });

      expect(ws.tasks).toHaveLength(2);
    });

    it('should use default maxParallel from config', () => {
      const ws = createWorkstream({ name: 'Test' });

      expect(ws.maxParallel).toBe(DEFAULT_WORKSTREAM_CONFIG.defaultMaxParallel);
    });
  });

  describe('calculateWorkstreamStats', () => {
    it('should calculate stats correctly', () => {
      const ws = createWorkstream({
        name: 'Test',
        tasks: [
          { name: 'Task 1' },
          { name: 'Task 2' },
          { name: 'Task 3' },
        ],
      });

      const stats = calculateWorkstreamStats(ws);

      expect(stats.totalTasks).toBe(3);
      expect(stats.byStatus.queued).toBe(3);
      expect(stats.completionRate).toBe(0);
    });
  });

  // ============================================================
  // WorkstreamManager Tests
  // ============================================================
  describe('create', () => {
    it('should create a workstream', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test Workstream',
      });

      expect(ws.id).toBeDefined();
      expect(ws.status).toBe('pending');
    });

    it('should create with tasks', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'With Tasks',
        tasks: [
          { name: 'Task A' },
          { name: 'Task B' },
        ],
      });

      expect(ws.tasks).toHaveLength(2);
    });

    it('should respect max workstreams limit', async () => {
      const manager = createWorkstreamManager({
        ...DEFAULT_WORKSTREAM_CONFIG,
        maxWorkstreams: 2,
      });

      await manager.create({ name: 'WS 1' });
      await manager.create({ name: 'WS 2' });

      await expect(manager.create({ name: 'WS 3' })).rejects.toThrow();
    });
  });

  describe('get', () => {
    it('should get workstream by ID', async () => {
      const manager = createWorkstreamManager();

      const created = await manager.create({ name: 'Test' });
      const retrieved = await manager.get(created.id);

      expect(retrieved).not.toBeNull();
      expect(retrieved?.id).toBe(created.id);
    });

    it('should return null for unknown ID', async () => {
      const manager = createWorkstreamManager();

      const result = await manager.get('WS-99999');

      expect(result).toBeNull();
    });
  });

  describe('addTask', () => {
    it('should add task to workstream', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({ name: 'Test' });
      const updated = await manager.addTask(ws.id, { name: 'New Task' });

      expect(updated?.tasks).toHaveLength(1);
    });

    it('should return null for unknown workstream', async () => {
      const manager = createWorkstreamManager();

      const result = await manager.addTask('WS-99999', { name: 'Task' });

      expect(result).toBeNull();
    });
  });

  describe('start', () => {
    it('should start workstream', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [{ name: 'Task 1' }],
      });

      const started = await manager.start(ws.id);

      expect(started?.status).toBe('running');
      expect(started?.startedAt).toBeDefined();
    });

    it('should not start empty workstream', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({ name: 'Empty' });

      await expect(manager.start(ws.id)).rejects.toThrow();
    });
  });

  describe('assignTask', () => {
    it('should assign task to agent', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [{ name: 'Task 1' }],
      });
      await manager.start(ws.id);

      const task = await manager.assignTask(ws.id, ws.tasks[0].id, 'agent-001');

      expect(task?.assignedTo).toBe('agent-001');
      expect(task?.status).toBe('assigned');
    });
  });

  describe('completeTask', () => {
    it('should complete task with result', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [{ name: 'Task 1' }],
      });
      await manager.start(ws.id);
      await manager.assignTask(ws.id, ws.tasks[0].id, 'agent-001');

      const task = await manager.completeTask(ws.id, ws.tasks[0].id, { output: 'done' });

      expect(task?.status).toBe('completed');
      expect(task?.result).toEqual({ output: 'done' });
    });

    it('should complete workstream when all tasks done', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [{ name: 'Only Task' }],
      });
      await manager.start(ws.id);
      await manager.assignTask(ws.id, ws.tasks[0].id, 'agent-001');
      await manager.completeTask(ws.id, ws.tasks[0].id, {});

      const updated = await manager.get(ws.id);
      expect(updated?.status).toBe('completed');
    });
  });

  describe('failTask', () => {
    it('should mark task as failed', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [{ name: 'Task 1' }],
      });
      await manager.start(ws.id);
      await manager.assignTask(ws.id, ws.tasks[0].id, 'agent-001');

      const task = await manager.failTask(ws.id, ws.tasks[0].id, 'Something went wrong');

      expect(task?.status).toBe('failed');
      expect(task?.error).toBe('Something went wrong');
    });
  });

  describe('getNextTasks', () => {
    it('should return tasks ready to run', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [
          { name: 'Task 1' },
          { name: 'Task 2' },
        ],
      });
      await manager.start(ws.id);

      const nextTasks = await manager.getNextTasks(ws.id);

      expect(nextTasks.length).toBeGreaterThan(0);
    });

    it('should respect dependencies', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [
          { name: 'Task 1' },
        ],
      });
      // タスク2はタスク1に依存
      await manager.addTask(ws.id, {
        name: 'Task 2',
        dependencies: [ws.tasks[0].id],
      });
      await manager.start(ws.id);

      const nextTasks = await manager.getNextTasks(ws.id);

      // Task 1のみが実行可能
      expect(nextTasks).toHaveLength(1);
      expect(nextTasks[0].name).toBe('Task 1');
    });

    it('should respect maxParallel', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        maxParallel: 2,
        tasks: [
          { name: 'Task 1' },
          { name: 'Task 2' },
          { name: 'Task 3' },
          { name: 'Task 4' },
        ],
      });
      await manager.start(ws.id);

      const nextTasks = await manager.getNextTasks(ws.id);

      expect(nextTasks.length).toBeLessThanOrEqual(2);
    });
  });

  describe('getStats', () => {
    it('should return workstream statistics', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [
          { name: 'Task 1' },
          { name: 'Task 2' },
        ],
      });

      const stats = await manager.getStats(ws.id);

      expect(stats).not.toBeNull();
      expect(stats?.totalTasks).toBe(2);
    });
  });

  describe('list', () => {
    it('should list all workstreams', async () => {
      const manager = createWorkstreamManager();

      await manager.create({ name: 'WS 1' });
      await manager.create({ name: 'WS 2' });

      const all = await manager.list();

      expect(all).toHaveLength(2);
    });
  });

  describe('cancel', () => {
    it('should cancel workstream', async () => {
      const manager = createWorkstreamManager();

      const ws = await manager.create({
        name: 'Test',
        tasks: [{ name: 'Task 1' }],
      });
      await manager.start(ws.id);

      const cancelled = await manager.cancel(ws.id);

      expect(cancelled?.status).toBe('cancelled');
    });
  });
});
