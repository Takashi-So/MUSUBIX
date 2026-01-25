/**
 * TodoWrite Integration Tests
 *
 * @see REQ-SM-004 - TodoWrite統合
 */

import { describe, it, expect, beforeEach } from 'vitest';

import {
  createTodoWriteIntegration,
  formatTaskList,
  formatQualityCheckResult,
  type TodoWriteIntegration,
} from '../../src/skills/session-manager/index.js';

describe('TodoWriteIntegration', () => {
  let integration: TodoWriteIntegration;

  beforeEach(() => {
    integration = createTodoWriteIntegration();
  });

  describe('createTask', () => {
    it('should create a new task', () => {
      const task = integration.createTask({
        title: 'Test Task',
        description: 'Test Description',
      });

      expect(task.id).toMatch(/^task-\d+-[a-z0-9]+$/);
      expect(task.title).toBe('Test Task');
      expect(task.description).toBe('Test Description');
      expect(task.status).toBe('not-started');
      expect(task.order).toBe(0);
    });

    it('should increment order for subsequent tasks', () => {
      const task1 = integration.createTask({ title: 'Task 1' });
      const task2 = integration.createTask({ title: 'Task 2' });
      const task3 = integration.createTask({ title: 'Task 3' });

      expect(task1.order).toBe(0);
      expect(task2.order).toBe(1);
      expect(task3.order).toBe(2);
    });

    it('should create blocked task with reason', () => {
      const task = integration.createTask({
        title: 'Blocked Task',
        blockedReason: 'Waiting for dependency',
      });

      expect(task.status).toBe('blocked');
      expect(task.blockedReason).toBe('Waiting for dependency');
    });

    it('should allow custom order', () => {
      const task = integration.createTask({
        title: 'Task',
        order: 10,
      });

      expect(task.order).toBe(10);
    });
  });

  describe('updateTaskStatus', () => {
    it('should update task status', () => {
      const task = integration.createTask({ title: 'Task' });
      const updated = integration.updateTaskStatus(task.id, 'in-progress');

      expect(updated).not.toBeNull();
      expect(updated!.status).toBe('in-progress');
    });

    it('should set blocked reason when blocking', () => {
      const task = integration.createTask({ title: 'Task' });
      const updated = integration.updateTaskStatus(task.id, 'blocked', 'Waiting');

      expect(updated!.status).toBe('blocked');
      expect(updated!.blockedReason).toBe('Waiting');
    });

    it('should clear blocked reason when unblocking', () => {
      const task = integration.createTask({ title: 'Task', blockedReason: 'Waiting' });
      const updated = integration.updateTaskStatus(task.id, 'in-progress');

      expect(updated!.status).toBe('in-progress');
      expect(updated!.blockedReason).toBeUndefined();
    });

    it('should return null for non-existent task', () => {
      const result = integration.updateTaskStatus('non-existent', 'completed');
      expect(result).toBeNull();
    });
  });

  describe('getAllTasks', () => {
    it('should return all tasks sorted by order', () => {
      integration.createTask({ title: 'Task 1', order: 2 });
      integration.createTask({ title: 'Task 2', order: 0 });
      integration.createTask({ title: 'Task 3', order: 1 });

      const tasks = integration.getAllTasks();

      expect(tasks).toHaveLength(3);
      expect(tasks[0].title).toBe('Task 2');
      expect(tasks[1].title).toBe('Task 3');
      expect(tasks[2].title).toBe('Task 1');
    });
  });

  describe('getTasksByStatus', () => {
    it('should filter tasks by status', () => {
      const task1 = integration.createTask({ title: 'Task 1' });
      integration.createTask({ title: 'Task 2' });
      integration.updateTaskStatus(task1.id, 'completed');

      const completedTasks = integration.getTasksByStatus('completed');
      const notStartedTasks = integration.getTasksByStatus('not-started');

      expect(completedTasks).toHaveLength(1);
      expect(completedTasks[0].title).toBe('Task 1');
      expect(notStartedTasks).toHaveLength(1);
      expect(notStartedTasks[0].title).toBe('Task 2');
    });
  });

  describe('checkQuality', () => {
    it('should pass for well-structured tasks', () => {
      integration.createTask({ title: '要件確認' });
      integration.createTask({ title: '設計作成' });
      integration.createTask({ title: '実装' });
      integration.createTask({ title: 'テスト作成' });

      const result = integration.checkQuality();

      expect(result.isValid).toBe(true);
    });

    it('should detect order issues', () => {
      const task1 = integration.createTask({ title: 'Task 1', order: 0 });
      integration.createTask({ title: 'Task 2', order: 1 });
      integration.createTask({ title: 'Task 3', order: 2 });

      // Skip task 2 and start task 3
      integration.updateTaskStatus(task1.id, 'completed');
      const task3 = integration.getAllTasks().find((t) => t.title === 'Task 3');
      integration.updateTaskStatus(task3!.id, 'in-progress');

      const result = integration.checkQuality();

      expect(result.issues.some((i) => i.type === 'order-error')).toBe(true);
    });

    it('should detect granularity issues', () => {
      const longTitle = 'A'.repeat(150);
      integration.createTask({ title: longTitle });

      const result = integration.checkQuality();

      expect(result.issues.some((i) => i.type === 'granularity')).toBe(true);
    });

    it('should detect missing steps for single implementation task', () => {
      integration.createTask({ title: '機能を実装する' });

      const result = integration.checkQuality();

      expect(result.issues.some((i) => i.type === 'missing-step')).toBe(true);
    });

    it('should suggest test task when missing', () => {
      integration.createTask({ title: '要件確認' });
      integration.createTask({ title: '設計作成' });
      integration.createTask({ title: '実装' });

      const result = integration.checkQuality();

      expect(result.suggestions.some((s) => s.includes('テスト'))).toBe(true);
    });

    it('should detect blocked tasks without reason', () => {
      const task = integration.createTask({ title: 'Task' });
      // Manually set blocked without reason (bypassing normal flow)
      integration.updateTaskStatus(task.id, 'blocked');

      const result = integration.checkQuality();

      expect(result.isValid).toBe(false);
      expect(result.issues.some((i) => i.type === 'requirement-mismatch')).toBe(true);
    });

    it('should suggest limiting in-progress tasks', () => {
      for (let i = 0; i < 5; i++) {
        const task = integration.createTask({ title: `Task ${i}` });
        integration.updateTaskStatus(task.id, 'in-progress');
      }

      const result = integration.checkQuality();

      expect(result.suggestions.some((s) => s.includes('多すぎます'))).toBe(true);
    });
  });

  describe('reorderTasks', () => {
    it('should reorder tasks', () => {
      const task1 = integration.createTask({ title: 'Task 1' });
      const task2 = integration.createTask({ title: 'Task 2' });
      const task3 = integration.createTask({ title: 'Task 3' });

      integration.reorderTasks([task3.id, task1.id, task2.id]);

      const tasks = integration.getAllTasks();
      expect(tasks[0].title).toBe('Task 3');
      expect(tasks[1].title).toBe('Task 1');
      expect(tasks[2].title).toBe('Task 2');
    });
  });

  describe('exportToSession / importFromSession', () => {
    it('should export tasks to session format', () => {
      const task1 = integration.createTask({ title: 'Task 1' });
      const task2 = integration.createTask({ title: 'Task 2' });
      const task3 = integration.createTask({ title: 'Task 3', blockedReason: 'Waiting' });

      integration.updateTaskStatus(task1.id, 'completed');
      integration.updateTaskStatus(task2.id, 'in-progress');

      const exported = integration.exportToSession();

      expect(exported.completedTasks).toHaveLength(1);
      expect(exported.inProgressTasks).toHaveLength(1);
      expect(exported.blockedTasks).toHaveLength(1);
    });

    it('should import tasks from session', () => {
      const task1 = integration.createTask({ title: 'Task 1' });
      integration.updateTaskStatus(task1.id, 'completed');
      const exported = integration.exportToSession();

      // Create new integration and import
      const newIntegration = createTodoWriteIntegration();
      newIntegration.importFromSession(exported);

      const tasks = newIntegration.getAllTasks();
      expect(tasks).toHaveLength(1);
      expect(tasks[0].title).toBe('Task 1');
      expect(tasks[0].status).toBe('completed');
    });
  });

  describe('clear', () => {
    it('should remove all tasks', () => {
      integration.createTask({ title: 'Task 1' });
      integration.createTask({ title: 'Task 2' });

      integration.clear();

      expect(integration.getAllTasks()).toHaveLength(0);
    });
  });
});

describe('formatTaskList', () => {
  it('should format task list as markdown', () => {
    const integration = createTodoWriteIntegration();

    const task1 = integration.createTask({ title: 'Task 1' });
    integration.createTask({ title: 'Task 2' });
    integration.createTask({ title: 'Task 3', blockedReason: 'Waiting' });

    integration.updateTaskStatus(task1.id, 'completed');

    const formatted = formatTaskList(integration);

    expect(formatted).toContain('## タスクリスト');
    expect(formatted).toContain('### 完了');
    expect(formatted).toContain('[x] Task 1');
    expect(formatted).toContain('### 未開始');
    expect(formatted).toContain('[ ] Task 2');
    expect(formatted).toContain('### ブロック中');
    expect(formatted).toContain('🚫 Task 3');
    expect(formatted).toContain('**進捗**');
  });
});

describe('formatQualityCheckResult', () => {
  it('should format passing result', () => {
    const result = {
      isValid: true,
      issues: [],
      suggestions: [],
    };

    const formatted = formatQualityCheckResult(result);

    expect(formatted).toContain('✅ **品質チェック合格**');
  });

  it('should format failing result with issues', () => {
    const result = {
      isValid: false,
      issues: [
        {
          type: 'order-error' as const,
          taskId: 'task-1',
          description: 'Order issue',
          suggestion: 'Fix order',
          severity: 'error' as const,
        },
      ],
      suggestions: ['Add tests'],
    };

    const formatted = formatQualityCheckResult(result);

    expect(formatted).toContain('❌ **品質チェック不合格**');
    expect(formatted).toContain('### 問題点');
    expect(formatted).toContain('Order issue');
    expect(formatted).toContain('Fix order');
    expect(formatted).toContain('### 提案');
    expect(formatted).toContain('Add tests');
  });
});
