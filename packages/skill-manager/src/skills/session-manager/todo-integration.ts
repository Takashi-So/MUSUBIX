/**
 * TodoWrite Integration
 *
 * Multi-step task tracking with quality checks
 *
 * @see REQ-SM-004 - TodoWrite統合
 * @see DES-v3.7.0 Section 4.4 - TodoWriteIntegration
 */

import type { TodoItem, TodoStatus, SessionData } from './types.js';

/**
 * Task quality issue types
 */
export type TaskQualityIssueType =
  | 'order-error' // 実行順序の問題
  | 'missing-step' // 欠落ステップ
  | 'granularity' // 粒度の問題
  | 'requirement-mismatch'; // 要件との不整合

/**
 * Task quality issue
 */
export interface TaskQualityIssue {
  readonly type: TaskQualityIssueType;
  readonly taskId?: string;
  readonly description: string;
  readonly suggestion: string;
  readonly severity: 'warning' | 'error';
}

/**
 * Task quality check result
 */
export interface TaskQualityCheckResult {
  readonly isValid: boolean;
  readonly issues: TaskQualityIssue[];
  readonly suggestions: string[];
}

/**
 * Task creation options
 */
export interface CreateTaskOptions {
  readonly title: string;
  readonly description?: string;
  readonly order?: number;
  readonly blockedReason?: string;
}

/**
 * TodoWrite integration interface
 */
export interface TodoWriteIntegration {
  /**
   * Create a new task
   */
  createTask(options: CreateTaskOptions): TodoItem;

  /**
   * Update task status
   */
  updateTaskStatus(taskId: string, status: TodoStatus, blockedReason?: string): TodoItem | null;

  /**
   * Get all tasks
   */
  getAllTasks(): TodoItem[];

  /**
   * Get tasks by status
   */
  getTasksByStatus(status: TodoStatus): TodoItem[];

  /**
   * Check task quality
   */
  checkQuality(): TaskQualityCheckResult;

  /**
   * Reorder tasks
   */
  reorderTasks(taskIds: string[]): void;

  /**
   * Export tasks to session data format
   */
  exportToSession(): Pick<SessionData, 'completedTasks' | 'inProgressTasks' | 'blockedTasks'>;

  /**
   * Import tasks from session data
   */
  importFromSession(
    session: Pick<SessionData, 'completedTasks' | 'inProgressTasks' | 'blockedTasks'>
  ): void;

  /**
   * Clear all tasks
   */
  clear(): void;
}

/**
 * Generate unique task ID
 */
function generateTaskId(): string {
  return `task-${Date.now()}-${Math.random().toString(36).slice(2, 7)}`;
}

/**
 * Create TodoWrite integration
 *
 * @returns TodoWriteIntegration instance
 */
export function createTodoWriteIntegration(): TodoWriteIntegration {
  const tasks: Map<string, TodoItem> = new Map();

  return {
    createTask(options: CreateTaskOptions): TodoItem {
      const id = generateTaskId();
      const now = new Date();
      const order = options.order ?? tasks.size;

      const task: TodoItem = {
        id,
        title: options.title,
        description: options.description,
        status: options.blockedReason ? 'blocked' : 'not-started',
        order,
        createdAt: now,
        updatedAt: now,
        blockedReason: options.blockedReason,
      };

      tasks.set(id, task);
      return task;
    },

    updateTaskStatus(taskId: string, status: TodoStatus, blockedReason?: string): TodoItem | null {
      const task = tasks.get(taskId);
      if (!task) return null;

      const updatedTask: TodoItem = {
        ...task,
        status,
        updatedAt: new Date(),
        blockedReason: status === 'blocked' ? blockedReason : undefined,
      };

      tasks.set(taskId, updatedTask);
      return updatedTask;
    },

    getAllTasks(): TodoItem[] {
      return Array.from(tasks.values()).sort((a, b) => a.order - b.order);
    },

    getTasksByStatus(status: TodoStatus): TodoItem[] {
      return this.getAllTasks().filter((task) => task.status === status);
    },

    checkQuality(): TaskQualityCheckResult {
      const allTasks = this.getAllTasks();
      const issues: TaskQualityIssue[] = [];
      const suggestions: string[] = [];

      // Check 1: Order validation
      const inProgressTasks = allTasks.filter((t) => t.status === 'in-progress');
      const completedTasks = allTasks.filter((t) => t.status === 'completed');

      for (const inProgress of inProgressTasks) {
        // Check if there are not-started tasks with lower order than in-progress
        const skippedTasks = allTasks.filter(
          (t) => t.status === 'not-started' && t.order < inProgress.order
        );

        if (skippedTasks.length > 0) {
          issues.push({
            type: 'order-error',
            taskId: inProgress.id,
            description: `タスク「${inProgress.title}」の前に未開始のタスクがあります`,
            suggestion: `先に ${skippedTasks.map((t) => `「${t.title}」`).join(', ')} を完了してください`,
            severity: 'warning',
          });
        }
      }

      // Check 2: Granularity check
      const longTitleTasks = allTasks.filter((t) => t.title.length > 100);
      for (const task of longTitleTasks) {
        issues.push({
          type: 'granularity',
          taskId: task.id,
          description: `タスク「${task.title.slice(0, 50)}...」が複雑すぎる可能性があります`,
          suggestion: 'より小さなタスクに分割することを検討してください',
          severity: 'warning',
        });
      }

      // Check 3: Too few tasks for complex work
      if (allTasks.length === 1 && allTasks[0].title.includes('実装')) {
        issues.push({
          type: 'missing-step',
          description: '「実装」タスクが1つだけです',
          suggestion: 'テスト作成、レビュー、ドキュメント更新などのステップを追加してください',
          severity: 'warning',
        });
      }

      // Check 4: No test task
      const hasTestTask = allTasks.some(
        (t) =>
          t.title.toLowerCase().includes('test') ||
          t.title.includes('テスト') ||
          t.title.includes('検証')
      );

      if (allTasks.length > 2 && !hasTestTask) {
        suggestions.push('テスト作成タスクの追加を検討してください');
      }

      // Check 5: Blocked tasks without reason
      const blockedWithoutReason = allTasks.filter(
        (t) => t.status === 'blocked' && !t.blockedReason
      );

      for (const task of blockedWithoutReason) {
        issues.push({
          type: 'requirement-mismatch',
          taskId: task.id,
          description: `ブロックされたタスク「${task.title}」に理由が記載されていません`,
          suggestion: 'ブロックの理由を記載してください',
          severity: 'error',
        });
      }

      // Generate suggestions based on progress
      const completionRate = completedTasks.length / Math.max(allTasks.length, 1);
      if (completionRate > 0.8 && allTasks.some((t) => t.status !== 'completed')) {
        suggestions.push('もう少しで完了です！残りのタスクを確認してください');
      }

      if (inProgressTasks.length > 3) {
        suggestions.push('進行中のタスクが多すぎます。一度に1-2個に絞ることを推奨します');
      }

      return {
        isValid: issues.filter((i) => i.severity === 'error').length === 0,
        issues,
        suggestions,
      };
    },

    reorderTasks(taskIds: string[]): void {
      const newOrder = new Map<string, number>();
      taskIds.forEach((id, index) => newOrder.set(id, index));

      for (const [id, task] of tasks) {
        const order = newOrder.get(id);
        if (order !== undefined) {
          tasks.set(id, { ...task, order, updatedAt: new Date() });
        }
      }
    },

    exportToSession(): Pick<SessionData, 'completedTasks' | 'inProgressTasks' | 'blockedTasks'> {
      const allTasks = this.getAllTasks();
      return {
        completedTasks: allTasks.filter((t) => t.status === 'completed'),
        inProgressTasks: allTasks.filter((t) => t.status === 'in-progress' || t.status === 'not-started'),
        blockedTasks: allTasks.filter((t) => t.status === 'blocked'),
      };
    },

    importFromSession(
      session: Pick<SessionData, 'completedTasks' | 'inProgressTasks' | 'blockedTasks'>
    ): void {
      this.clear();

      const allTasks = [
        ...session.completedTasks,
        ...session.inProgressTasks,
        ...session.blockedTasks,
      ];

      for (const task of allTasks) {
        tasks.set(task.id, task);
      }
    },

    clear(): void {
      tasks.clear();
    },
  };
}

/**
 * Format task list for display
 *
 * @param integration - TodoWrite integration
 * @returns Formatted task list string
 */
export function formatTaskList(integration: TodoWriteIntegration): string {
  const allTasks = integration.getAllTasks();
  const lines: string[] = [];

  lines.push('## タスクリスト');
  lines.push('');

  const completed = allTasks.filter((t) => t.status === 'completed');
  const inProgress = allTasks.filter((t) => t.status === 'in-progress');
  const notStarted = allTasks.filter((t) => t.status === 'not-started');
  const blocked = allTasks.filter((t) => t.status === 'blocked');

  if (completed.length > 0) {
    lines.push('### 完了');
    for (const task of completed) {
      lines.push(`- [x] ${task.title}`);
    }
    lines.push('');
  }

  if (inProgress.length > 0) {
    lines.push('### 進行中');
    for (const task of inProgress) {
      lines.push(`- [ ] 🔄 ${task.title}`);
    }
    lines.push('');
  }

  if (notStarted.length > 0) {
    lines.push('### 未開始');
    for (const task of notStarted) {
      lines.push(`- [ ] ${task.title}`);
    }
    lines.push('');
  }

  if (blocked.length > 0) {
    lines.push('### ブロック中');
    for (const task of blocked) {
      lines.push(`- [ ] 🚫 ${task.title} (理由: ${task.blockedReason || '不明'})`);
    }
    lines.push('');
  }

  // Add progress summary
  const total = allTasks.length;
  const completedCount = completed.length;
  const progress = total > 0 ? Math.round((completedCount / total) * 100) : 0;
  lines.push(`**進捗**: ${completedCount}/${total} (${progress}%)`);

  return lines.join('\n');
}

/**
 * Format quality check result for display
 *
 * @param result - Quality check result
 * @returns Formatted result string
 */
export function formatQualityCheckResult(result: TaskQualityCheckResult): string {
  const lines: string[] = [];

  lines.push('## タスク品質チェック');
  lines.push('');

  if (result.isValid) {
    lines.push('✅ **品質チェック合格**');
  } else {
    lines.push('❌ **品質チェック不合格**');
  }
  lines.push('');

  if (result.issues.length > 0) {
    lines.push('### 問題点');
    for (const issue of result.issues) {
      const icon = issue.severity === 'error' ? '❌' : '⚠️';
      lines.push(`${icon} **${issue.type}**: ${issue.description}`);
      lines.push(`   💡 ${issue.suggestion}`);
    }
    lines.push('');
  }

  if (result.suggestions.length > 0) {
    lines.push('### 提案');
    for (const suggestion of result.suggestions) {
      lines.push(`- 💡 ${suggestion}`);
    }
  }

  return lines.join('\n');
}
