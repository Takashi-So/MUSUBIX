/**
 * WorkstreamManager - ワークストリーム管理
 *
 * @description
 * 並列タスク実行のためのワークストリームを管理する。
 * DURING_PHASE層でParallelExecutorと連携し、タスクの分散実行を制御。
 *
 * @see DES-ORCH-001 - ワークストリーム管理システム
 * @see TSK-FR-043 - WorkstreamManagerインターフェース定義
 * @see TSK-FR-044 - create/get/addTask実装
 * @see TSK-FR-045 - start/assignTask/completeTask実装
 * @see TSK-FR-046 - ParallelExecutor統合
 * @trace REQ-FR-005 - 並列タスク実行
 */

import type {
  Workstream,
  WorkstreamTask,
  WorkstreamInput,
  WorkstreamTaskInput,
  WorkstreamStatus,
  WorkstreamTaskStatus,
  WorkstreamStats,
  WorkstreamConfig,
} from '../value-objects/Workstream.js';

import {
  createWorkstream,
  createWorkstreamTask,
  calculateWorkstreamStats,
  DEFAULT_WORKSTREAM_CONFIG,
} from '../value-objects/Workstream.js';

/**
 * WorkstreamManagerインターフェース
 *
 * @trace DES-ORCH-001
 */
export interface IWorkstreamManager {
  /**
   * ワークストリームを作成
   */
  create(input: WorkstreamInput): Promise<Workstream>;

  /**
   * IDでワークストリームを取得
   */
  get(id: string): Promise<Workstream | null>;

  /**
   * タスクを追加
   */
  addTask(workstreamId: string, task: WorkstreamTaskInput): Promise<Workstream | null>;

  /**
   * ワークストリームを開始
   */
  start(id: string): Promise<Workstream | null>;

  /**
   * タスクをエージェントに割り当て
   */
  assignTask(workstreamId: string, taskId: string, agentId: string): Promise<WorkstreamTask | null>;

  /**
   * タスクを完了
   */
  completeTask(workstreamId: string, taskId: string, result: unknown): Promise<WorkstreamTask | null>;

  /**
   * タスクを失敗
   */
  failTask(workstreamId: string, taskId: string, error: string): Promise<WorkstreamTask | null>;

  /**
   * 次に実行可能なタスクを取得
   */
  getNextTasks(workstreamId: string): Promise<readonly WorkstreamTask[]>;

  /**
   * 統計を取得
   */
  getStats(workstreamId: string): Promise<WorkstreamStats | null>;

  /**
   * 全ワークストリームを取得
   */
  list(): Promise<readonly Workstream[]>;

  /**
   * ワークストリームをキャンセル
   */
  cancel(id: string): Promise<Workstream | null>;
}

/**
 * WorkstreamManager実装
 *
 * @trace DES-ORCH-001
 */
export class WorkstreamManager implements IWorkstreamManager {
  private readonly workstreams: Map<string, Workstream> = new Map();
  private readonly config: WorkstreamConfig;

  constructor(config: WorkstreamConfig = DEFAULT_WORKSTREAM_CONFIG) {
    this.config = config;
  }

  /**
   * @trace TSK-FR-044
   */
  async create(input: WorkstreamInput): Promise<Workstream> {
    if (this.workstreams.size >= this.config.maxWorkstreams) {
      throw new Error(`Maximum workstreams limit reached (${this.config.maxWorkstreams})`);
    }

    const workstream = createWorkstream(input, this.config);
    this.workstreams.set(workstream.id, workstream);
    return workstream;
  }

  async get(id: string): Promise<Workstream | null> {
    return this.workstreams.get(id) ?? null;
  }

  /**
   * @trace TSK-FR-044
   */
  async addTask(workstreamId: string, taskInput: WorkstreamTaskInput): Promise<Workstream | null> {
    const ws = this.workstreams.get(workstreamId);
    if (!ws) {
      return null;
    }

    const task = createWorkstreamTask(taskInput);
    const updated: Workstream = Object.freeze({
      ...ws,
      tasks: Object.freeze([...ws.tasks, task]),
      updatedAt: Date.now(),
    });

    this.workstreams.set(workstreamId, updated);
    return updated;
  }

  /**
   * @trace TSK-FR-045
   */
  async start(id: string): Promise<Workstream | null> {
    const ws = this.workstreams.get(id);
    if (!ws) {
      return null;
    }

    if (ws.tasks.length === 0) {
      throw new Error('Cannot start workstream with no tasks');
    }

    const now = Date.now();
    const updated: Workstream = Object.freeze({
      ...ws,
      status: 'running' as WorkstreamStatus,
      startedAt: now,
      updatedAt: now,
    });

    this.workstreams.set(id, updated);
    return updated;
  }

  /**
   * @trace TSK-FR-045
   */
  async assignTask(workstreamId: string, taskId: string, agentId: string): Promise<WorkstreamTask | null> {
    const ws = this.workstreams.get(workstreamId);
    if (!ws) {
      return null;
    }

    const taskIndex = ws.tasks.findIndex(t => t.id === taskId);
    if (taskIndex === -1) {
      return null;
    }

    const now = Date.now();
    const task = ws.tasks[taskIndex];
    const updatedTask: WorkstreamTask = Object.freeze({
      ...task,
      status: 'assigned' as WorkstreamTaskStatus,
      assignedTo: agentId,
      startedAt: now,
    });

    const updatedTasks = [...ws.tasks];
    updatedTasks[taskIndex] = updatedTask;

    const updated: Workstream = Object.freeze({
      ...ws,
      tasks: Object.freeze(updatedTasks),
      updatedAt: now,
    });

    this.workstreams.set(workstreamId, updated);
    return updatedTask;
  }

  /**
   * @trace TSK-FR-045
   */
  async completeTask(workstreamId: string, taskId: string, result: unknown): Promise<WorkstreamTask | null> {
    const ws = this.workstreams.get(workstreamId);
    if (!ws) {
      return null;
    }

    const taskIndex = ws.tasks.findIndex(t => t.id === taskId);
    if (taskIndex === -1) {
      return null;
    }

    const now = Date.now();
    const task = ws.tasks[taskIndex];
    const updatedTask: WorkstreamTask = Object.freeze({
      ...task,
      status: 'completed' as WorkstreamTaskStatus,
      completedAt: now,
      result,
    });

    const updatedTasks = [...ws.tasks];
    updatedTasks[taskIndex] = updatedTask;

    // 全タスク完了確認
    const allCompleted = updatedTasks.every(
      t => t.status === 'completed' || t.status === 'failed' || t.status === 'skipped'
    );

    const updated: Workstream = Object.freeze({
      ...ws,
      tasks: Object.freeze(updatedTasks),
      status: allCompleted ? 'completed' as WorkstreamStatus : ws.status,
      completedAt: allCompleted ? now : ws.completedAt,
      updatedAt: now,
    });

    this.workstreams.set(workstreamId, updated);
    return updatedTask;
  }

  async failTask(workstreamId: string, taskId: string, error: string): Promise<WorkstreamTask | null> {
    const ws = this.workstreams.get(workstreamId);
    if (!ws) {
      return null;
    }

    const taskIndex = ws.tasks.findIndex(t => t.id === taskId);
    if (taskIndex === -1) {
      return null;
    }

    const now = Date.now();
    const task = ws.tasks[taskIndex];
    const updatedTask: WorkstreamTask = Object.freeze({
      ...task,
      status: 'failed' as WorkstreamTaskStatus,
      completedAt: now,
      error,
    });

    const updatedTasks = [...ws.tasks];
    updatedTasks[taskIndex] = updatedTask;

    const updated: Workstream = Object.freeze({
      ...ws,
      tasks: Object.freeze(updatedTasks),
      updatedAt: now,
    });

    this.workstreams.set(workstreamId, updated);
    return updatedTask;
  }

  /**
   * @trace TSK-FR-046
   */
  async getNextTasks(workstreamId: string): Promise<readonly WorkstreamTask[]> {
    const ws = this.workstreams.get(workstreamId);
    if (!ws || ws.status !== 'running') {
      return [];
    }

    // 現在実行中/割り当て済みのタスク数
    const runningCount = ws.tasks.filter(
      t => t.status === 'running' || t.status === 'assigned'
    ).length;

    // 空きスロット数
    const availableSlots = ws.maxParallel - runningCount;
    if (availableSlots <= 0) {
      return [];
    }

    // 完了済みタスクIDセット
    const completedIds = new Set(
      ws.tasks.filter(t => t.status === 'completed').map(t => t.id)
    );

    // 実行可能タスク: queued かつ 依存がすべて完了
    const eligibleTasks = ws.tasks.filter(task => {
      if (task.status !== 'queued') {
        return false;
      }
      // 依存タスクがすべて完了しているか
      return task.dependencies.every(depId => completedIds.has(depId));
    });

    // 優先度順にソートして上位を返す
    const sorted = [...eligibleTasks].sort((a, b) => b.priority - a.priority);

    return Object.freeze(sorted.slice(0, availableSlots));
  }

  async getStats(workstreamId: string): Promise<WorkstreamStats | null> {
    const ws = this.workstreams.get(workstreamId);
    if (!ws) {
      return null;
    }

    return calculateWorkstreamStats(ws);
  }

  async list(): Promise<readonly Workstream[]> {
    return Object.freeze(Array.from(this.workstreams.values()));
  }

  async cancel(id: string): Promise<Workstream | null> {
    const ws = this.workstreams.get(id);
    if (!ws) {
      return null;
    }

    const now = Date.now();
    const updated: Workstream = Object.freeze({
      ...ws,
      status: 'cancelled' as WorkstreamStatus,
      completedAt: now,
      updatedAt: now,
    });

    this.workstreams.set(id, updated);
    return updated;
  }
}

/**
 * ファクトリ関数
 *
 * @trace TSK-FR-043
 */
export function createWorkstreamManager(config?: WorkstreamConfig): IWorkstreamManager {
  return new WorkstreamManager(config);
}
