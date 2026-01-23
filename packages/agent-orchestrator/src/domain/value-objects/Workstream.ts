/**
 * Workstream Types
 *
 * @description
 * ワークストリーム管理の型定義
 *
 * @see TSK-FR-043 - Workstream型定義
 * @see REQ-FR-041〜045 - WorkstreamManager
 * @trace DES-MUSUBIX-FR-001 DES-ORCH-001
 */

/**
 * ワークストリームのステータス
 */
export type WorkstreamStatus =
  | 'pending'     // 待機中
  | 'running'     // 実行中
  | 'paused'      // 一時停止
  | 'completed'   // 完了
  | 'failed'      // 失敗
  | 'cancelled';  // キャンセル

/**
 * ワークストリーム内タスクのステータス
 */
export type WorkstreamTaskStatus =
  | 'queued'      // キュー待ち
  | 'assigned'    // 割り当て済み
  | 'running'     // 実行中
  | 'completed'   // 完了
  | 'failed'      // 失敗
  | 'skipped';    // スキップ

/**
 * ワークストリーム内のタスク
 */
export interface WorkstreamTask {
  readonly id: string;
  readonly name: string;
  readonly status: WorkstreamTaskStatus;
  readonly priority: number;
  readonly dependencies: readonly string[];
  readonly assignedTo?: string;
  readonly startedAt?: number;
  readonly completedAt?: number;
  readonly result?: unknown;
  readonly error?: string;
  readonly metadata?: Readonly<Record<string, unknown>>;
}

/**
 * ワークストリーム内タスクの入力
 */
export interface WorkstreamTaskInput {
  readonly name: string;
  readonly priority?: number;
  readonly dependencies?: readonly string[];
  readonly metadata?: Record<string, unknown>;
}

/**
 * ワークストリーム
 */
export interface Workstream {
  readonly id: string;
  readonly name: string;
  readonly status: WorkstreamStatus;
  readonly tasks: readonly WorkstreamTask[];
  readonly maxParallel: number;
  readonly createdAt: number;
  readonly updatedAt: number;
  readonly startedAt?: number;
  readonly completedAt?: number;
  readonly metadata?: Readonly<Record<string, unknown>>;
}

/**
 * ワークストリーム作成入力
 */
export interface WorkstreamInput {
  readonly name: string;
  readonly maxParallel?: number;
  readonly tasks?: readonly WorkstreamTaskInput[];
  readonly metadata?: Record<string, unknown>;
}

/**
 * ワークストリーム統計
 */
export interface WorkstreamStats {
  readonly totalTasks: number;
  readonly byStatus: Readonly<Record<WorkstreamTaskStatus, number>>;
  readonly completionRate: number;
  readonly avgTaskDuration: number;
  readonly parallelUtilization: number;
}

/**
 * ワークストリーム設定
 */
export interface WorkstreamConfig {
  readonly maxWorkstreams: number;
  readonly defaultMaxParallel: number;
  readonly taskTimeout: number;
  readonly enableAutoRetry: boolean;
  readonly maxRetries: number;
}

/**
 * デフォルト設定
 */
export const DEFAULT_WORKSTREAM_CONFIG: WorkstreamConfig = Object.freeze({
  maxWorkstreams: 10,
  defaultMaxParallel: 4,
  taskTimeout: 300000, // 5分
  enableAutoRetry: true,
  maxRetries: 3,
});

// IDカウンター
let workstreamIdCounter = 0;
let taskIdCounter = 0;

/**
 * IDカウンターをリセット（テスト用）
 */
export function resetWorkstreamCounters(): void {
  workstreamIdCounter = 0;
  taskIdCounter = 0;
}

/**
 * WorkstreamTaskを作成
 */
export function createWorkstreamTask(input: WorkstreamTaskInput): WorkstreamTask {
  taskIdCounter++;
  const id = `WST-${String(taskIdCounter).padStart(5, '0')}`;

  return Object.freeze({
    id,
    name: input.name,
    status: 'queued' as WorkstreamTaskStatus,
    priority: input.priority ?? 0,
    dependencies: Object.freeze(input.dependencies ?? []),
    metadata: input.metadata ? Object.freeze(input.metadata) : undefined,
  });
}

/**
 * Workstreamを作成
 */
export function createWorkstream(input: WorkstreamInput, config: WorkstreamConfig = DEFAULT_WORKSTREAM_CONFIG): Workstream {
  workstreamIdCounter++;
  const id = `WS-${String(workstreamIdCounter).padStart(5, '0')}`;
  const now = Date.now();

  const tasks = (input.tasks ?? []).map(t => createWorkstreamTask(t));

  return Object.freeze({
    id,
    name: input.name,
    status: 'pending' as WorkstreamStatus,
    tasks: Object.freeze(tasks),
    maxParallel: input.maxParallel ?? config.defaultMaxParallel,
    createdAt: now,
    updatedAt: now,
    metadata: input.metadata ? Object.freeze(input.metadata) : undefined,
  });
}

/**
 * ワークストリーム統計を計算
 */
export function calculateWorkstreamStats(workstream: Workstream): WorkstreamStats {
  const byStatus: Record<WorkstreamTaskStatus, number> = {
    queued: 0,
    assigned: 0,
    running: 0,
    completed: 0,
    failed: 0,
    skipped: 0,
  };

  let totalDuration = 0;
  let completedCount = 0;

  for (const task of workstream.tasks) {
    byStatus[task.status]++;
    if (task.status === 'completed' && task.startedAt && task.completedAt) {
      totalDuration += task.completedAt - task.startedAt;
      completedCount++;
    }
  }

  const totalTasks = workstream.tasks.length;
  const completionRate = totalTasks > 0 ? (byStatus.completed / totalTasks) : 0;
  const avgTaskDuration = completedCount > 0 ? totalDuration / completedCount : 0;

  // 並列利用率: 実行中タスク数 / maxParallel
  const runningCount = byStatus.running + byStatus.assigned;
  const parallelUtilization = workstream.maxParallel > 0 
    ? Math.min(1, runningCount / workstream.maxParallel) 
    : 0;

  return Object.freeze({
    totalTasks,
    byStatus: Object.freeze(byStatus),
    completionRate,
    avgTaskDuration,
    parallelUtilization,
  });
}
