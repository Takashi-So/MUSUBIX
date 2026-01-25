/**
 * Skill-Workflow Bridge Types
 *
 * REQ-INT-001: SkillWorkflowBridge - workflow-engine と skill-manager の橋渡し
 *
 * @packageDocumentation
 */

import type { PhaseType } from '../domain/value-objects/PhaseType.js';

/**
 * スキルアクション種別
 */
export type SkillActionType =
  | 'session_start'
  | 'session_end'
  | 'pre_compact'
  | 'context_check'
  | 'tool_counter_update'
  | 'learning_evaluate'
  | 'pattern_extract'
  | 'phase_recommendation';

/**
 * フェーズごとのスキルアクション定義
 */
export interface PhaseSkillAction {
  /** フェーズタイプ */
  readonly phase: PhaseType;
  /** 推奨スキルアクション */
  readonly recommendedActions: readonly SkillActionType[];
  /** フェーズ開始時の自動アクション */
  readonly onEnter: readonly SkillActionType[];
  /** フェーズ終了時の自動アクション */
  readonly onExit: readonly SkillActionType[];
  /** コンテキストモード */
  readonly contextMode: 'dev' | 'review' | 'research';
}

/**
 * フェーズごとのスキルアクション定義マップ
 */
export const PHASE_SKILL_ACTIONS: ReadonlyMap<PhaseType, PhaseSkillAction> =
  new Map([
    [
      'requirements',
      {
        phase: 'requirements',
        recommendedActions: [
          'session_start',
          'context_check',
          'phase_recommendation',
        ],
        onEnter: ['session_start', 'context_check'],
        onExit: ['pre_compact'],
        contextMode: 'research',
      },
    ],
    [
      'design',
      {
        phase: 'design',
        recommendedActions: ['context_check', 'phase_recommendation'],
        onEnter: ['context_check'],
        onExit: ['pre_compact'],
        contextMode: 'dev',
      },
    ],
    [
      'task-breakdown',
      {
        phase: 'task-breakdown',
        recommendedActions: ['context_check', 'tool_counter_update'],
        onEnter: ['context_check'],
        onExit: ['pre_compact'],
        contextMode: 'dev',
      },
    ],
    [
      'implementation',
      {
        phase: 'implementation',
        recommendedActions: [
          'context_check',
          'tool_counter_update',
          'pattern_extract',
        ],
        onEnter: ['context_check'],
        onExit: ['learning_evaluate', 'pattern_extract'],
        contextMode: 'dev',
      },
    ],
    [
      'completion',
      {
        phase: 'completion',
        recommendedActions: [
          'session_end',
          'learning_evaluate',
          'pre_compact',
        ],
        onEnter: ['learning_evaluate'],
        onExit: ['session_end', 'pre_compact'],
        contextMode: 'review',
      },
    ],
  ]);

/**
 * フェーズ変更イベント
 */
export interface PhaseChangeEvent {
  /** 前のフェーズ */
  readonly fromPhase: PhaseType | null;
  /** 新しいフェーズ */
  readonly toPhase: PhaseType;
  /** 変更日時 */
  readonly timestamp: Date;
  /** ワークフローID */
  readonly workflowId: string;
  /** 承認者（あれば） */
  readonly approvedBy?: string;
}

/**
 * スキルアクション実行結果
 */
export interface SkillActionResult {
  /** アクション種別 */
  readonly action: SkillActionType;
  /** 成功フラグ */
  readonly success: boolean;
  /** エラーメッセージ（失敗時） */
  readonly error?: string;
  /** 追加データ */
  readonly data?: Record<string, unknown>;
}

/**
 * フェーズ遷移推奨
 */
export interface PhaseTransitionRecommendation {
  /** 現在のフェーズ */
  readonly currentPhase: PhaseType;
  /** 推奨する次のフェーズ */
  readonly recommendedPhase: PhaseType | null;
  /** 推奨理由 */
  readonly reason: string;
  /** 遷移可能か */
  readonly canTransition: boolean;
  /** 遷移に必要な条件（未達成の場合） */
  readonly prerequisites?: string[];
}

/**
 * SkillWorkflowBridge インターフェース
 */
export interface SkillWorkflowBridge {
  /**
   * フェーズ変更時のコールバック
   * @param event フェーズ変更イベント
   * @returns 実行されたスキルアクションの結果
   */
  onPhaseChange(event: PhaseChangeEvent): Promise<SkillActionResult[]>;

  /**
   * 推奨フェーズ遷移を取得
   * @param currentPhase 現在のフェーズ
   * @param context コンテキスト情報
   * @returns フェーズ遷移推奨
   */
  getRecommendedTransition(
    currentPhase: PhaseType,
    context?: TransitionContext
  ): PhaseTransitionRecommendation;

  /**
   * フェーズに対応するスキルアクションを取得
   * @param phase フェーズ
   * @returns スキルアクション定義
   */
  getPhaseSkillActions(phase: PhaseType): PhaseSkillAction | undefined;

  /**
   * 特定のスキルアクションを実行
   * @param action アクション種別
   * @param context 実行コンテキスト
   * @returns アクション結果
   */
  executeAction(
    action: SkillActionType,
    context?: ActionContext
  ): Promise<SkillActionResult>;
}

/**
 * 遷移判断用コンテキスト
 */
export interface TransitionContext {
  /** 成果物が存在するか */
  readonly hasArtifacts?: boolean;
  /** 承認済みか */
  readonly isApproved?: boolean;
  /** 品質ゲート通過済みか */
  readonly qualityGatePassed?: boolean;
  /** カスタムデータ */
  readonly customData?: Record<string, unknown>;
}

/**
 * アクション実行コンテキスト
 */
export interface ActionContext {
  /** ワークフローID */
  readonly workflowId?: string;
  /** セッションID */
  readonly sessionId?: string;
  /** フェーズ */
  readonly phase?: PhaseType;
  /** カスタムデータ */
  readonly data?: Record<string, unknown>;
}
