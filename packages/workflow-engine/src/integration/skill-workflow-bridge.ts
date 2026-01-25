/**
 * Skill-Workflow Bridge Implementation
 *
 * REQ-INT-001: SkillWorkflowBridge - workflow-engine と skill-manager の橋渡し
 *
 * @packageDocumentation
 */

import type { PhaseType } from '../domain/value-objects/PhaseType.js';
import { VALID_TRANSITIONS } from '../domain/value-objects/PhaseType.js';

import {
  type ActionContext,
  PHASE_SKILL_ACTIONS,
  type PhaseChangeEvent,
  type PhaseSkillAction,
  type PhaseTransitionRecommendation,
  type SkillActionResult,
  type SkillActionType,
  type SkillWorkflowBridge,
  type TransitionContext,
} from './types.js';

/**
 * スキルアクションを実行（スタブ実装）
 * 実際の実装では skill-manager と連携
 */
async function executeSkillAction(
  action: SkillActionType,
  context?: ActionContext
): Promise<SkillActionResult> {
  // 各アクションの基本的な処理
  switch (action) {
    case 'session_start':
      return {
        action,
        success: true,
        data: {
          sessionId: context?.sessionId ?? `session-${Date.now()}`,
          startedAt: new Date().toISOString(),
        },
      };

    case 'session_end':
      return {
        action,
        success: true,
        data: {
          sessionId: context?.sessionId,
          endedAt: new Date().toISOString(),
        },
      };

    case 'pre_compact':
      return {
        action,
        success: true,
        data: {
          snapshotId: `snapshot-${Date.now()}`,
          phase: context?.phase,
        },
      };

    case 'context_check':
      return {
        action,
        success: true,
        data: {
          contextMode: context?.phase
            ? PHASE_SKILL_ACTIONS.get(context.phase)?.contextMode
            : 'dev',
        },
      };

    case 'tool_counter_update':
      return {
        action,
        success: true,
        data: { updated: true },
      };

    case 'learning_evaluate':
      return {
        action,
        success: true,
        data: { evaluated: true },
      };

    case 'pattern_extract':
      return {
        action,
        success: true,
        data: { patternsExtracted: 0 },
      };

    case 'phase_recommendation':
      return {
        action,
        success: true,
        data: { recommended: true },
      };

    default:
      return {
        action,
        success: false,
        error: `Unknown action: ${action}`,
      };
  }
}

/**
 * 次の有効なフェーズを取得
 */
function getNextValidPhase(currentPhase: PhaseType): PhaseType | null {
  const validNext = VALID_TRANSITIONS.get(currentPhase);
  if (!validNext || validNext.length === 0) {
    return null;
  }
  return validNext[0];
}

/**
 * 遷移可能かチェック
 */
function canTransitionToNext(
  currentPhase: PhaseType,
  context?: TransitionContext
): { canTransition: boolean; prerequisites?: string[] } {
  // 完了フェーズからは遷移不可
  if (currentPhase === 'completion') {
    return { canTransition: false, prerequisites: ['ワークフロー完了済み'] };
  }

  const prerequisites: string[] = [];

  // 成果物チェック
  if (context?.hasArtifacts === false) {
    prerequisites.push('成果物の作成が必要です');
  }

  // 承認チェック
  if (context?.isApproved === false) {
    prerequisites.push('ユーザー承認が必要です');
  }

  // 品質ゲートチェック
  if (context?.qualityGatePassed === false) {
    prerequisites.push('品質ゲートの通過が必要です');
  }

  return {
    canTransition: prerequisites.length === 0,
    prerequisites: prerequisites.length > 0 ? prerequisites : undefined,
  };
}

/**
 * フェーズに対応する推奨理由を生成
 */
function generateTransitionReason(
  currentPhase: PhaseType,
  nextPhase: PhaseType | null,
  canTransition: boolean
): string {
  if (!nextPhase) {
    return 'ワークフローが完了しています';
  }

  if (!canTransition) {
    return `${currentPhase}フェーズの条件を満たしてから${nextPhase}フェーズに進んでください`;
  }

  const phaseReasons: Record<PhaseType, string> = {
    requirements: '要件定義が完了したら設計フェーズに進みます',
    design: '設計が完了したらタスク分解フェーズに進みます',
    'task-breakdown': 'タスク分解が完了したら実装フェーズに進みます',
    implementation: '実装が完了したら完了フェーズに進みます',
    completion: 'ワークフローが完了しています',
  };

  return phaseReasons[currentPhase];
}

/**
 * SkillWorkflowBridge を作成
 *
 * REQ-INT-001: workflow-engine と skill-manager の橋渡し
 */
export function createSkillWorkflowBridge(): SkillWorkflowBridge {
  return {
    async onPhaseChange(event: PhaseChangeEvent): Promise<SkillActionResult[]> {
      const results: SkillActionResult[] = [];

      // 前のフェーズの onExit アクションを実行
      if (event.fromPhase) {
        const fromActions = PHASE_SKILL_ACTIONS.get(event.fromPhase);
        if (fromActions) {
          for (const action of fromActions.onExit) {
            const result = await executeSkillAction(action, {
              workflowId: event.workflowId,
              phase: event.fromPhase,
            });
            results.push(result);
          }
        }
      }

      // 新しいフェーズの onEnter アクションを実行
      const toActions = PHASE_SKILL_ACTIONS.get(event.toPhase);
      if (toActions) {
        for (const action of toActions.onEnter) {
          const result = await executeSkillAction(action, {
            workflowId: event.workflowId,
            phase: event.toPhase,
          });
          results.push(result);
        }
      }

      return results;
    },

    getRecommendedTransition(
      currentPhase: PhaseType,
      context?: TransitionContext
    ): PhaseTransitionRecommendation {
      const nextPhase = getNextValidPhase(currentPhase);
      const { canTransition, prerequisites } = canTransitionToNext(
        currentPhase,
        context
      );

      return {
        currentPhase,
        recommendedPhase: nextPhase,
        reason: generateTransitionReason(currentPhase, nextPhase, canTransition),
        canTransition: canTransition && nextPhase !== null,
        prerequisites,
      };
    },

    getPhaseSkillActions(phase: PhaseType): PhaseSkillAction | undefined {
      return PHASE_SKILL_ACTIONS.get(phase);
    },

    async executeAction(
      action: SkillActionType,
      context?: ActionContext
    ): Promise<SkillActionResult> {
      return executeSkillAction(action, context);
    },
  };
}

/**
 * フェーズ変更イベントを作成するヘルパー
 */
export function createPhaseChangeEvent(
  workflowId: string,
  fromPhase: PhaseType | null,
  toPhase: PhaseType,
  approvedBy?: string
): PhaseChangeEvent {
  return {
    fromPhase,
    toPhase,
    timestamp: new Date(),
    workflowId,
    approvedBy,
  };
}

/**
 * すべてのフェーズスキルアクションを取得
 */
export function getAllPhaseSkillActions(): ReadonlyMap<
  PhaseType,
  PhaseSkillAction
> {
  return PHASE_SKILL_ACTIONS;
}
