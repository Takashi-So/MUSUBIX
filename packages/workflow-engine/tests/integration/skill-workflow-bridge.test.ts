/**
 * Skill-Workflow Bridge Tests
 *
 * REQ-INT-001: SkillWorkflowBridge
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createSkillWorkflowBridge,
  createPhaseChangeEvent,
  getAllPhaseSkillActions,
  type SkillWorkflowBridge,
  type PhaseChangeEvent,
  PHASE_SKILL_ACTIONS,
} from '../../src/integration/index.js';
import type { PhaseType } from '../../src/domain/value-objects/PhaseType.js';

describe('SkillWorkflowBridge', () => {
  let bridge: SkillWorkflowBridge;

  beforeEach(() => {
    bridge = createSkillWorkflowBridge();
  });

  describe('onPhaseChange', () => {
    it('should execute onEnter actions for new phase', async () => {
      const event: PhaseChangeEvent = createPhaseChangeEvent(
        'workflow-001',
        null,
        'requirements'
      );

      const results = await bridge.onPhaseChange(event);

      expect(results.length).toBeGreaterThan(0);
      expect(results.every((r) => r.success)).toBe(true);
    });

    it('should execute onExit actions for previous phase and onEnter for new phase', async () => {
      const event: PhaseChangeEvent = createPhaseChangeEvent(
        'workflow-001',
        'requirements',
        'design'
      );

      const results = await bridge.onPhaseChange(event);

      // requirements の onExit + design の onEnter
      expect(results.length).toBeGreaterThan(1);
      expect(results.every((r) => r.success)).toBe(true);
    });

    it('should execute session_start action for requirements phase', async () => {
      const event: PhaseChangeEvent = createPhaseChangeEvent(
        'workflow-001',
        null,
        'requirements'
      );

      const results = await bridge.onPhaseChange(event);

      const sessionStartResult = results.find(
        (r) => r.action === 'session_start'
      );
      expect(sessionStartResult).toBeDefined();
      expect(sessionStartResult?.success).toBe(true);
      expect(sessionStartResult?.data?.sessionId).toBeDefined();
    });

    it('should execute session_end action when exiting completion phase', async () => {
      // completion フェーズの onExit には session_end が含まれる
      const event: PhaseChangeEvent = createPhaseChangeEvent(
        'workflow-001',
        'completion',
        'requirements' // 通常はありえない遷移だがテスト用
      );

      const results = await bridge.onPhaseChange(event);

      const sessionEndResult = results.find((r) => r.action === 'session_end');
      expect(sessionEndResult).toBeDefined();
      expect(sessionEndResult?.success).toBe(true);
    });

    it('should execute learning_evaluate for completion phase entry', async () => {
      const event: PhaseChangeEvent = createPhaseChangeEvent(
        'workflow-001',
        'implementation',
        'completion'
      );

      const results = await bridge.onPhaseChange(event);

      const learningResult = results.find(
        (r) => r.action === 'learning_evaluate'
      );
      expect(learningResult).toBeDefined();
      expect(learningResult?.success).toBe(true);
    });
  });

  describe('getRecommendedTransition', () => {
    it('should recommend design phase after requirements', () => {
      const recommendation = bridge.getRecommendedTransition('requirements');

      expect(recommendation.currentPhase).toBe('requirements');
      expect(recommendation.recommendedPhase).toBe('design');
      expect(recommendation.canTransition).toBe(true);
    });

    it('should recommend task-breakdown after design (NOT implementation)', () => {
      const recommendation = bridge.getRecommendedTransition('design');

      expect(recommendation.currentPhase).toBe('design');
      expect(recommendation.recommendedPhase).toBe('task-breakdown');
      expect(recommendation.recommendedPhase).not.toBe('implementation');
      expect(recommendation.canTransition).toBe(true);
    });

    it('should recommend implementation after task-breakdown', () => {
      const recommendation = bridge.getRecommendedTransition('task-breakdown');

      expect(recommendation.currentPhase).toBe('task-breakdown');
      expect(recommendation.recommendedPhase).toBe('implementation');
      expect(recommendation.canTransition).toBe(true);
    });

    it('should recommend completion after implementation', () => {
      const recommendation = bridge.getRecommendedTransition('implementation');

      expect(recommendation.currentPhase).toBe('implementation');
      expect(recommendation.recommendedPhase).toBe('completion');
      expect(recommendation.canTransition).toBe(true);
    });

    it('should return null for completion phase', () => {
      const recommendation = bridge.getRecommendedTransition('completion');

      expect(recommendation.currentPhase).toBe('completion');
      expect(recommendation.recommendedPhase).toBe(null);
      expect(recommendation.canTransition).toBe(false);
    });

    it('should indicate prerequisites when artifacts missing', () => {
      const recommendation = bridge.getRecommendedTransition('requirements', {
        hasArtifacts: false,
      });

      expect(recommendation.canTransition).toBe(false);
      expect(recommendation.prerequisites).toContain(
        '成果物の作成が必要です'
      );
    });

    it('should indicate prerequisites when not approved', () => {
      const recommendation = bridge.getRecommendedTransition('design', {
        isApproved: false,
      });

      expect(recommendation.canTransition).toBe(false);
      expect(recommendation.prerequisites).toContain(
        'ユーザー承認が必要です'
      );
    });

    it('should indicate prerequisites when quality gate not passed', () => {
      const recommendation = bridge.getRecommendedTransition('task-breakdown', {
        qualityGatePassed: false,
      });

      expect(recommendation.canTransition).toBe(false);
      expect(recommendation.prerequisites).toContain(
        '品質ゲートの通過が必要です'
      );
    });

    it('should allow transition when all conditions met', () => {
      const recommendation = bridge.getRecommendedTransition('requirements', {
        hasArtifacts: true,
        isApproved: true,
        qualityGatePassed: true,
      });

      expect(recommendation.canTransition).toBe(true);
      expect(recommendation.prerequisites).toBeUndefined();
    });
  });

  describe('getPhaseSkillActions', () => {
    it('should return skill actions for requirements phase', () => {
      const actions = bridge.getPhaseSkillActions('requirements');

      expect(actions).toBeDefined();
      expect(actions?.phase).toBe('requirements');
      expect(actions?.contextMode).toBe('research');
      expect(actions?.onEnter).toContain('session_start');
    });

    it('should return skill actions for design phase', () => {
      const actions = bridge.getPhaseSkillActions('design');

      expect(actions).toBeDefined();
      expect(actions?.phase).toBe('design');
      expect(actions?.contextMode).toBe('dev');
    });

    it('should return skill actions for implementation phase', () => {
      const actions = bridge.getPhaseSkillActions('implementation');

      expect(actions).toBeDefined();
      expect(actions?.phase).toBe('implementation');
      expect(actions?.contextMode).toBe('dev');
      expect(actions?.onExit).toContain('learning_evaluate');
      expect(actions?.onExit).toContain('pattern_extract');
    });

    it('should return skill actions for completion phase', () => {
      const actions = bridge.getPhaseSkillActions('completion');

      expect(actions).toBeDefined();
      expect(actions?.phase).toBe('completion');
      expect(actions?.contextMode).toBe('review');
      expect(actions?.onExit).toContain('session_end');
    });

    it('should return undefined for unknown phase', () => {
      const actions = bridge.getPhaseSkillActions(
        'unknown-phase' as PhaseType
      );
      expect(actions).toBeUndefined();
    });
  });

  describe('executeAction', () => {
    it('should execute session_start action', async () => {
      const result = await bridge.executeAction('session_start');

      expect(result.action).toBe('session_start');
      expect(result.success).toBe(true);
      expect(result.data?.sessionId).toBeDefined();
      expect(result.data?.startedAt).toBeDefined();
    });

    it('should execute session_end action', async () => {
      const result = await bridge.executeAction('session_end', {
        sessionId: 'test-session-001',
      });

      expect(result.action).toBe('session_end');
      expect(result.success).toBe(true);
      expect(result.data?.endedAt).toBeDefined();
    });

    it('should execute pre_compact action', async () => {
      const result = await bridge.executeAction('pre_compact', {
        phase: 'design',
      });

      expect(result.action).toBe('pre_compact');
      expect(result.success).toBe(true);
      expect(result.data?.snapshotId).toBeDefined();
      expect(result.data?.phase).toBe('design');
    });

    it('should execute context_check action', async () => {
      const result = await bridge.executeAction('context_check', {
        phase: 'requirements',
      });

      expect(result.action).toBe('context_check');
      expect(result.success).toBe(true);
      expect(result.data?.contextMode).toBe('research');
    });

    it('should execute tool_counter_update action', async () => {
      const result = await bridge.executeAction('tool_counter_update');

      expect(result.action).toBe('tool_counter_update');
      expect(result.success).toBe(true);
      expect(result.data?.updated).toBe(true);
    });

    it('should execute learning_evaluate action', async () => {
      const result = await bridge.executeAction('learning_evaluate');

      expect(result.action).toBe('learning_evaluate');
      expect(result.success).toBe(true);
      expect(result.data?.evaluated).toBe(true);
    });

    it('should execute pattern_extract action', async () => {
      const result = await bridge.executeAction('pattern_extract');

      expect(result.action).toBe('pattern_extract');
      expect(result.success).toBe(true);
      expect(result.data?.patternsExtracted).toBeDefined();
    });

    it('should execute phase_recommendation action', async () => {
      const result = await bridge.executeAction('phase_recommendation');

      expect(result.action).toBe('phase_recommendation');
      expect(result.success).toBe(true);
    });

    it('should return error for unknown action', async () => {
      const result = await bridge.executeAction('unknown' as any);

      expect(result.success).toBe(false);
      expect(result.error).toContain('Unknown action');
    });
  });
});

describe('createPhaseChangeEvent', () => {
  it('should create event with all properties', () => {
    const event = createPhaseChangeEvent(
      'workflow-001',
      'requirements',
      'design',
      'user@example.com'
    );

    expect(event.workflowId).toBe('workflow-001');
    expect(event.fromPhase).toBe('requirements');
    expect(event.toPhase).toBe('design');
    expect(event.approvedBy).toBe('user@example.com');
    expect(event.timestamp).toBeInstanceOf(Date);
  });

  it('should create event with null fromPhase', () => {
    const event = createPhaseChangeEvent('workflow-002', null, 'requirements');

    expect(event.fromPhase).toBeNull();
    expect(event.toPhase).toBe('requirements');
    expect(event.approvedBy).toBeUndefined();
  });
});

describe('getAllPhaseSkillActions', () => {
  it('should return all phase skill actions', () => {
    const actions = getAllPhaseSkillActions();

    expect(actions.size).toBe(5);
    expect(actions.has('requirements')).toBe(true);
    expect(actions.has('design')).toBe(true);
    expect(actions.has('task-breakdown')).toBe(true);
    expect(actions.has('implementation')).toBe(true);
    expect(actions.has('completion')).toBe(true);
  });

  it('should match PHASE_SKILL_ACTIONS constant', () => {
    const actions = getAllPhaseSkillActions();
    expect(actions).toBe(PHASE_SKILL_ACTIONS);
  });
});

describe('Phase Transition Enforcement (Article X)', () => {
  let bridge: SkillWorkflowBridge;

  beforeEach(() => {
    bridge = createSkillWorkflowBridge();
  });

  it('should NOT allow direct transition from design to implementation', () => {
    // 設計フェーズから実装フェーズへの直接遷移は禁止
    const recommendation = bridge.getRecommendedTransition('design');

    expect(recommendation.recommendedPhase).toBe('task-breakdown');
    expect(recommendation.recommendedPhase).not.toBe('implementation');
  });

  it('should enforce task-breakdown phase between design and implementation', () => {
    // 正しいフロー: design → task-breakdown → implementation
    const fromDesign = bridge.getRecommendedTransition('design');
    expect(fromDesign.recommendedPhase).toBe('task-breakdown');

    const fromTaskBreakdown = bridge.getRecommendedTransition('task-breakdown');
    expect(fromTaskBreakdown.recommendedPhase).toBe('implementation');
  });

  it('should follow correct phase order for all transitions', () => {
    const phases: PhaseType[] = [
      'requirements',
      'design',
      'task-breakdown',
      'implementation',
      'completion',
    ];

    for (let i = 0; i < phases.length - 1; i++) {
      const recommendation = bridge.getRecommendedTransition(phases[i]);
      expect(recommendation.recommendedPhase).toBe(phases[i + 1]);
    }
  });
});
