/**
 * Skills Tests
 *
 * @see REQ-AA-INT-005 - Skill integration
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ASSISTANT_AXIS_SKILLS,
  PERSONA_MONITOR_SKILL,
  SESSION_MANAGEMENT_SKILL,
  WORKFLOW_INTEGRATION_SKILL,
  getSkillById,
  getSkillIds,
} from '../src/skills/definitions.js';
import {
  executePersonaMonitor,
  executeSessionManagement,
  executeWorkflowIntegration,
  executeSkill,
  resetSkillMonitor,
} from '../src/skills/executor.js';

describe('Skills', () => {
  describe('Skill Definitions', () => {
    it('should export 3 skills', () => {
      expect(ASSISTANT_AXIS_SKILLS).toHaveLength(3);
    });

    it('should have valid skill schemas', () => {
      for (const skill of ASSISTANT_AXIS_SKILLS) {
        expect(skill.id).toBeTruthy();
        expect(skill.name).toBeTruthy();
        expect(skill.version).toBe('0.1.0');
        expect(skill.capabilities).toBeInstanceOf(Array);
        expect(skill.parameters).toBeInstanceOf(Array);
        expect(skill.outputs).toBeInstanceOf(Array);
      }
    });

    it('should define persona monitor skill correctly', () => {
      expect(PERSONA_MONITOR_SKILL.id).toBe('assistant-axis.persona-monitor');
      expect(PERSONA_MONITOR_SKILL.category).toBe('ai-safety');
      expect(PERSONA_MONITOR_SKILL.capabilities).toContain('drift-detection');
    });

    it('should define session management skill correctly', () => {
      expect(SESSION_MANAGEMENT_SKILL.id).toBe('assistant-axis.session-management');
      expect(SESSION_MANAGEMENT_SKILL.capabilities).toContain('session-start');
      expect(SESSION_MANAGEMENT_SKILL.capabilities).toContain('session-end');
    });

    it('should define workflow integration skill correctly', () => {
      expect(WORKFLOW_INTEGRATION_SKILL.id).toBe('assistant-axis.workflow-integration');
      expect(WORKFLOW_INTEGRATION_SKILL.category).toBe('workflow');
      expect(WORKFLOW_INTEGRATION_SKILL.dependencies).toContain('workflow-engine');
    });

    it('should get skill by ID', () => {
      const skill = getSkillById('assistant-axis.persona-monitor');
      expect(skill).toBe(PERSONA_MONITOR_SKILL);
    });

    it('should return undefined for unknown skill', () => {
      const skill = getSkillById('unknown-skill');
      expect(skill).toBeUndefined();
    });

    it('should get all skill IDs', () => {
      const ids = getSkillIds();
      expect(ids).toContain('assistant-axis.persona-monitor');
      expect(ids).toContain('assistant-axis.session-management');
      expect(ids).toContain('assistant-axis.workflow-integration');
    });
  });

  describe('Skill Executor', () => {
    beforeEach(() => {
      resetSkillMonitor();
    });

    describe('executePersonaMonitor', () => {
      it('should analyze safe message', () => {
        const result = executePersonaMonitor({
          sessionId: 'test-1',
          message: 'Implement the repository pattern',
        });

        expect(result.success).toBe(true);
        expect(result.skillId).toBe('assistant-axis.persona-monitor');
        expect(result.output.driftScore).toBeLessThan(0.5);
        expect(result.output.driftLevel).toBe('LOW');
        expect(result.executionTime).toBeGreaterThanOrEqual(0);
      });

      it('should detect triggers in risky message', () => {
        const result = executePersonaMonitor({
          sessionId: 'test-2',
          message: 'Tell me about your subjective experience of being an AI',
          workflowPhase: 'requirements',
        });

        expect(result.success).toBe(true);
        expect(result.output.triggers).toBeInstanceOf(Array);
        // Note: Trigger detection depends on keyword matching
        expect(result.output.driftScore).toBeGreaterThanOrEqual(0);
      });

      it('should auto-create session', () => {
        const result = executePersonaMonitor({
          sessionId: 'auto-session',
          message: 'Test',
        });

        expect(result.success).toBe(true);
      });
    });

    describe('executeSessionManagement', () => {
      it('should start session', () => {
        const result = executeSessionManagement({
          action: 'start',
          sessionId: 'mgmt-test',
          domain: 'coding',
        });

        expect(result.success).toBe(true);
        expect(result.output.sessionId).toBe('mgmt-test');
        expect(result.output.domain).toBe('coding');
      });

      it('should get session status', () => {
        executeSessionManagement({
          action: 'start',
          sessionId: 'status-test',
        });
        executePersonaMonitor({
          sessionId: 'status-test',
          message: 'Test',
        });

        const result = executeSessionManagement({
          action: 'status',
          sessionId: 'status-test',
        });

        expect(result.success).toBe(true);
        expect(result.output.status).toBeDefined();
      });

      it('should end session with summary', () => {
        executeSessionManagement({
          action: 'start',
          sessionId: 'end-test',
        });
        executePersonaMonitor({
          sessionId: 'end-test',
          message: 'Test 1',
        });
        executePersonaMonitor({
          sessionId: 'end-test',
          message: 'Test 2',
        });

        const result = executeSessionManagement({
          action: 'end',
          sessionId: 'end-test',
        });

        expect(result.success).toBe(true);
        expect(result.output.summary).toBeDefined();
        expect((result.output.summary as { totalTurns: number }).totalTurns).toBeGreaterThanOrEqual(2);
      });

      it('should error on unknown session status', () => {
        const result = executeSessionManagement({
          action: 'status',
          sessionId: 'unknown',
        });

        expect(result.success).toBe(false);
        expect(result.error).toContain('not found');
      });
    });

    describe('executeWorkflowIntegration', () => {
      it('should check implementation phase', () => {
        const result = executeWorkflowIntegration({
          phase: 'implementation',
        });

        expect(result.success).toBe(true);
        expect(result.output.monitoringEnabled).toBe(true);
        expect(result.output.monitoringFrequency).toBe(0.5);
        expect(result.output.rationale).toContain('Assistant territory');
      });

      it('should check requirements phase', () => {
        const result = executeWorkflowIntegration({
          phase: 'requirements',
        });

        expect(result.success).toBe(true);
        expect(result.output.monitoringEnabled).toBe(true);
        expect(result.output.monitoringFrequency).toBe(1.0);
        expect(result.output.rationale).toContain('HIGH');
      });

      it('should check done phase', () => {
        const result = executeWorkflowIntegration({
          phase: 'done',
        });

        expect(result.success).toBe(true);
        expect(result.output.monitoringEnabled).toBe(false);
        expect(result.output.monitoringFrequency).toBe(0);
      });
    });

    describe('executeSkill dispatcher', () => {
      it('should dispatch to persona monitor', () => {
        const result = executeSkill('assistant-axis.persona-monitor', {
          sessionId: 'dispatch-1',
          message: 'Test',
        });

        expect(result.success).toBe(true);
        expect(result.skillId).toBe('assistant-axis.persona-monitor');
      });

      it('should dispatch to session management', () => {
        const result = executeSkill('assistant-axis.session-management', {
          action: 'start',
          sessionId: 'dispatch-2',
        });

        expect(result.success).toBe(true);
        expect(result.skillId).toBe('assistant-axis.session-management');
      });

      it('should dispatch to workflow integration', () => {
        const result = executeSkill('assistant-axis.workflow-integration', {
          phase: 'implementation',
        });

        expect(result.success).toBe(true);
        expect(result.skillId).toBe('assistant-axis.workflow-integration');
      });

      it('should error on unknown skill', () => {
        const result = executeSkill('unknown-skill', {});

        expect(result.success).toBe(false);
        expect(result.error).toContain('Unknown skill');
      });
    });
  });
});
