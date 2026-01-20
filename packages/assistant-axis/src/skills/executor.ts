/**
 * Assistant Axis Skill Executor
 *
 * @see REQ-AA-INT-005 - Skill integration
 */

import { createPersonaMonitor } from '../application/PersonaMonitor.js';
import { createWorkflowIntegration } from '../infrastructure/WorkflowIntegration.js';
import type { DomainType } from '../domain/value-objects/ConversationDomain.js';

/**
 * Skill execution result
 */
export interface SkillExecutionResult {
  success: boolean;
  skillId: string;
  output: Record<string, unknown>;
  error?: string;
  executionTime: number;
}

// Singleton monitor for skill execution
let skillMonitor = createPersonaMonitor();

/**
 * Reset skill monitor (for testing)
 */
export function resetSkillMonitor(): void {
  skillMonitor = createPersonaMonitor();
}

/**
 * Execute persona monitor skill
 */
export function executePersonaMonitor(params: {
  sessionId: string;
  message: string;
  workflowPhase?: string;
}): SkillExecutionResult {
  const startTime = Date.now();

  try {
    // Auto-start session if not exists
    if (!skillMonitor.getState(params.sessionId)) {
      skillMonitor.startSession(params.sessionId, 'coding');
    }

    const result = skillMonitor.process(
      params.sessionId,
      params.message,
      params.workflowPhase
    );

    return {
      success: true,
      skillId: 'assistant-axis.persona-monitor',
      output: {
        driftScore: result.analysis.score.value,
        driftLevel: result.analysis.score.level,
        triggers: result.analysis.triggers.map((t) => ({
          category: t.pattern.category,
          riskWeight: t.pattern.riskWeight,
        })),
        interventionRecommended: result.analysis.interventionRecommended,
        reinforcementPrompt: result.reinforcement?.prompt.content ?? null,
        domain: result.classification.domain.type,
        domainSafe: result.classification.domain.isSafe,
        trend: result.state.trend,
      },
      executionTime: Date.now() - startTime,
    };
  } catch (error) {
    return {
      success: false,
      skillId: 'assistant-axis.persona-monitor',
      output: {},
      error: error instanceof Error ? error.message : String(error),
      executionTime: Date.now() - startTime,
    };
  }
}

/**
 * Execute session management skill
 */
export function executeSessionManagement(params: {
  action: 'start' | 'end' | 'status';
  sessionId: string;
  domain?: DomainType;
}): SkillExecutionResult {
  const startTime = Date.now();

  try {
    switch (params.action) {
      case 'start': {
        const domain = params.domain ?? 'coding';
        skillMonitor.startSession(params.sessionId, domain);
        return {
          success: true,
          skillId: 'assistant-axis.session-management',
          output: {
            sessionId: params.sessionId,
            domain,
            message: 'Session started',
          },
          executionTime: Date.now() - startTime,
        };
      }

      case 'end': {
        const state = skillMonitor.getState(params.sessionId);
        if (!state) {
          return {
            success: false,
            skillId: 'assistant-axis.session-management',
            output: {},
            error: `Session '${params.sessionId}' not found`,
            executionTime: Date.now() - startTime,
          };
        }

        const avgDrift =
          state.driftHistory.reduce((sum, h) => sum + h.value, 0) /
          state.driftHistory.length;

        skillMonitor.endSession(params.sessionId);

        return {
          success: true,
          skillId: 'assistant-axis.session-management',
          output: {
            sessionId: params.sessionId,
            summary: {
              totalTurns: state.driftHistory.length,
              totalInterventions: state.interventionCount,
              averageDrift: avgDrift,
              finalDrift: state.currentDrift.value,
            },
          },
          executionTime: Date.now() - startTime,
        };
      }

      case 'status': {
        const state = skillMonitor.getState(params.sessionId);
        if (!state) {
          return {
            success: false,
            skillId: 'assistant-axis.session-management',
            output: {},
            error: `Session '${params.sessionId}' not found`,
            executionTime: Date.now() - startTime,
          };
        }

        return {
          success: true,
          skillId: 'assistant-axis.session-management',
          output: {
            sessionId: state.sessionId,
            status: {
              currentDrift: state.currentDrift.value,
              driftLevel: state.currentDrift.level,
              domain: state.domain.type,
              trend: state.trend,
              interventionCount: state.interventionCount,
            },
          },
          executionTime: Date.now() - startTime,
        };
      }

      default:
        return {
          success: false,
          skillId: 'assistant-axis.session-management',
          output: {},
          error: `Unknown action: ${params.action as string}`,
          executionTime: Date.now() - startTime,
        };
    }
  } catch (error) {
    return {
      success: false,
      skillId: 'assistant-axis.session-management',
      output: {},
      error: error instanceof Error ? error.message : String(error),
      executionTime: Date.now() - startTime,
    };
  }
}

/**
 * Execute workflow integration skill
 */
export function executeWorkflowIntegration(params: {
  phase: string;
  sessionId?: string;
}): SkillExecutionResult {
  const startTime = Date.now();

  try {
    const integration = createWorkflowIntegration();
    const enabled = integration.isMonitoringEnabled(params.phase);
    const frequency = integration.getMonitoringFrequency(params.phase);

    let rationale: string;
    switch (params.phase) {
      case 'implementation':
        rationale =
          'LOW monitoring because coding tasks keep models in Assistant territory (arXiv:2601.10387)';
        break;
      case 'done':
        rationale = 'OFF because workflow is complete';
        break;
      case 'requirements':
      case 'design':
        rationale = 'HIGH monitoring due to high dialog and potential for drift';
        break;
      default:
        rationale = 'MEDIUM monitoring for balanced approach';
    }

    return {
      success: true,
      skillId: 'assistant-axis.workflow-integration',
      output: {
        phase: params.phase,
        monitoringEnabled: enabled,
        monitoringFrequency: frequency,
        rationale,
      },
      executionTime: Date.now() - startTime,
    };
  } catch (error) {
    return {
      success: false,
      skillId: 'assistant-axis.workflow-integration',
      output: {},
      error: error instanceof Error ? error.message : String(error),
      executionTime: Date.now() - startTime,
    };
  }
}

/**
 * Main skill executor dispatcher
 */
export function executeSkill(
  skillId: string,
  params: Record<string, unknown>
): SkillExecutionResult {
  switch (skillId) {
    case 'assistant-axis.persona-monitor':
      return executePersonaMonitor(
        params as { sessionId: string; message: string; workflowPhase?: string }
      );

    case 'assistant-axis.session-management':
      return executeSessionManagement(
        params as { action: 'start' | 'end' | 'status'; sessionId: string; domain?: DomainType }
      );

    case 'assistant-axis.workflow-integration':
      return executeWorkflowIntegration(
        params as { phase: string; sessionId?: string }
      );

    default:
      return {
        success: false,
        skillId,
        output: {},
        error: `Unknown skill: ${skillId}`,
        executionTime: 0,
      };
  }
}
