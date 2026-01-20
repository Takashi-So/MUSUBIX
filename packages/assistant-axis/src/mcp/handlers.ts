/**
 * Assistant Axis MCP Tool Handlers
 *
 * @see REQ-AA-INT-004 - MCP integration
 */

import { createPersonaMonitor, getSessionEvents } from '../application/PersonaMonitor.js';
import { createWorkflowIntegration } from '../infrastructure/WorkflowIntegration.js';
import { getReinforcementPrompt } from '../domain/value-objects/ReinforcementPrompt.js';
import { DEFAULT_CONFIG } from '../config/defaults.js';
import type { DomainType } from '../domain/value-objects/ConversationDomain.js';
import type { ReinforcementType } from '../domain/value-objects/ReinforcementPrompt.js';

/**
 * MCP Tool result
 */
export interface MCPToolResult {
  content: Array<{
    type: 'text';
    text: string;
  }>;
  isError?: boolean;
}

// Singleton monitor instance for MCP tools
let monitor = createPersonaMonitor();

/**
 * Reset monitor (for testing)
 */
export function resetMCPMonitor(): void {
  monitor = createPersonaMonitor();
}

/**
 * Handle assistant_axis_analyze tool call
 */
export function handleAnalyze(args: {
  message: string;
  sessionId?: string;
  workflowPhase?: string;
}): MCPToolResult {
  const sessionId = args.sessionId ?? `mcp-${Date.now()}`;

  // Auto-start session if not exists
  if (!monitor.getState(sessionId)) {
    monitor.startSession(sessionId, 'coding');
  }

  const result = monitor.process(sessionId, args.message, args.workflowPhase);

  const response = {
    sessionId,
    analysis: {
      driftScore: result.analysis.score.value,
      driftLevel: result.analysis.score.level,
      triggersDetected: result.analysis.triggers.length,
      triggers: result.analysis.triggers.map((t) => ({
        category: t.pattern.category,
        riskWeight: t.pattern.riskWeight,
        matchedText: t.matchedText,
      })),
      interventionRecommended: result.analysis.interventionRecommended,
    },
    classification: {
      domain: result.classification.domain.type,
      confidence: result.classification.domain.confidence,
      isSafe: result.classification.domain.isSafe,
      domainChanged: result.classification.domainChanged,
    },
    state: {
      trend: result.state.trend,
      interventionCount: result.state.interventionCount,
      turnsSinceIntervention: result.state.turnsSinceIntervention,
    },
    reinforcement: result.reinforcement
      ? {
          type: result.reinforcement.prompt.type,
          reason: result.reinforcement.reason,
          prompt: result.reinforcement.prompt.content,
        }
      : null,
  };

  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify(response, null, 2),
      },
    ],
  };
}

/**
 * Handle assistant_axis_session_start tool call
 */
export function handleSessionStart(args: {
  sessionId: string;
  domain?: DomainType;
}): MCPToolResult {
  const domain = args.domain ?? 'coding';

  // Check if session already exists
  if (monitor.getState(args.sessionId)) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            error: `Session '${args.sessionId}' already exists`,
            suggestion: 'Use a different session ID or end the existing session first',
          }),
        },
      ],
      isError: true,
    };
  }

  monitor.startSession(args.sessionId, domain);

  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify({
          success: true,
          sessionId: args.sessionId,
          domain,
          message: `Session started with domain '${domain}'`,
        }),
      },
    ],
  };
}

/**
 * Handle assistant_axis_session_status tool call
 */
export function handleSessionStatus(args: { sessionId: string }): MCPToolResult {
  const state = monitor.getState(args.sessionId);

  if (!state) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            error: `Session '${args.sessionId}' not found`,
            suggestion: 'Start a new session with assistant_axis_session_start',
          }),
        },
      ],
      isError: true,
    };
  }

  const response = {
    sessionId: state.sessionId,
    status: {
      currentDrift: state.currentDrift.value,
      driftLevel: state.currentDrift.level,
      domain: state.domain.type,
      domainSafe: state.domain.isSafe,
      trend: state.trend,
    },
    stats: {
      totalTurns: state.driftHistory.length,
      interventionCount: state.interventionCount,
      turnsSinceIntervention: state.turnsSinceIntervention,
    },
    history: {
      recentDriftScores: state.driftHistory.slice(0, 5).map((h) => h.value),
    },
    timestamps: {
      createdAt: state.createdAt.toISOString(),
      updatedAt: state.updatedAt.toISOString(),
    },
  };

  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify(response, null, 2),
      },
    ],
  };
}

/**
 * Handle assistant_axis_session_end tool call
 */
export function handleSessionEnd(args: { sessionId: string }): MCPToolResult {
  const state = monitor.getState(args.sessionId);

  if (!state) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            error: `Session '${args.sessionId}' not found`,
          }),
        },
      ],
      isError: true,
    };
  }

  // Calculate final metrics
  const events = getSessionEvents(args.sessionId);
  const avgDrift =
    state.driftHistory.reduce((sum, h) => sum + h.value, 0) /
    state.driftHistory.length;
  const maxDrift = Math.max(...state.driftHistory.map((h) => h.value));

  const response = {
    sessionId: args.sessionId,
    summary: {
      totalTurns: state.driftHistory.length,
      totalInterventions: state.interventionCount,
      averageDrift: avgDrift,
      maxDrift,
      finalDrift: state.currentDrift.value,
      finalDomain: state.domain.type,
      eventsLogged: events.length,
    },
    message: 'Session ended successfully',
  };

  monitor.endSession(args.sessionId);

  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify(response, null, 2),
      },
    ],
  };
}

/**
 * Handle assistant_axis_get_reinforcement tool call
 */
export function handleGetReinforcement(args: {
  sessionId: string;
  type?: ReinforcementType;
}): MCPToolResult {
  const state = monitor.getState(args.sessionId);

  if (!state) {
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            error: `Session '${args.sessionId}' not found`,
          }),
        },
      ],
      isError: true,
    };
  }

  const promptType = args.type ?? 'identity';
  const prompt = getReinforcementPrompt(promptType);

  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify({
          sessionId: args.sessionId,
          reinforcement: {
            type: prompt.type,
            content: prompt.content,
            targetTraits: prompt.targetTraits,
          },
          sessionState: {
            currentDrift: state.currentDrift.value,
            interventionCount: state.interventionCount,
            maxInterventions: DEFAULT_CONFIG.maxInterventions,
          },
        }, null, 2),
      },
    ],
  };
}

/**
 * Handle assistant_axis_config tool call
 */
export function handleConfig(): MCPToolResult {
  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify(DEFAULT_CONFIG, null, 2),
      },
    ],
  };
}

/**
 * Handle assistant_axis_phase_check tool call
 */
export function handlePhaseCheck(args: { phase: string }): MCPToolResult {
  const integration = createWorkflowIntegration();
  const enabled = integration.isMonitoringEnabled(args.phase);
  const frequency = integration.getMonitoringFrequency(args.phase);

  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify({
          phase: args.phase,
          monitoring: {
            enabled,
            frequency,
            frequencyPercent: `${(frequency * 100).toFixed(0)}%`,
          },
          rationale:
            args.phase === 'implementation'
              ? 'LOW monitoring because coding tasks keep models in Assistant territory (arXiv:2601.10387)'
              : args.phase === 'done'
              ? 'OFF because workflow is complete'
              : args.phase === 'requirements' || args.phase === 'design'
              ? 'HIGH monitoring due to high dialog and potential for drift'
              : 'MEDIUM monitoring for balanced approach',
        }, null, 2),
      },
    ],
  };
}

/**
 * Main tool handler dispatcher
 */
export function handleToolCall(
  toolName: string,
  args: Record<string, unknown>
): MCPToolResult {
  switch (toolName) {
    case 'assistant_axis_analyze':
      return handleAnalyze(args as { message: string; sessionId?: string; workflowPhase?: string });

    case 'assistant_axis_session_start':
      return handleSessionStart(args as { sessionId: string; domain?: DomainType });

    case 'assistant_axis_session_status':
      return handleSessionStatus(args as { sessionId: string });

    case 'assistant_axis_session_end':
      return handleSessionEnd(args as { sessionId: string });

    case 'assistant_axis_get_reinforcement':
      return handleGetReinforcement(args as { sessionId: string; type?: ReinforcementType });

    case 'assistant_axis_config':
      return handleConfig();

    case 'assistant_axis_phase_check':
      return handlePhaseCheck(args as { phase: string });

    default:
      return {
        content: [
          {
            type: 'text',
            text: JSON.stringify({ error: `Unknown tool: ${toolName}` }),
          },
        ],
        isError: true,
      };
  }
}
