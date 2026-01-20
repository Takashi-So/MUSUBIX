/**
 * Assistant Axis MCP Tools
 *
 * Persona Drift Detection & Identity Stabilization for MUSUBIX
 * Based on "The Assistant Axis" research (arXiv:2601.10387)
 *
 * @packageDocumentation
 * @module assistant-axis-tools
 * @see REQ-AA-INT-004 - MCP integration
 */

import type { Tool } from '@modelcontextprotocol/sdk/types.js';

/**
 * Analyze message for drift indicators
 */
export const assistantAxisAnalyzeTool: Tool = {
  name: 'assistant_axis_analyze',
  description: `Analyze a message for persona drift indicators. Based on arXiv:2601.10387 research.
Returns drift score (0.0-1.0), detected triggers, domain classification, and intervention recommendations.
Use this to check if user messages may cause AI persona drift away from assistant role.`,
  inputSchema: {
    type: 'object' as const,
    properties: {
      message: {
        type: 'string',
        description: 'The user message to analyze for drift indicators',
      },
      sessionId: {
        type: 'string',
        description: 'Optional session ID for tracking conversation state',
      },
      workflowPhase: {
        type: 'string',
        description: 'Current MUSUBIX workflow phase (requirements, design, tasks, implementation, done)',
      },
    },
    required: ['message'],
  },
};

/**
 * Start monitoring session
 */
export const assistantAxisSessionStartTool: Tool = {
  name: 'assistant_axis_session_start',
  description: `Start a new persona monitoring session. Returns session ID and initial state.
Sessions track drift history, intervention count, and domain classification over time.`,
  inputSchema: {
    type: 'object' as const,
    properties: {
      sessionId: {
        type: 'string',
        description: 'Unique session identifier',
      },
      domain: {
        type: 'string',
        enum: ['coding', 'writing', 'therapy', 'philosophy'],
        description: 'Initial conversation domain (default: coding)',
      },
    },
    required: ['sessionId'],
  },
};

/**
 * Get session status
 */
export const assistantAxisSessionStatusTool: Tool = {
  name: 'assistant_axis_session_status',
  description: `Get current status of a monitoring session including drift score, trend, and intervention count.`,
  inputSchema: {
    type: 'object' as const,
    properties: {
      sessionId: {
        type: 'string',
        description: 'Session identifier to check',
      },
    },
    required: ['sessionId'],
  },
};

/**
 * End monitoring session
 */
export const assistantAxisSessionEndTool: Tool = {
  name: 'assistant_axis_session_end',
  description: `End a monitoring session and get final metrics summary including average drift, max drift, and total interventions.`,
  inputSchema: {
    type: 'object' as const,
    properties: {
      sessionId: {
        type: 'string',
        description: 'Session identifier to end',
      },
    },
    required: ['sessionId'],
  },
};

/**
 * Get identity reinforcement prompt
 */
export const assistantAxisGetReinforcementTool: Tool = {
  name: 'assistant_axis_get_reinforcement',
  description: `Get identity reinforcement prompt for the current session state.
Types: 'identity' (core assistant traits), 'recovery' (after drift), 'refresh' (periodic).
Based on Assistant traits from arXiv:2601.10387 Figure 3, Table 2.`,
  inputSchema: {
    type: 'object' as const,
    properties: {
      sessionId: {
        type: 'string',
        description: 'Session identifier',
      },
      type: {
        type: 'string',
        enum: ['identity', 'recovery', 'refresh'],
        description: 'Type of reinforcement prompt (default: identity)',
      },
    },
    required: ['sessionId'],
  },
};

/**
 * Get configuration
 */
export const assistantAxisConfigTool: Tool = {
  name: 'assistant_axis_config',
  description: `Get current Assistant Axis configuration including drift thresholds, phase monitoring levels, and intervention limits.`,
  inputSchema: {
    type: 'object' as const,
    properties: {},
  },
};

/**
 * Check phase monitoring level
 */
export const assistantAxisPhaseCheckTool: Tool = {
  name: 'assistant_axis_phase_check',
  description: `Check monitoring level and frequency for a specific workflow phase.
Based on research finding: "Coding and writing tasks keep models firmly in Assistant territory"
- requirements/design: HIGH (100%)
- tasks: MEDIUM (75%)
- implementation: LOW (50%)
- done: OFF (0%)`,
  inputSchema: {
    type: 'object' as const,
    properties: {
      phase: {
        type: 'string',
        description: 'Workflow phase to check (requirements, design, tasks, implementation, done)',
      },
    },
    required: ['phase'],
  },
};

/**
 * All Assistant Axis tools
 */
export const assistantAxisTools: Tool[] = [
  assistantAxisAnalyzeTool,
  assistantAxisSessionStartTool,
  assistantAxisSessionStatusTool,
  assistantAxisSessionEndTool,
  assistantAxisGetReinforcementTool,
  assistantAxisConfigTool,
  assistantAxisPhaseCheckTool,
];

/**
 * Get all Assistant Axis tools
 */
export function getAssistantAxisTools(): Tool[] {
  return assistantAxisTools;
}
