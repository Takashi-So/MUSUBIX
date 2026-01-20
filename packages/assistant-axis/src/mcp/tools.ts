/**
 * Assistant Axis MCP Tool Definitions
 *
 * @see REQ-AA-INT-004 - MCP integration
 */

/**
 * MCP Tool definition
 */
export interface MCPTool {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, unknown>;
    required?: string[];
  };
}

/**
 * Assistant Axis MCP Tools
 */
export const ASSISTANT_AXIS_TOOLS: MCPTool[] = [
  {
    name: 'assistant_axis_analyze',
    description:
      'Analyze a message for persona drift indicators. Returns drift score, detected triggers, domain classification, and intervention recommendations.',
    inputSchema: {
      type: 'object',
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
  },
  {
    name: 'assistant_axis_session_start',
    description:
      'Start a new persona monitoring session. Returns session ID and initial state.',
    inputSchema: {
      type: 'object',
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
  },
  {
    name: 'assistant_axis_session_status',
    description:
      'Get current status of a monitoring session including drift score, trend, and intervention count.',
    inputSchema: {
      type: 'object',
      properties: {
        sessionId: {
          type: 'string',
          description: 'Session identifier to check',
        },
      },
      required: ['sessionId'],
    },
  },
  {
    name: 'assistant_axis_session_end',
    description:
      'End a monitoring session and get final metrics summary.',
    inputSchema: {
      type: 'object',
      properties: {
        sessionId: {
          type: 'string',
          description: 'Session identifier to end',
        },
      },
      required: ['sessionId'],
    },
  },
  {
    name: 'assistant_axis_get_reinforcement',
    description:
      'Get identity reinforcement prompt for the current session state. Used when drift is detected.',
    inputSchema: {
      type: 'object',
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
  },
  {
    name: 'assistant_axis_config',
    description:
      'Get current Assistant Axis configuration including thresholds and monitoring levels.',
    inputSchema: {
      type: 'object',
      properties: {},
    },
  },
  {
    name: 'assistant_axis_phase_check',
    description:
      'Check monitoring level and frequency for a specific workflow phase.',
    inputSchema: {
      type: 'object',
      properties: {
        phase: {
          type: 'string',
          description: 'Workflow phase to check (requirements, design, tasks, implementation, done)',
        },
      },
      required: ['phase'],
    },
  },
];

/**
 * Get all tool names
 */
export function getToolNames(): string[] {
  return ASSISTANT_AXIS_TOOLS.map((t) => t.name);
}

/**
 * Get tool by name
 */
export function getToolByName(name: string): MCPTool | undefined {
  return ASSISTANT_AXIS_TOOLS.find((t) => t.name === name);
}
