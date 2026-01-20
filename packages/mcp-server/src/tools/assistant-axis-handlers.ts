/**
 * Assistant Axis MCP Tool Handlers
 *
 * @packageDocumentation
 * @module assistant-axis-handlers
 * @see REQ-AA-INT-004 - MCP integration
 */

import {
  handleToolCall,
  resetMCPMonitor,
} from '@nahisaho/musubix-assistant-axis';

/**
 * Input types for handlers
 */
export interface AssistantAxisAnalyzeInput {
  message: string;
  sessionId?: string;
  workflowPhase?: string;
}

export interface AssistantAxisSessionStartInput {
  sessionId: string;
  domain?: 'coding' | 'writing' | 'therapy' | 'philosophy';
}

export interface AssistantAxisSessionStatusInput {
  sessionId: string;
}

export interface AssistantAxisSessionEndInput {
  sessionId: string;
}

export interface AssistantAxisGetReinforcementInput {
  sessionId: string;
  type?: 'identity' | 'recovery' | 'refresh';
}

export interface AssistantAxisPhaseCheckInput {
  phase: string;
}

/**
 * Handle assistant_axis_analyze
 */
export function handleAssistantAxisAnalyze(input: AssistantAxisAnalyzeInput): unknown {
  const result = handleToolCall('assistant_axis_analyze', input as unknown as Record<string, unknown>);
  return JSON.parse(result.content[0].text);
}

/**
 * Handle assistant_axis_session_start
 */
export function handleAssistantAxisSessionStart(input: AssistantAxisSessionStartInput): unknown {
  const result = handleToolCall('assistant_axis_session_start', input as unknown as Record<string, unknown>);
  return JSON.parse(result.content[0].text);
}

/**
 * Handle assistant_axis_session_status
 */
export function handleAssistantAxisSessionStatus(input: AssistantAxisSessionStatusInput): unknown {
  const result = handleToolCall('assistant_axis_session_status', input as unknown as Record<string, unknown>);
  return JSON.parse(result.content[0].text);
}

/**
 * Handle assistant_axis_session_end
 */
export function handleAssistantAxisSessionEnd(input: AssistantAxisSessionEndInput): unknown {
  const result = handleToolCall('assistant_axis_session_end', input as unknown as Record<string, unknown>);
  return JSON.parse(result.content[0].text);
}

/**
 * Handle assistant_axis_get_reinforcement
 */
export function handleAssistantAxisGetReinforcement(input: AssistantAxisGetReinforcementInput): unknown {
  const result = handleToolCall('assistant_axis_get_reinforcement', input as unknown as Record<string, unknown>);
  return JSON.parse(result.content[0].text);
}

/**
 * Handle assistant_axis_config
 */
export function handleAssistantAxisConfig(): unknown {
  const result = handleToolCall('assistant_axis_config', {});
  return JSON.parse(result.content[0].text);
}

/**
 * Handle assistant_axis_phase_check
 */
export function handleAssistantAxisPhaseCheck(input: AssistantAxisPhaseCheckInput): unknown {
  const result = handleToolCall('assistant_axis_phase_check', input as unknown as Record<string, unknown>);
  return JSON.parse(result.content[0].text);
}

/**
 * Main handler dispatcher
 */
export function handleAssistantAxisTool(
  toolName: string,
  args: Record<string, unknown>
): unknown {
  switch (toolName) {
    case 'assistant_axis_analyze':
      return handleAssistantAxisAnalyze(args as unknown as AssistantAxisAnalyzeInput);
    case 'assistant_axis_session_start':
      return handleAssistantAxisSessionStart(args as unknown as AssistantAxisSessionStartInput);
    case 'assistant_axis_session_status':
      return handleAssistantAxisSessionStatus(args as unknown as AssistantAxisSessionStatusInput);
    case 'assistant_axis_session_end':
      return handleAssistantAxisSessionEnd(args as unknown as AssistantAxisSessionEndInput);
    case 'assistant_axis_get_reinforcement':
      return handleAssistantAxisGetReinforcement(args as unknown as AssistantAxisGetReinforcementInput);
    case 'assistant_axis_config':
      return handleAssistantAxisConfig();
    case 'assistant_axis_phase_check':
      return handleAssistantAxisPhaseCheck(args as unknown as AssistantAxisPhaseCheckInput);
    default:
      throw new Error(`Unknown Assistant Axis tool: ${toolName}`);
  }
}

/**
 * Reset Assistant Axis monitor (for testing)
 */
export function resetAssistantAxis(): void {
  resetMCPMonitor();
}
