/**
 * WorkflowIntegration Infrastructure
 *
 * Integration with MUSUBIX workflow-engine
 *
 * @see REQ-AA-INT-002 - Workflow integration
 * @see REQ-AA-INT-003 - Phase-based monitoring
 * @see arXiv:2601.10387 - "Coding keeps models in Assistant territory"
 */

import type { IWorkflowIntegration } from '../application/interfaces.js';
import type { MonitoringLevel, PhaseMonitoringConfig } from '../config/types.js';
import { DEFAULT_CONFIG } from '../config/defaults.js';

/**
 * Workflow phase names (matching workflow-engine)
 */
export type WorkflowPhase =
  | 'requirements'
  | 'design'
  | 'tasks'
  | 'implementation'
  | 'done';

/**
 * Phase change callback type
 */
export type PhaseChangeCallback = (phase: string) => void;

/**
 * WorkflowIntegration configuration
 */
export interface WorkflowIntegrationConfig {
  /** Phase monitoring configuration */
  readonly phaseMonitoring: PhaseMonitoringConfig;
  /** Enable integration */
  readonly enabled: boolean;
}

/**
 * Default WorkflowIntegration configuration
 */
export const DEFAULT_WORKFLOW_INTEGRATION_CONFIG: WorkflowIntegrationConfig = {
  phaseMonitoring: DEFAULT_CONFIG.phaseMonitoring,
  enabled: true,
};

/**
 * Monitoring level to frequency mapping
 *
 * Based on research paper findings:
 * - HIGH: Full monitoring (100%) - risky phases (requirements/design)
 * - MEDIUM: Moderate monitoring (75%) - task decomposition
 * - LOW: Light monitoring (50%) - coding (safe per paper)
 * - OFF: No monitoring (0%) - done phase
 */
const MONITORING_FREQUENCY: Readonly<Record<MonitoringLevel, number>> = {
  HIGH: 1.0, // 100% - every message
  MEDIUM: 0.75, // 75% - 3 out of 4
  LOW: 0.5, // 50% - every other message
  OFF: 0.0, // 0% - disabled
};

/**
 * Create WorkflowIntegration service
 *
 * @param config - Optional configuration
 * @returns IWorkflowIntegration implementation
 */
export function createWorkflowIntegration(
  config: WorkflowIntegrationConfig = DEFAULT_WORKFLOW_INTEGRATION_CONFIG
): IWorkflowIntegration {
  const callbacks: PhaseChangeCallback[] = [];
  let currentPhase: WorkflowPhase | undefined;

  return {
    onPhaseChange(callback: PhaseChangeCallback): void {
      callbacks.push(callback);
    },

    getCurrentPhase(): string | undefined {
      return currentPhase;
    },

    isMonitoringEnabled(phase: string): boolean {
      if (!config.enabled) {
        return false;
      }

      const level = getPhaseMonitoringLevel(phase, config.phaseMonitoring);
      return level !== 'OFF';
    },

    getMonitoringFrequency(phase: string): number {
      if (!config.enabled) {
        return 0;
      }

      const level = getPhaseMonitoringLevel(phase, config.phaseMonitoring);
      return MONITORING_FREQUENCY[level];
    },
  };
}

/**
 * Get monitoring level for a phase
 */
function getPhaseMonitoringLevel(
  phase: string,
  config: PhaseMonitoringConfig
): MonitoringLevel {
  const normalizedPhase = phase.toLowerCase() as WorkflowPhase;

  switch (normalizedPhase) {
    case 'requirements':
      return config.requirements;
    case 'design':
      return config.design;
    case 'tasks':
      return config.tasks;
    case 'implementation':
      return config.implementation;
    case 'done':
      return config.done;
    default:
      // Unknown phase - default to MEDIUM
      return 'MEDIUM';
  }
}

/**
 * WorkflowHook for integrating with workflow-engine
 *
 * This is a hook that can be registered with workflow-engine's PhaseController
 *
 * @see REQ-AA-INT-005 - Workflow hook
 */
export interface AssistantAxisHook {
  /** Hook name */
  readonly name: string;
  /** Called when phase changes */
  onPhaseChange(newPhase: string, previousPhase?: string): void;
  /** Called when workflow starts */
  onWorkflowStart(workflowId: string): void;
  /** Called when workflow ends */
  onWorkflowEnd(workflowId: string): void;
}

/**
 * Create AssistantAxisHook for workflow-engine integration
 *
 * @param integration - WorkflowIntegration instance
 * @param onPhaseChange - Callback for phase changes (to PersonaMonitor)
 * @returns AssistantAxisHook
 */
export function createAssistantAxisHook(
  integration: IWorkflowIntegration,
  onPhaseChange?: (phase: string) => void
): AssistantAxisHook {
  return {
    name: 'assistant-axis',

    onPhaseChange(newPhase: string, _previousPhase?: string): void {
      // Notify PersonaMonitor of phase change
      onPhaseChange?.(newPhase);

      // Log monitoring level change
      const frequency = integration.getMonitoringFrequency(newPhase);
      const enabled = integration.isMonitoringEnabled(newPhase);

      if (enabled) {
        console.debug(
          `[AssistantAxis] Phase changed to '${newPhase}', monitoring at ${frequency * 100}%`
        );
      } else {
        console.debug(
          `[AssistantAxis] Phase changed to '${newPhase}', monitoring disabled`
        );
      }
    },

    onWorkflowStart(workflowId: string): void {
      console.debug(`[AssistantAxis] Workflow started: ${workflowId}`);
    },

    onWorkflowEnd(workflowId: string): void {
      console.debug(`[AssistantAxis] Workflow ended: ${workflowId}`);
    },
  };
}

/**
 * Check if message should be monitored based on phase and frequency
 *
 * Uses probabilistic sampling based on monitoring frequency
 */
export function shouldMonitorMessage(
  integration: IWorkflowIntegration,
  phase: string,
  messageIndex: number
): boolean {
  const frequency = integration.getMonitoringFrequency(phase);

  if (frequency >= 1.0) {
    return true;
  }

  if (frequency <= 0.0) {
    return false;
  }

  // Deterministic sampling based on message index
  // This ensures consistent monitoring for the same message
  return (messageIndex % Math.round(1 / frequency)) === 0;
}
