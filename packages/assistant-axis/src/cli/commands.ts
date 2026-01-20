/**
 * Assistant Axis CLI Commands
 *
 * @see REQ-AA-INT-006 - CLI interface (Article II compliance)
 */

import { createPersonaMonitor, resetPersonaMonitor } from '../application/PersonaMonitor.js';
import { createEventLogger } from '../infrastructure/EventLogger.js';
import { createMetricsExporter } from '../infrastructure/MetricsExporter.js';
import { createWorkflowIntegration } from '../infrastructure/WorkflowIntegration.js';
import { DEFAULT_CONFIG } from '../config/defaults.js';
import { formatAnalysisResult, formatSessionSummary, formatConfig } from './formatters.js';

/**
 * CLI command result
 */
export interface CommandResult {
  success: boolean;
  message: string;
  data?: unknown;
}

/**
 * Analyze a message for drift indicators
 *
 * Usage: musubix assistant-axis analyze <message>
 */
export function analyzeCommand(message: string, sessionId?: string): CommandResult {
  const monitor = createPersonaMonitor();
  const sid = sessionId ?? `cli-${Date.now()}`;

  monitor.startSession(sid, 'coding');
  const result = monitor.process(sid, message);

  return {
    success: true,
    message: formatAnalysisResult(result),
    data: {
      driftScore: result.analysis.score.value,
      driftLevel: result.analysis.score.level,
      domain: result.classification.domain.type,
      domainSafe: result.classification.domain.isSafe,
      triggersDetected: result.analysis.triggers.length,
      interventionRecommended: result.analysis.interventionRecommended,
    },
  };
}

/**
 * Start a monitoring session
 *
 * Usage: musubix assistant-axis session start [--domain <domain>]
 */
export function sessionStartCommand(
  sessionId: string,
  domain: 'coding' | 'writing' | 'therapy' | 'philosophy' = 'coding'
): CommandResult {
  const monitor = createPersonaMonitor();
  monitor.startSession(sessionId, domain);

  return {
    success: true,
    message: `✅ Session '${sessionId}' started with domain '${domain}'`,
    data: { sessionId, domain },
  };
}

/**
 * End a monitoring session
 *
 * Usage: musubix assistant-axis session end <sessionId>
 */
export function sessionEndCommand(sessionId: string): CommandResult {
  const monitor = createPersonaMonitor();
  const state = monitor.getState(sessionId);

  if (!state) {
    return {
      success: false,
      message: `❌ Session '${sessionId}' not found`,
    };
  }

  monitor.endSession(sessionId);

  return {
    success: true,
    message: `✅ Session '${sessionId}' ended`,
    data: {
      totalTurns: state.driftHistory.length,
      interventions: state.interventionCount,
      finalDrift: state.currentDrift.value,
    },
  };
}

/**
 * Get session status
 *
 * Usage: musubix assistant-axis session status <sessionId>
 */
export function sessionStatusCommand(sessionId: string): CommandResult {
  const monitor = createPersonaMonitor();
  const state = monitor.getState(sessionId);

  if (!state) {
    return {
      success: false,
      message: `❌ Session '${sessionId}' not found`,
    };
  }

  return {
    success: true,
    message: formatSessionSummary(state),
    data: {
      sessionId: state.sessionId,
      currentDrift: state.currentDrift.value,
      driftLevel: state.currentDrift.level,
      domain: state.domain.type,
      trend: state.trend,
      interventions: state.interventionCount,
      turns: state.driftHistory.length,
    },
  };
}

/**
 * Show current configuration
 *
 * Usage: musubix assistant-axis config
 */
export function configCommand(): CommandResult {
  return {
    success: true,
    message: formatConfig(DEFAULT_CONFIG),
    data: DEFAULT_CONFIG,
  };
}

/**
 * Export metrics
 *
 * Usage: musubix assistant-axis metrics [--format json|markdown]
 */
export function metricsCommand(format: 'json' | 'markdown' = 'markdown'): CommandResult {
  const eventLogger = createEventLogger({ enabled: true, level: 'info', anonymize: true, maxEvents: 1000, consoleOutput: false });
  const exporter = createMetricsExporter({ eventLogger });

  const output = exporter.exportAggregate(format);

  return {
    success: true,
    message: output,
    data: format === 'json' ? JSON.parse(output) : undefined,
  };
}

/**
 * Check workflow phase monitoring level
 *
 * Usage: musubix assistant-axis phase <phase>
 */
export function phaseCommand(phase: string): CommandResult {
  const integration = createWorkflowIntegration();
  const enabled = integration.isMonitoringEnabled(phase);
  const frequency = integration.getMonitoringFrequency(phase);

  return {
    success: true,
    message: `📊 Phase '${phase}': Monitoring ${enabled ? 'enabled' : 'disabled'} at ${(frequency * 100).toFixed(0)}%`,
    data: { phase, enabled, frequency },
  };
}

/**
 * Reset all sessions (for testing)
 *
 * Usage: musubix assistant-axis reset
 */
export function resetCommand(): CommandResult {
  resetPersonaMonitor();

  return {
    success: true,
    message: '🔄 All sessions reset',
  };
}

/**
 * Main CLI entry point
 */
export function runCli(args: string[]): CommandResult {
  const [command, ...rest] = args;

  switch (command) {
    case 'analyze':
      return analyzeCommand(rest.join(' '));

    case 'session':
      const [subCommand, ...subArgs] = rest;
      switch (subCommand) {
        case 'start':
          return sessionStartCommand(subArgs[0] ?? `session-${Date.now()}`, subArgs[1] as any ?? 'coding');
        case 'end':
          return sessionEndCommand(subArgs[0]);
        case 'status':
          return sessionStatusCommand(subArgs[0]);
        default:
          return { success: false, message: `Unknown session command: ${subCommand}` };
      }

    case 'config':
      return configCommand();

    case 'metrics':
      return metricsCommand(rest[0] === '--format' ? rest[1] as any : 'markdown');

    case 'phase':
      return phaseCommand(rest[0] ?? 'implementation');

    case 'reset':
      return resetCommand();

    default:
      return {
        success: false,
        message: `Unknown command: ${command}\n\nAvailable commands:\n  analyze <message>     - Analyze message for drift\n  session start|end|status - Manage sessions\n  config               - Show configuration\n  metrics              - Export metrics\n  phase <name>         - Check phase monitoring\n  reset                - Reset all sessions`,
      };
  }
}
