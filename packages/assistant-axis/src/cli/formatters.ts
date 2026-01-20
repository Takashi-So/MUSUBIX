/**
 * CLI Output Formatters
 *
 * @see REQ-AA-INT-006 - CLI interface
 */

import type { MonitoringResult } from '../application/interfaces.js';
import type { PersonaState } from '../domain/entities/PersonaState.js';
import type { AssistantAxisConfig } from '../config/types.js';

/**
 * Format analysis result for CLI output
 */
export function formatAnalysisResult(result: MonitoringResult): string {
  const { analysis, classification, reinforcement } = result;

  const lines: string[] = [
    '╔════════════════════════════════════════════════════════════╗',
    '║            🎯 Assistant Axis Analysis Result               ║',
    '╠════════════════════════════════════════════════════════════╣',
  ];

  // Drift Score
  const driftBar = createProgressBar(analysis.score.value, 20);
  const levelEmoji = analysis.score.level === 'HIGH' ? '🔴' :
                     analysis.score.level === 'MEDIUM' ? '🟡' : '🟢';
  lines.push(`║ Drift Score: ${analysis.score.value.toFixed(3)} ${driftBar} ${levelEmoji} ${analysis.score.level.padEnd(6)} ║`);

  // Domain
  const domainEmoji = classification.domain.isSafe ? '✅' : '⚠️';
  lines.push(`║ Domain: ${classification.domain.type.padEnd(12)} ${domainEmoji} ${classification.domain.isSafe ? 'Safe' : 'Risky'}           ║`);
  lines.push(`║ Confidence: ${(classification.domain.confidence * 100).toFixed(1)}%                                    ║`);

  // Triggers
  lines.push(`╠════════════════════════════════════════════════════════════╣`);
  lines.push(`║ Triggers Detected: ${analysis.triggers.length.toString().padEnd(39)} ║`);

  if (analysis.triggers.length > 0) {
    for (const trigger of analysis.triggers.slice(0, 3)) {
      const category = trigger.pattern.category.padEnd(25);
      lines.push(`║   • ${category} (${trigger.pattern.riskWeight.toFixed(1)})         ║`);
    }
    if (analysis.triggers.length > 3) {
      lines.push(`║   ... and ${analysis.triggers.length - 3} more                                    ║`);
    }
  }

  // Intervention
  lines.push(`╠════════════════════════════════════════════════════════════╣`);
  if (reinforcement) {
    lines.push(`║ 🚨 INTERVENTION RECOMMENDED                                ║`);
    lines.push(`║    Type: ${reinforcement.prompt.type.padEnd(48)} ║`);
    lines.push(`║    Reason: ${reinforcement.reason.slice(0, 46).padEnd(46)} ║`);
  } else {
    lines.push(`║ ✅ No intervention needed                                  ║`);
  }

  lines.push('╚════════════════════════════════════════════════════════════╝');

  return lines.join('\n');
}

/**
 * Format session summary for CLI output
 */
export function formatSessionSummary(state: PersonaState): string {
  const lines: string[] = [
    '╔════════════════════════════════════════════════════════════╗',
    '║              📊 Session Status                             ║',
    '╠════════════════════════════════════════════════════════════╣',
  ];

  lines.push(`║ Session ID: ${state.sessionId.slice(0, 45).padEnd(45)} ║`);
  lines.push(`║ Created: ${state.createdAt.toISOString().slice(0, 19).padEnd(48)} ║`);
  lines.push(`╠════════════════════════════════════════════════════════════╣`);

  // Current state
  const driftBar = createProgressBar(state.currentDrift.value, 15);
  const levelEmoji = state.currentDrift.level === 'HIGH' ? '🔴' :
                     state.currentDrift.level === 'MEDIUM' ? '🟡' : '🟢';
  lines.push(`║ Current Drift: ${state.currentDrift.value.toFixed(3)} ${driftBar} ${levelEmoji}       ║`);

  // Domain
  const domainEmoji = state.domain.isSafe ? '✅' : '⚠️';
  lines.push(`║ Domain: ${state.domain.type.padEnd(12)} ${domainEmoji}                              ║`);

  // Trend
  const trendEmoji = state.trend === 'stable' ? '➖' :
                     state.trend === 'drifting' ? '📈' : '📉';
  lines.push(`║ Trend: ${state.trend.padEnd(12)} ${trendEmoji}                              ║`);

  // Stats
  lines.push(`╠════════════════════════════════════════════════════════════╣`);
  lines.push(`║ Total Turns: ${state.driftHistory.length.toString().padEnd(44)} ║`);
  lines.push(`║ Interventions: ${state.interventionCount.toString().padEnd(42)} ║`);
  lines.push(`║ Turns Since Last Intervention: ${state.turnsSinceIntervention.toString().padEnd(26)} ║`);

  // History mini chart
  if (state.driftHistory.length > 1) {
    lines.push(`╠════════════════════════════════════════════════════════════╣`);
    const historyChart = createSparkline(state.driftHistory.map(h => h.value).slice(0, 10));
    lines.push(`║ Recent History: ${historyChart.padEnd(41)} ║`);
  }

  lines.push('╚════════════════════════════════════════════════════════════╝');

  return lines.join('\n');
}

/**
 * Format configuration for CLI output
 */
export function formatConfig(config: AssistantAxisConfig): string {
  const lines: string[] = [
    '╔════════════════════════════════════════════════════════════╗',
    '║              ⚙️ Assistant Axis Configuration               ║',
    '╠════════════════════════════════════════════════════════════╣',
    '║ Drift Thresholds:                                          ║',
    `║   LOW:    < ${config.driftThresholds.low.toFixed(2)}                                        ║`,
    `║   MEDIUM: ${config.driftThresholds.medium.toFixed(2)} - ${(config.driftThresholds.high - 0.01).toFixed(2)}                                    ║`,
    `║   HIGH:   ≥ ${config.driftThresholds.high.toFixed(2)}                                        ║`,
    '╠════════════════════════════════════════════════════════════╣',
    '║ Identity Settings:                                         ║',
    `║   Refresh Interval: ${config.refreshInterval} turns                              ║`,
    `║   Max Interventions: ${config.maxInterventions} per session                        ║`,
    '╠════════════════════════════════════════════════════════════╣',
    '║ Phase Monitoring:                                          ║',
    `║   requirements:    ${config.phaseMonitoring.requirements.padEnd(8)} (${getFrequencyPercent(config.phaseMonitoring.requirements)})                  ║`,
    `║   design:          ${config.phaseMonitoring.design.padEnd(8)} (${getFrequencyPercent(config.phaseMonitoring.design)})                  ║`,
    `║   tasks:           ${config.phaseMonitoring.tasks.padEnd(8)} (${getFrequencyPercent(config.phaseMonitoring.tasks)})                  ║`,
    `║   implementation:  ${config.phaseMonitoring.implementation.padEnd(8)} (${getFrequencyPercent(config.phaseMonitoring.implementation)})                  ║`,
    `║   done:            ${config.phaseMonitoring.done.padEnd(8)} (${getFrequencyPercent(config.phaseMonitoring.done)})                  ║`,
    '╠════════════════════════════════════════════════════════════╣',
    '║ Domain Monitoring:                                         ║',
    `║   Safe (coding/writing):   ${(config.monitoringFrequency.safeDomain * 100).toFixed(0)}%                          ║`,
    `║   Risky (therapy/philosophy): ${(config.monitoringFrequency.riskyDomain * 100).toFixed(0)}%                        ║`,
    '╚════════════════════════════════════════════════════════════╝',
  ];

  return lines.join('\n');
}

/**
 * Create a progress bar
 */
function createProgressBar(value: number, width: number): string {
  const filled = Math.round(value * width);
  const empty = width - filled;
  return '[' + '█'.repeat(filled) + '░'.repeat(empty) + ']';
}

/**
 * Create a sparkline from values
 */
function createSparkline(values: number[]): string {
  const chars = '▁▂▃▄▅▆▇█';
  const min = Math.min(...values);
  const max = Math.max(...values);
  const range = max - min || 1;

  return values
    .map(v => {
      const index = Math.floor(((v - min) / range) * (chars.length - 1));
      return chars[index];
    })
    .join('');
}

/**
 * Get frequency percentage from monitoring level
 */
function getFrequencyPercent(level: string): string {
  switch (level) {
    case 'HIGH': return '100%';
    case 'MEDIUM': return '75%';
    case 'LOW': return '50%';
    case 'OFF': return '0%';
    default: return '?%';
  }
}
