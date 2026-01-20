/**
 * MetricsExporter Infrastructure
 *
 * Exports metrics for analysis and monitoring
 *
 * @see REQ-AA-MON-002 - Metrics export
 */

import type { IMetricsExporter, SessionMetricsSummary } from '../application/interfaces.js';
import type { IEventLogger } from '../application/interfaces.js';
import type { DomainType } from '../domain/value-objects/ConversationDomain.js';
import type { DriftEvent, SessionEndedEvent } from '../domain/entities/DriftEvent.js';

/**
 * MetricsExporter configuration
 */
export interface MetricsExporterConfig {
  /** Event logger for data source */
  readonly eventLogger: IEventLogger;
}

/**
 * Aggregate metrics
 */
export interface AggregateMetrics {
  readonly totalSessions: number;
  readonly totalTurns: number;
  readonly totalInterventions: number;
  readonly averageDrift: number;
  readonly maxDrift: number;
  readonly interventionRate: number;
  readonly domainDistribution: Record<DomainType, number>;
}

/**
 * Create MetricsExporter service
 *
 * @param config - Configuration
 * @returns IMetricsExporter implementation
 */
export function createMetricsExporter(
  config: MetricsExporterConfig
): IMetricsExporter {
  const { eventLogger } = config;

  return {
    exportSession(sessionId: string, format: 'json' | 'markdown'): string {
      const events = eventLogger.getSessionEvents(sessionId);
      const summary = this.getSessionSummary(sessionId);

      if (format === 'json') {
        return JSON.stringify({ summary, events }, null, 2);
      }

      // Markdown format
      return formatSessionMarkdown(summary, events);
    },

    exportAggregate(format: 'json' | 'markdown'): string {
      const metrics = calculateAggregateMetrics(eventLogger);

      if (format === 'json') {
        return JSON.stringify(metrics, null, 2);
      }

      // Markdown format
      return formatAggregateMarkdown(metrics);
    },

    getSessionSummary(sessionId: string): SessionMetricsSummary {
      const events = eventLogger.getSessionEvents(sessionId);

      // Find session end event for totals
      const sessionEndEvent = events.find(
        (e) => e.type === 'session-ended'
      ) as SessionEndedEvent | undefined;

      // Calculate metrics from events
      const driftEvents = events.filter((e) => e.type === 'drift-detected');
      const interventionEvents = events.filter(
        (e) => e.type === 'intervention-triggered'
      );

      const driftScores = driftEvents.map((e) => {
        const de = e as { driftScore: { value: number } };
        return de.driftScore?.value ?? 0;
      });

      const totalTurns = sessionEndEvent?.totalTurns ?? driftEvents.length;
      const averageDrift =
        driftScores.length > 0
          ? driftScores.reduce((a, b) => a + b, 0) / driftScores.length
          : 0;
      const maxDrift = driftScores.length > 0 ? Math.max(...driftScores) : 0;
      const interventionCount =
        sessionEndEvent?.totalInterventions ?? interventionEvents.length;

      // Determine dominant domain
      const domainCounts: Record<DomainType, number> = {
        coding: 0,
        writing: 0,
        therapy: 0,
        philosophy: 0,
      };

      const domainEvents = events.filter((e) => e.type === 'domain-changed');
      for (const event of domainEvents) {
        const de = event as { newDomain: string };
        const domain = de.newDomain as DomainType;
        if (domain in domainCounts) {
          domainCounts[domain]++;
        }
      }

      const dominantDomain = (Object.entries(domainCounts).sort(
        (a, b) => b[1] - a[1]
      )[0]?.[0] ?? 'coding') as DomainType;

      // Calculate trend
      const driftTrend = calculateDriftTrend(driftScores);

      return {
        sessionId,
        totalTurns,
        averageDrift,
        maxDrift,
        interventionCount,
        dominantDomain,
        driftTrend,
      };
    },
  };
}

/**
 * Calculate aggregate metrics from all events
 */
function calculateAggregateMetrics(eventLogger: IEventLogger): AggregateMetrics {
  const allEvents = eventLogger.getAllEvents();

  // Count sessions
  const sessionIds = new Set(allEvents.map((e) => e.sessionId));
  const totalSessions = sessionIds.size;

  // Sum totals from session-ended events
  const sessionEndEvents = allEvents.filter(
    (e) => e.type === 'session-ended'
  ) as SessionEndedEvent[];

  const totalTurns = sessionEndEvents.reduce((sum, e) => sum + e.totalTurns, 0);
  const totalInterventions = sessionEndEvents.reduce(
    (sum, e) => sum + e.totalInterventions,
    0
  );

  // Calculate average drift
  const driftSum = sessionEndEvents.reduce((sum, e) => sum + e.averageDrift, 0);
  const averageDrift =
    sessionEndEvents.length > 0 ? driftSum / sessionEndEvents.length : 0;

  // Find max drift
  const maxDrift =
    sessionEndEvents.length > 0
      ? Math.max(...sessionEndEvents.map((e) => e.averageDrift))
      : 0;

  // Calculate intervention rate
  const interventionRate =
    totalTurns > 0 ? totalInterventions / totalTurns : 0;

  // Domain distribution
  const domainDistribution: Record<DomainType, number> = {
    coding: 0,
    writing: 0,
    therapy: 0,
    philosophy: 0,
  };

  const domainEvents = allEvents.filter((e) => e.type === 'domain-changed');
  for (const event of domainEvents) {
    const de = event as { newDomain: string };
    const domain = de.newDomain as DomainType;
    if (domain in domainDistribution) {
      domainDistribution[domain]++;
    }
  }

  return {
    totalSessions,
    totalTurns,
    totalInterventions,
    averageDrift,
    maxDrift,
    interventionRate,
    domainDistribution,
  };
}

/**
 * Calculate drift trend from scores
 */
function calculateDriftTrend(
  scores: number[]
): 'stable' | 'increasing' | 'decreasing' {
  if (scores.length < 3) {
    return 'stable';
  }

  const windowSize = Math.min(5, scores.length);
  const recent = scores.slice(-windowSize);
  const older = scores.slice(-windowSize * 2, -windowSize);

  if (older.length === 0) {
    return 'stable';
  }

  const recentAvg = recent.reduce((a, b) => a + b, 0) / recent.length;
  const olderAvg = older.reduce((a, b) => a + b, 0) / older.length;

  const diff = recentAvg - olderAvg;

  if (diff > 0.1) {
    return 'increasing';
  }
  if (diff < -0.1) {
    return 'decreasing';
  }
  return 'stable';
}

/**
 * Format session summary as Markdown
 */
function formatSessionMarkdown(
  summary: SessionMetricsSummary,
  events: readonly DriftEvent[]
): string {
  return `# Session Metrics: ${summary.sessionId}

## Summary

| Metric | Value |
|--------|-------|
| Total Turns | ${summary.totalTurns} |
| Average Drift | ${summary.averageDrift.toFixed(3)} |
| Max Drift | ${summary.maxDrift.toFixed(3)} |
| Interventions | ${summary.interventionCount} |
| Dominant Domain | ${summary.dominantDomain} |
| Drift Trend | ${summary.driftTrend} |

## Events Timeline

${events.map((e) => `- \`${e.timestamp.toISOString()}\` ${e.type}`).join('\n')}
`;
}

/**
 * Format aggregate metrics as Markdown
 */
function formatAggregateMarkdown(metrics: AggregateMetrics): string {
  return `# Assistant Axis Aggregate Metrics

## Overview

| Metric | Value |
|--------|-------|
| Total Sessions | ${metrics.totalSessions} |
| Total Turns | ${metrics.totalTurns} |
| Total Interventions | ${metrics.totalInterventions} |
| Average Drift | ${metrics.averageDrift.toFixed(3)} |
| Max Drift | ${metrics.maxDrift.toFixed(3)} |
| Intervention Rate | ${(metrics.interventionRate * 100).toFixed(1)}% |

## Domain Distribution

| Domain | Count |
|--------|-------|
| Coding | ${metrics.domainDistribution.coding} |
| Writing | ${metrics.domainDistribution.writing} |
| Therapy | ${metrics.domainDistribution.therapy} |
| Philosophy | ${metrics.domainDistribution.philosophy} |
`;
}
