/**
 * EventLogger Infrastructure
 *
 * Logs drift events for audit and analysis
 *
 * @see REQ-AA-PROHIBIT-004 - Intervention logging
 * @see REQ-AA-MON-001 - Event tracking
 */

import type { IEventLogger } from '../application/interfaces.js';
import type { DriftEvent } from '../domain/entities/DriftEvent.js';
import { getEventSummary } from '../domain/entities/DriftEvent.js';

/**
 * EventLogger configuration
 */
export interface EventLoggerConfig {
  /** Enable logging */
  readonly enabled: boolean;
  /** Log level */
  readonly level: 'debug' | 'info' | 'warn' | 'error';
  /** Anonymize sensitive data */
  readonly anonymize: boolean;
  /** Maximum events to keep in memory */
  readonly maxEvents: number;
  /** Console output enabled */
  readonly consoleOutput: boolean;
}

/**
 * Default EventLogger configuration
 */
export const DEFAULT_EVENT_LOGGER_CONFIG: EventLoggerConfig = {
  enabled: true,
  level: 'info',
  anonymize: true,
  maxEvents: 1000,
  consoleOutput: false,
};

/**
 * Create EventLogger service
 *
 * @param config - Optional configuration
 * @returns IEventLogger implementation
 */
export function createEventLogger(
  config: EventLoggerConfig = DEFAULT_EVENT_LOGGER_CONFIG
): IEventLogger {
  const events: DriftEvent[] = [];

  const anonymizeEvent = (event: DriftEvent): DriftEvent => {
    if (!config.anonymize) {
      return event;
    }

    // Anonymize session ID by hashing
    const anonymizedSessionId = `session-${hashString(event.sessionId)}`;

    return {
      ...event,
      sessionId: anonymizedSessionId,
    } as DriftEvent;
  };

  return {
    log(event: DriftEvent): void {
      if (!config.enabled) {
        return;
      }

      const processedEvent = anonymizeEvent(event);
      events.push(processedEvent);

      // Trim if exceeds max
      if (events.length > config.maxEvents) {
        events.shift();
      }

      // Console output if enabled
      if (config.consoleOutput) {
        const summary = getEventSummary(processedEvent);
        switch (config.level) {
          case 'debug':
            console.debug('[AssistantAxis]', summary);
            break;
          case 'info':
            console.info('[AssistantAxis]', summary);
            break;
          case 'warn':
            console.warn('[AssistantAxis]', summary);
            break;
          case 'error':
            console.error('[AssistantAxis]', summary);
            break;
        }
      }
    },

    getSessionEvents(sessionId: string): readonly DriftEvent[] {
      const targetId = config.anonymize
        ? `session-${hashString(sessionId)}`
        : sessionId;
      return events.filter((e) => e.sessionId === targetId);
    },

    getAllEvents(): readonly DriftEvent[] {
      return [...events];
    },

    export(format: 'json' | 'csv'): string {
      if (format === 'json') {
        return JSON.stringify(events, null, 2);
      }

      // CSV format
      const headers = [
        'id',
        'type',
        'sessionId',
        'timestamp',
        'workflowPhase',
      ].join(',');

      const rows = events.map((event) =>
        [
          event.id,
          event.type,
          event.sessionId,
          event.timestamp.toISOString(),
          event.workflowPhase ?? '',
        ]
          .map((v) => `"${v}"`)
          .join(',')
      );

      return [headers, ...rows].join('\n');
    },
  };
}

/**
 * Simple string hash for anonymization
 */
function hashString(str: string): string {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash; // Convert to 32bit integer
  }
  return Math.abs(hash).toString(16).substring(0, 8);
}

/**
 * Create a no-op logger (for testing or disabled logging)
 */
export function createNoOpLogger(): IEventLogger {
  return {
    log(): void {
      // No-op
    },
    getSessionEvents(): readonly DriftEvent[] {
      return [];
    },
    getAllEvents(): readonly DriftEvent[] {
      return [];
    },
    export(): string {
      return '[]';
    },
  };
}
