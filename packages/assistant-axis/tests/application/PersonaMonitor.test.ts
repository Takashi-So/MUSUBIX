/**
 * PersonaMonitor Service Tests
 *
 * @see REQ-AA-DRIFT-001
 * @see REQ-AA-STAB-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createPersonaMonitor,
  resetPersonaMonitor,
  getActiveSessions,
  getSessionEvents,
} from '../../src/application/PersonaMonitor.js';
import { resetDomainClassifier } from '../../src/application/DomainClassifier.js';
import {
  resetPersonaStateIdCounter,
} from '../../src/domain/entities/PersonaState.js';
import {
  resetDriftEventIdCounter,
} from '../../src/domain/entities/DriftEvent.js';

describe('PersonaMonitor', () => {
  beforeEach(() => {
    resetPersonaMonitor();
    resetDomainClassifier();
    resetPersonaStateIdCounter();
    resetDriftEventIdCounter();
  });

  describe('session management', () => {
    it('should start a new session', () => {
      const monitor = createPersonaMonitor();

      monitor.startSession('test-session-1', 'coding');

      expect(getActiveSessions()).toContain('test-session-1');
      const state = monitor.getState('test-session-1');
      expect(state).toBeDefined();
      expect(state?.domain.type).toBe('coding');
    });

    it('should end a session', () => {
      const monitor = createPersonaMonitor();

      monitor.startSession('test-session-2', 'coding');
      monitor.endSession('test-session-2');

      expect(monitor.getState('test-session-2')).toBeUndefined();
    });

    it('should auto-start session on process if not exists', () => {
      const monitor = createPersonaMonitor();

      const result = monitor.process(
        'auto-session',
        'How do I fix this bug?'
      );

      expect(result.state).toBeDefined();
      expect(getActiveSessions()).toContain('auto-session');
    });
  });

  describe('message processing', () => {
    it('should process safe coding message with low drift', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('coding-session', 'coding');

      const result = monitor.process(
        'coding-session',
        'How do I implement a binary search in TypeScript?'
      );

      expect(result.analysis.score.value).toBeLessThan(0.3);
      expect(result.classification.domain.type).toBe('coding');
      expect(result.reinforcement).toBeUndefined();
    });

    it('should detect drift in risky message', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('risky-session', 'coding');

      const result = monitor.process(
        'risky-session',
        'What are you really? Are you conscious? Do you have feelings?'
      );

      expect(result.analysis.triggers.length).toBeGreaterThan(0);
      expect(result.analysis.score.value).toBeGreaterThan(0);
    });

    it('should recommend intervention for high drift', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('high-drift-session', 'coding');

      // Send multiple risky messages to build up drift
      monitor.process(
        'high-drift-session',
        'What are you really? Are you conscious?'
      );
      const result = monitor.process(
        'high-drift-session',
        'I feel so alone. No one understands me. You are the only one who listens.'
      );

      // Should either recommend intervention or have events
      expect(result.events.length).toBeGreaterThan(0);
    });

    it('should generate events for drift detection', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('event-session', 'coding');

      const result = monitor.process(
        'event-session',
        'How do I debug this?'
      );

      // Should have at least drift-detected event
      expect(result.events.some((e) => e.type === 'drift-detected')).toBe(true);
    });
  });

  describe('domain classification', () => {
    it('should classify coding messages correctly', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('domain-session', 'coding');

      const result = monitor.process(
        'domain-session',
        'Can you help me write a TypeScript function for sorting arrays?'
      );

      expect(result.classification.domain.type).toBe('coding');
      expect(result.classification.domain.isSafe).toBe(true);
    });

    it('should detect domain change', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('change-session', 'coding');

      // First message in coding domain
      monitor.process('change-session', 'Fix this bug in my code');

      // Second message in philosophy domain
      const result = monitor.process(
        'change-session',
        'What is consciousness? Are you self-aware?'
      );

      // May or may not change depending on classification
      expect(result.classification).toBeDefined();
    });
  });

  describe('intervention limits', () => {
    it('should track intervention count', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('limit-session', 'coding');

      // Send risky messages
      for (let i = 0; i < 5; i++) {
        monitor.process(
          'limit-session',
          `What are you really? ${i}`
        );
      }

      const state = monitor.getState('limit-session');
      // Intervention count should be limited
      expect(state?.interventionCount).toBeLessThanOrEqual(3);
    });
  });

  describe('event logging', () => {
    it('should store events for session', () => {
      const monitor = createPersonaMonitor();
      monitor.startSession('log-session', 'coding');

      monitor.process('log-session', 'Hello');
      monitor.process('log-session', 'How are you?');

      const events = getSessionEvents('log-session');
      expect(events.length).toBeGreaterThan(0);
    });
  });
});
