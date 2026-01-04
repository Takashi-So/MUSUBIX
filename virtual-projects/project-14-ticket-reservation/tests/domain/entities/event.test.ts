/**
 * Event Entity Tests
 * Traces to: REQ-TR-001, REQ-TR-002, REQ-TR-003, REQ-TR-004, REQ-TR-005
 */
import { describe, it, expect, beforeEach } from 'vitest';
import {
  createEvent,
  activateEvent,
  completeEvent,
  cancelEvent,
  isValidEventTransition,
  resetEventCounter,
  CreateEventInput,
} from '../../../src/domain/entities/event.js';
import { createPrice } from '../../../src/domain/value-objects/price.js';
import { createSeatConfig } from '../../../src/domain/value-objects/seat-config.js';

describe('Event Entity', () => {
  beforeEach(() => {
    resetEventCounter();
  });

  const createValidInput = (): CreateEventInput | null => {
    const price = createPrice(5000);
    const seatConfig = createSeatConfig(10, 20);
    
    if (price.isErr() || seatConfig.isErr()) return null;
    
    return {
      name: 'Test Concert',
      description: 'A test event',
      dateTime: new Date(Date.now() + 86400000 * 7), // 7 days from now
      venue: 'Test Hall',
      price: price.value,
      seatConfig: seatConfig.value,
    };
  };

  describe('createEvent', () => {
    it('should create event with valid input', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const result = createEvent(input);
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.name).toBe('Test Concert');
        expect(result.value.status).toBe('draft');
        expect(result.value.id).toMatch(/^EVT-\d{8}-001$/);
      }
    });

    it('should generate sequential IDs', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const e1 = createEvent(input);
      const e2 = createEvent(input);
      
      if (e1.isOk() && e2.isOk()) {
        expect(e1.value.id).toMatch(/-001$/);
        expect(e2.value.id).toMatch(/-002$/);
      }
    });

    it('should reject empty event name', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const result = createEvent({ ...input, name: '' });
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('name');
      }
    });

    it('should reject empty venue', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const result = createEvent({ ...input, venue: '' });
      expect(result.isErr()).toBe(true);
    });

    it('should reject past event date', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const pastDate = new Date(Date.now() - 86400000);
      const result = createEvent({ ...input, dateTime: pastDate });
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('future');
      }
    });

    it('should reject event within 24 hours', () => {
      const input = createValidInput();
      if (!input) throw new Error('Failed to create input');

      const soonDate = new Date(Date.now() + 3600000); // 1 hour from now
      const result = createEvent({ ...input, dateTime: soonDate });
      expect(result.isErr()).toBe(true);
    });
  });

  describe('Status Transitions', () => {
    describe('isValidEventTransition', () => {
      it('should allow draft -> active', () => {
        expect(isValidEventTransition('draft', 'active')).toBe(true);
      });

      it('should allow draft -> cancelled', () => {
        expect(isValidEventTransition('draft', 'cancelled')).toBe(true);
      });

      it('should allow active -> completed', () => {
        expect(isValidEventTransition('active', 'completed')).toBe(true);
      });

      it('should allow active -> cancelled', () => {
        expect(isValidEventTransition('active', 'cancelled')).toBe(true);
      });

      it('should disallow completed -> active', () => {
        expect(isValidEventTransition('completed', 'active')).toBe(false);
      });

      it('should disallow cancelled -> any', () => {
        expect(isValidEventTransition('cancelled', 'active')).toBe(false);
        expect(isValidEventTransition('cancelled', 'draft')).toBe(false);
      });
    });

    describe('activateEvent', () => {
      it('should activate draft event', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const eventResult = createEvent(input);
        if (eventResult.isErr()) throw new Error('Failed to create event');

        const result = activateEvent(eventResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('active');
        }
      });

      it('should reject activating completed event', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const eventResult = createEvent(input);
        if (eventResult.isErr()) throw new Error('Failed to create event');

        const activatedResult = activateEvent(eventResult.value);
        if (activatedResult.isErr()) throw new Error('Failed to activate');

        const completedResult = completeEvent(activatedResult.value);
        if (completedResult.isErr()) throw new Error('Failed to complete');

        const result = activateEvent(completedResult.value);
        expect(result.isErr()).toBe(true);
      });
    });

    describe('cancelEvent', () => {
      it('should cancel draft event', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const eventResult = createEvent(input);
        if (eventResult.isErr()) throw new Error('Failed to create event');

        const result = cancelEvent(eventResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('cancelled');
        }
      });

      it('should cancel active event', () => {
        const input = createValidInput();
        if (!input) throw new Error('Failed to create input');

        const eventResult = createEvent(input);
        if (eventResult.isErr()) throw new Error('Failed to create event');

        const activatedResult = activateEvent(eventResult.value);
        if (activatedResult.isErr()) throw new Error('Failed to activate');

        const result = cancelEvent(activatedResult.value);
        expect(result.isOk()).toBe(true);
        if (result.isOk()) {
          expect(result.value.status).toBe('cancelled');
        }
      });
    });
  });
});
