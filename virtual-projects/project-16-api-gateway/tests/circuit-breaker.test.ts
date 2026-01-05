// Tests for Circuit Breaker
// REQ-ROUTE-004

import { describe, it, expect } from 'vitest';
import {
  createCircuitBreaker,
  canRequest,
  recordSuccess,
  recordFailure,
  tryHalfOpen,
} from '../src/domain/circuit-breaker.js';

describe('CircuitBreaker', () => {
  describe('createCircuitBreaker', () => {
    it('should create circuit in closed state', () => {
      const circuit = createCircuitBreaker('backend-1');

      expect(circuit.state).toBe('closed');
      expect(circuit.failureCount).toBe(0);
      expect(circuit.successCount).toBe(0);
    });

    it('should use custom config', () => {
      const circuit = createCircuitBreaker('backend-1', {
        failureThreshold: 3,
        resetTimeoutMs: 10000,
      });

      expect(circuit.config.failureThreshold).toBe(3);
      expect(circuit.config.resetTimeoutMs).toBe(10000);
    });
  });

  describe('canRequest', () => {
    it('should allow requests when closed', () => {
      const circuit = createCircuitBreaker('backend-1');
      expect(canRequest(circuit)).toBe(true);
    });

    it('should allow requests when half-open', () => {
      let circuit = createCircuitBreaker('backend-1');
      // Force to half-open state
      for (let i = 0; i < 5; i++) {
        circuit = recordFailure(circuit);
      }
      const future = new Date(Date.now() + 31000);
      circuit = tryHalfOpen(circuit, future);

      expect(circuit.state).toBe('half-open');
      expect(canRequest(circuit)).toBe(true);
    });

    it('should block requests when open', () => {
      let circuit = createCircuitBreaker('backend-1');
      for (let i = 0; i < 5; i++) {
        circuit = recordFailure(circuit);
      }

      expect(circuit.state).toBe('open');
      expect(canRequest(circuit)).toBe(false);
    });

    it('should allow requests when open timeout expired', () => {
      let circuit = createCircuitBreaker('backend-1', { resetTimeoutMs: 1000 });
      for (let i = 0; i < 5; i++) {
        circuit = recordFailure(circuit);
      }

      const future = new Date(Date.now() + 2000);
      expect(canRequest(circuit, future)).toBe(true);
    });
  });

  describe('recordSuccess', () => {
    it('should reset failure count when closed', () => {
      let circuit = createCircuitBreaker('backend-1');
      circuit = recordFailure(circuit);
      circuit = recordFailure(circuit);

      circuit = recordSuccess(circuit);

      expect(circuit.failureCount).toBe(0);
    });

    it('should close circuit after success threshold in half-open', () => {
      let circuit = createCircuitBreaker('backend-1', {
        failureThreshold: 2,
        successThreshold: 2,
        resetTimeoutMs: 1000,
      });

      // Open the circuit
      circuit = recordFailure(circuit);
      circuit = recordFailure(circuit);
      expect(circuit.state).toBe('open');

      // Move to half-open
      circuit = tryHalfOpen(circuit, new Date(Date.now() + 2000));
      expect(circuit.state).toBe('half-open');

      // Record successes
      circuit = recordSuccess(circuit);
      expect(circuit.state).toBe('half-open');
      circuit = recordSuccess(circuit);
      expect(circuit.state).toBe('closed');
    });
  });

  describe('recordFailure', () => {
    it('should increment failure count', () => {
      let circuit = createCircuitBreaker('backend-1');

      circuit = recordFailure(circuit);
      expect(circuit.failureCount).toBe(1);

      circuit = recordFailure(circuit);
      expect(circuit.failureCount).toBe(2);
    });

    it('should open circuit at threshold', () => {
      let circuit = createCircuitBreaker('backend-1', { failureThreshold: 3 });

      circuit = recordFailure(circuit);
      circuit = recordFailure(circuit);
      expect(circuit.state).toBe('closed');

      circuit = recordFailure(circuit);
      expect(circuit.state).toBe('open');
    });

    it('should reopen circuit from half-open on failure', () => {
      let circuit = createCircuitBreaker('backend-1', {
        failureThreshold: 2,
        resetTimeoutMs: 1000,
      });

      circuit = recordFailure(circuit);
      circuit = recordFailure(circuit);
      circuit = tryHalfOpen(circuit, new Date(Date.now() + 2000));
      expect(circuit.state).toBe('half-open');

      circuit = recordFailure(circuit);
      expect(circuit.state).toBe('open');
    });
  });

  describe('tryHalfOpen', () => {
    it('should not change closed circuit', () => {
      const circuit = createCircuitBreaker('backend-1');
      const result = tryHalfOpen(circuit);

      expect(result.state).toBe('closed');
    });

    it('should transition to half-open after timeout', () => {
      let circuit = createCircuitBreaker('backend-1', {
        failureThreshold: 2,
        resetTimeoutMs: 5000,
      });

      circuit = recordFailure(circuit);
      circuit = recordFailure(circuit);
      expect(circuit.state).toBe('open');

      // Before timeout
      let result = tryHalfOpen(circuit, new Date(Date.now() + 3000));
      expect(result.state).toBe('open');

      // After timeout
      result = tryHalfOpen(circuit, new Date(Date.now() + 6000));
      expect(result.state).toBe('half-open');
    });
  });
});
