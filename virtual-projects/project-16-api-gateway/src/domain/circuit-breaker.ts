// REQ-ROUTE-004: Circuit Breaker
// Traces to: DES-ROUTE-004

/**
 * Circuit breaker states
 * @requirement REQ-ROUTE-004
 */
export type CircuitState = 'closed' | 'open' | 'half-open';

/**
 * Circuit breaker configuration
 */
export interface CircuitBreakerConfig {
  failureThreshold: number; // Failures before opening
  successThreshold: number; // Successes to close from half-open
  resetTimeoutMs: number; // Time before half-open from open
}

/**
 * Circuit breaker entity
 * @requirement REQ-ROUTE-004
 */
export interface CircuitBreaker {
  backendId: string;
  state: CircuitState;
  failureCount: number;
  successCount: number;
  lastFailureTime?: Date;
  lastStateChangeTime: Date;
  config: CircuitBreakerConfig;
}

/**
 * Default circuit breaker configuration
 */
export const DEFAULT_CIRCUIT_CONFIG: CircuitBreakerConfig = {
  failureThreshold: 5,
  successThreshold: 2,
  resetTimeoutMs: 30000, // 30 seconds
};

/**
 * Create circuit breaker for backend
 * @requirement REQ-ROUTE-004
 */
export function createCircuitBreaker(
  backendId: string,
  config: Partial<CircuitBreakerConfig> = {}
): CircuitBreaker {
  return {
    backendId,
    state: 'closed',
    failureCount: 0,
    successCount: 0,
    lastStateChangeTime: new Date(),
    config: { ...DEFAULT_CIRCUIT_CONFIG, ...config },
  };
}

/**
 * Check if circuit allows requests
 * @requirement REQ-ROUTE-004
 */
export function canRequest(circuit: CircuitBreaker, now: Date = new Date()): boolean {
  if (circuit.state === 'closed') {
    return true;
  }

  if (circuit.state === 'half-open') {
    return true; // Allow test request
  }

  // State is 'open'
  const timeSinceChange = now.getTime() - circuit.lastStateChangeTime.getTime();
  if (timeSinceChange >= circuit.config.resetTimeoutMs) {
    // Should transition to half-open
    return true;
  }

  return false;
}

/**
 * Record successful request
 * @requirement REQ-ROUTE-004
 */
export function recordSuccess(circuit: CircuitBreaker): CircuitBreaker {
  const now = new Date();

  if (circuit.state === 'closed') {
    // Reset failure count on success
    return {
      ...circuit,
      failureCount: 0,
    };
  }

  if (circuit.state === 'half-open') {
    const newSuccessCount = circuit.successCount + 1;
    if (newSuccessCount >= circuit.config.successThreshold) {
      // Close the circuit
      return {
        ...circuit,
        state: 'closed',
        failureCount: 0,
        successCount: 0,
        lastStateChangeTime: now,
      };
    }
    return {
      ...circuit,
      successCount: newSuccessCount,
    };
  }

  return circuit;
}

/**
 * Record failed request
 * @requirement REQ-ROUTE-004
 */
export function recordFailure(circuit: CircuitBreaker): CircuitBreaker {
  const now = new Date();

  if (circuit.state === 'closed') {
    const newFailureCount = circuit.failureCount + 1;
    if (newFailureCount >= circuit.config.failureThreshold) {
      // Open the circuit
      return {
        ...circuit,
        state: 'open',
        failureCount: newFailureCount,
        successCount: 0,
        lastFailureTime: now,
        lastStateChangeTime: now,
      };
    }
    return {
      ...circuit,
      failureCount: newFailureCount,
      lastFailureTime: now,
    };
  }

  if (circuit.state === 'half-open') {
    // Any failure opens the circuit again
    return {
      ...circuit,
      state: 'open',
      successCount: 0,
      lastFailureTime: now,
      lastStateChangeTime: now,
    };
  }

  return circuit;
}

/**
 * Transition to half-open if timeout expired
 * @requirement REQ-ROUTE-004
 */
export function tryHalfOpen(circuit: CircuitBreaker, now: Date = new Date()): CircuitBreaker {
  if (circuit.state !== 'open') {
    return circuit;
  }

  const timeSinceChange = now.getTime() - circuit.lastStateChangeTime.getTime();
  if (timeSinceChange >= circuit.config.resetTimeoutMs) {
    return {
      ...circuit,
      state: 'half-open',
      successCount: 0,
      lastStateChangeTime: now,
    };
  }

  return circuit;
}
