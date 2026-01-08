/**
 * Errors for MUSUBIX Synthesis
 * @module @nahisaho/musubix-synthesis
 */

/**
 * Base synthesis error
 */
export class SynthesisError extends Error {
  readonly code: string;

  constructor(message: string, code: string = 'SYNTHESIS_ERROR') {
    super(message);
    this.name = 'SynthesisError';
    this.code = code;
  }
}

/**
 * DSL error
 */
export class DSLError extends SynthesisError {
  constructor(message: string) {
    super(message, 'DSL_ERROR');
    this.name = 'DSLError';
  }
}

/**
 * DSL operator not found
 */
export class OperatorNotFoundError extends DSLError {
  readonly operatorName: string;

  constructor(operatorName: string) {
    super(`Unknown operator: ${operatorName}`);
    this.name = 'OperatorNotFoundError';
    this.operatorName = operatorName;
  }
}

/**
 * Type error
 */
export class TypeError extends SynthesisError {
  readonly expected?: string;
  readonly actual?: string;

  constructor(message: string, expected?: string, actual?: string) {
    super(message, 'TYPE_ERROR');
    this.name = 'TypeError';
    this.expected = expected;
    this.actual = actual;
  }
}

/**
 * Type mismatch error
 */
export class TypeMismatchError extends TypeError {
  constructor(expected: string, actual: string) {
    super(`Type mismatch: expected ${expected}, got ${actual}`, expected, actual);
    this.name = 'TypeMismatchError';
  }
}

/**
 * Synthesis failure error
 */
export class SynthesisFailureError extends SynthesisError {
  readonly reason: string;

  constructor(reason: string) {
    super(`Synthesis failed: ${reason}`, 'SYNTHESIS_FAILURE');
    this.name = 'SynthesisFailureError';
    this.reason = reason;
  }
}

/**
 * Synthesis timeout error
 */
export class SynthesisTimeoutError extends SynthesisError {
  readonly timeout: number;

  constructor(timeout: number) {
    super(`Synthesis timed out after ${timeout}ms`, 'SYNTHESIS_TIMEOUT');
    this.name = 'SynthesisTimeoutError';
    this.timeout = timeout;
  }
}

/**
 * Depth exceeded error
 */
export class DepthExceededError extends SynthesisError {
  readonly maxDepth: number;

  constructor(maxDepth: number) {
    super(`Maximum depth ${maxDepth} exceeded`, 'DEPTH_EXCEEDED');
    this.name = 'DepthExceededError';
    this.maxDepth = maxDepth;
  }
}

/**
 * No solution error
 */
export class NoSolutionError extends SynthesisError {
  constructor(message: string = 'No solution found') {
    super(message, 'NO_SOLUTION');
    this.name = 'NoSolutionError';
  }
}

/**
 * Invalid example error
 */
export class InvalidExampleError extends SynthesisError {
  readonly exampleIndex: number;

  constructor(exampleIndex: number, reason: string) {
    super(`Invalid example at index ${exampleIndex}: ${reason}`, 'INVALID_EXAMPLE');
    this.name = 'InvalidExampleError';
    this.exampleIndex = exampleIndex;
  }
}

/**
 * Rule error
 */
export class RuleError extends SynthesisError {
  constructor(message: string) {
    super(message, 'RULE_ERROR');
    this.name = 'RuleError';
  }
}

/**
 * Rule not found error
 */
export class RuleNotFoundError extends RuleError {
  readonly ruleId: string;

  constructor(ruleId: string) {
    super(`Rule not found: ${ruleId}`);
    this.name = 'RuleNotFoundError';
    this.ruleId = ruleId;
  }
}

/**
 * Execution error
 */
export class ExecutionError extends SynthesisError {
  readonly program?: string;

  constructor(message: string, program?: string) {
    super(message, 'EXECUTION_ERROR');
    this.name = 'ExecutionError';
    this.program = program;
  }
}
