/**
 * Error classes for musubix-library-learner
 */

/**
 * Base error class for library-learner errors
 */
export class LibraryLearnerError extends Error {
  constructor(
    message: string,
    public readonly code: string,
    public readonly cause?: Error
  ) {
    super(message);
    this.name = 'LibraryLearnerError';
    Error.captureStackTrace?.(this, this.constructor);
  }
}

/**
 * Error thrown when pattern mining fails
 */
export class PatternMiningError extends LibraryLearnerError {
  constructor(message: string, cause?: Error) {
    super(message, 'PATTERN_MINING_ERROR', cause);
    this.name = 'PatternMiningError';
  }
}

/**
 * Error thrown when abstraction fails
 */
export class AbstractionError extends LibraryLearnerError {
  constructor(message: string, cause?: Error) {
    super(message, 'ABSTRACTION_ERROR', cause);
    this.name = 'AbstractionError';
  }
}

/**
 * Error thrown when type analysis fails
 */
export class TypeAnalysisError extends LibraryLearnerError {
  constructor(message: string, cause?: Error) {
    super(message, 'TYPE_ANALYSIS_ERROR', cause);
    this.name = 'TypeAnalysisError';
  }
}

/**
 * Error thrown when library operations fail
 */
export class LibraryError extends LibraryLearnerError {
  constructor(message: string, cause?: Error) {
    super(message, 'LIBRARY_ERROR', cause);
    this.name = 'LibraryError';
  }
}

/**
 * Error thrown when E-graph operations fail
 */
export class EGraphError extends LibraryLearnerError {
  constructor(message: string, cause?: Error) {
    super(message, 'EGRAPH_ERROR', cause);
    this.name = 'EGraphError';
  }
}

/**
 * Error thrown when synthesis fails
 */
export class SynthesisError extends LibraryLearnerError {
  constructor(message: string, cause?: Error) {
    super(message, 'SYNTHESIS_ERROR', cause);
    this.name = 'SynthesisError';
  }
}

/**
 * Error thrown when validation fails
 */
export class ValidationError extends LibraryLearnerError {
  constructor(message: string, cause?: Error) {
    super(message, 'VALIDATION_ERROR', cause);
    this.name = 'ValidationError';
  }
}

/**
 * Error thrown when a pattern is not found
 */
export class PatternNotFoundError extends LibraryLearnerError {
  constructor(patternId: string) {
    super(`Pattern not found: ${patternId}`, 'PATTERN_NOT_FOUND');
    this.name = 'PatternNotFoundError';
  }
}

/**
 * Error thrown when operation times out
 */
export class TimeoutError extends LibraryLearnerError {
  constructor(operation: string, timeout: number) {
    super(`Operation '${operation}' timed out after ${timeout}ms`, 'TIMEOUT');
    this.name = 'TimeoutError';
  }
}
