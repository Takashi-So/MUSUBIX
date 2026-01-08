/**
 * Neural Search Errors
 * @module @nahisaho/musubix-neural-search
 */

/**
 * Base error for neural search
 */
export class NeuralSearchError extends Error {
  constructor(message: string, public readonly code: string) {
    super(message);
    this.name = 'NeuralSearchError';
  }
}

/**
 * Embedding error
 */
export class EmbeddingError extends NeuralSearchError {
  constructor(message: string) {
    super(message, 'EMBEDDING_ERROR');
    this.name = 'EmbeddingError';
  }
}

/**
 * Search error
 */
export class SearchError extends NeuralSearchError {
  constructor(message: string) {
    super(message, 'SEARCH_ERROR');
    this.name = 'SearchError';
  }
}

/**
 * Search timeout error
 */
export class SearchTimeoutError extends SearchError {
  constructor(timeout: number) {
    super(`Search timed out after ${timeout}ms`);
    this.name = 'SearchTimeoutError';
  }
}

/**
 * Search depth exceeded error
 */
export class SearchDepthExceededError extends SearchError {
  constructor(maxDepth: number) {
    super(`Maximum search depth ${maxDepth} exceeded`);
    this.name = 'SearchDepthExceededError';
  }
}

/**
 * Learning error
 */
export class LearningError extends NeuralSearchError {
  constructor(message: string) {
    super(message, 'LEARNING_ERROR');
    this.name = 'LearningError';
  }
}

/**
 * Invalid state error
 */
export class InvalidStateError extends NeuralSearchError {
  constructor(message: string) {
    super(message, 'INVALID_STATE');
    this.name = 'InvalidStateError';
  }
}
