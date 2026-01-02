/**
 * Error Handler Utility
 * 
 * Provides structured error handling, classification, and recovery
 * 
 * @packageDocumentation
 * @module utils/error-handler
 * 
 * @see REQ-MNT-002 - Error Handler
 * @see REQ-ERR-001 - Graceful Degradation
 * @see DES-MUSUBIX-001 Section 16.2 - Error Handler Design
 */

import {
  ErrorCode,
  type MuSubixErrorData,
  type RecoverySuggestion,
  type ErrorClassification,
  type ErrorSeverity,
} from '../types/errors.js';
import { logger, type Logger } from './logger.js';

/**
 * MUSUBIX Error class
 */
export class MuSubixError extends Error {
  public readonly code: ErrorCode;
  public readonly timestamp: string;
  public readonly correlationId?: string;
  public readonly details?: string;
  public readonly context?: Record<string, unknown>;
  public readonly recovery?: RecoverySuggestion[];

  constructor(
    code: ErrorCode,
    message: string,
    options?: {
      cause?: Error;
      details?: string;
      correlationId?: string;
      context?: Record<string, unknown>;
      recovery?: RecoverySuggestion[];
    }
  ) {
    super(message, { cause: options?.cause });
    this.name = 'MuSubixError';
    this.code = code;
    this.timestamp = new Date().toISOString();
    this.details = options?.details;
    this.correlationId = options?.correlationId;
    this.context = options?.context;
    this.recovery = options?.recovery;
  }

  /**
   * Convert to error data structure
   */
  toErrorData(): MuSubixErrorData {
    return {
      code: this.code,
      message: this.message,
      details: this.details,
      timestamp: this.timestamp,
      correlationId: this.correlationId,
      cause: this.cause instanceof Error ? this.cause : undefined,
      context: this.context,
      recovery: this.recovery,
    };
  }

  /**
   * Convert to JSON
   */
  toJSON(): Record<string, unknown> {
    return {
      name: this.name,
      code: this.code,
      message: this.message,
      details: this.details,
      timestamp: this.timestamp,
      correlationId: this.correlationId,
      context: this.context,
      recovery: this.recovery,
      stack: this.stack,
    };
  }
}

/**
 * Error classification rules
 */
const ERROR_CLASSIFICATIONS: Record<number, ErrorClassification> = {
  // Configuration errors - recoverable by fixing config
  [ErrorCode.CONFIG_NOT_FOUND]: {
    category: 'configuration',
    recoverable: true,
    shouldLog: true,
    logLevel: 'error',
    userFacing: true,
  },
  [ErrorCode.CONFIG_INVALID]: {
    category: 'configuration',
    recoverable: true,
    shouldLog: true,
    logLevel: 'error',
    userFacing: true,
  },
  
  // Integration errors - may need retry or fallback
  [ErrorCode.LLM_CONNECTION_FAILED]: {
    category: 'integration',
    recoverable: true,
    shouldLog: true,
    logLevel: 'error',
    userFacing: true,
  },
  [ErrorCode.LLM_RATE_LIMIT]: {
    category: 'integration',
    recoverable: true,
    shouldLog: true,
    logLevel: 'warn',
    userFacing: true,
  },
  [ErrorCode.YATA_CONNECTION_FAILED]: {
    category: 'integration',
    recoverable: true,
    shouldLog: true,
    logLevel: 'error',
    userFacing: true,
  },
  
  // Validation errors - user needs to fix input
  [ErrorCode.VALIDATION_FAILED]: {
    category: 'validation',
    recoverable: true,
    shouldLog: true,
    logLevel: 'warn',
    userFacing: true,
  },
  [ErrorCode.EARS_SYNTAX_ERROR]: {
    category: 'validation',
    recoverable: true,
    shouldLog: true,
    logLevel: 'warn',
    userFacing: true,
  },
  
  // File system errors
  [ErrorCode.FILE_NOT_FOUND]: {
    category: 'filesystem',
    recoverable: true,
    shouldLog: true,
    logLevel: 'error',
    userFacing: true,
  },
  
  // Internal errors - not recoverable
  [ErrorCode.INTERNAL]: {
    category: 'internal',
    recoverable: false,
    shouldLog: true,
    logLevel: 'fatal',
    userFacing: false,
  },
};

/**
 * Default error classification
 */
const DEFAULT_CLASSIFICATION: ErrorClassification = {
  category: 'internal',
  recoverable: false,
  shouldLog: true,
  logLevel: 'error',
  userFacing: true,
};

/**
 * Error Handler class
 */
export class ErrorHandler {
  private log: Logger;
  private fallbackHandler?: (error: MuSubixError) => void;

  constructor(context?: string) {
    this.log = context ? logger.child(context) : logger.child('error-handler');
  }

  /**
   * Set fallback handler for graceful degradation
   */
  setFallback(handler: (error: MuSubixError) => void): void {
    this.fallbackHandler = handler;
  }

  /**
   * Handle an error
   */
  handle(error: unknown): MuSubixError {
    const musubixError = this.normalize(error);
    const classification = this.classify(musubixError);

    // Log if needed
    if (classification.shouldLog) {
      this.logError(musubixError, classification.logLevel);
    }

    // Try recovery if possible
    if (classification.recoverable && this.fallbackHandler) {
      try {
        this.fallbackHandler(musubixError);
      } catch (fallbackError) {
        this.log.error('Fallback handler failed', fallbackError as Error);
      }
    }

    return musubixError;
  }

  /**
   * Normalize any error to MuSubixError
   */
  normalize(error: unknown): MuSubixError {
    if (error instanceof MuSubixError) {
      return error;
    }

    if (error instanceof Error) {
      return new MuSubixError(ErrorCode.UNKNOWN, error.message, {
        cause: error,
        details: error.stack,
      });
    }

    return new MuSubixError(
      ErrorCode.UNKNOWN,
      typeof error === 'string' ? error : 'An unknown error occurred',
      { context: { originalError: error } }
    );
  }

  /**
   * Classify an error
   */
  classify(error: MuSubixError): ErrorClassification {
    return ERROR_CLASSIFICATIONS[error.code] ?? DEFAULT_CLASSIFICATION;
  }

  /**
   * Log error with appropriate level
   */
  private logError(error: MuSubixError, level: ErrorSeverity): void {
    const data = {
      code: error.code,
      correlationId: error.correlationId,
      context: error.context,
    };

    switch (level) {
      case 'fatal':
        this.log.fatal(error.message, error, data);
        break;
      case 'error':
        this.log.error(error.message, error, data);
        break;
      case 'warning':
        this.log.warn(error.message, data);
        break;
      default:
        this.log.info(error.message, data);
    }
  }

  /**
   * Wrap async function with error handling
   */
  wrap<T, Args extends unknown[]>(
    fn: (...args: Args) => Promise<T>
  ): (...args: Args) => Promise<T> {
    return async (...args: Args): Promise<T> => {
      try {
        return await fn(...args);
      } catch (error) {
        throw this.handle(error);
      }
    };
  }

  /**
   * Try operation with fallback
   */
  async tryWithFallback<T>(
    operation: () => Promise<T>,
    fallback: () => Promise<T>
  ): Promise<T> {
    try {
      return await operation();
    } catch (error) {
      this.handle(error);
      this.log.warn('Attempting fallback due to error');
      return fallback();
    }
  }
}

/**
 * Create common recovery suggestions
 */
export const RecoverySuggestions = {
  retry: (description = 'Retry the operation'): RecoverySuggestion => ({
    type: 'retry',
    description,
    automatable: true,
    action: 'retry',
  }),
  
  configure: (field: string): RecoverySuggestion => ({
    type: 'configure',
    description: `Configure ${field} in musubix.config.json`,
    automatable: false,
  }),
  
  fallback: (description: string): RecoverySuggestion => ({
    type: 'fallback',
    description,
    automatable: true,
    action: 'fallback',
  }),
  
  manual: (description: string): RecoverySuggestion => ({
    type: 'manual',
    description,
    automatable: false,
  }),
};

/**
 * Error factory functions
 */
export const Errors = {
  configNotFound: (path: string): MuSubixError =>
    new MuSubixError(ErrorCode.CONFIG_NOT_FOUND, `Configuration file not found: ${path}`, {
      context: { path },
      recovery: [RecoverySuggestions.manual('Run "musubix init" to create configuration')],
    }),

  configInvalid: (message: string, path?: string): MuSubixError =>
    new MuSubixError(ErrorCode.CONFIG_INVALID, message, {
      context: { path },
      recovery: [RecoverySuggestions.configure('the invalid field')],
    }),

  llmConnectionFailed: (endpoint: string, cause?: Error): MuSubixError =>
    new MuSubixError(ErrorCode.LLM_CONNECTION_FAILED, `Failed to connect to LLM: ${endpoint}`, {
      cause,
      context: { endpoint },
      recovery: [
        RecoverySuggestions.retry(),
        RecoverySuggestions.configure('llm.endpoint'),
      ],
    }),

  yataConnectionFailed: (cause?: Error): MuSubixError =>
    new MuSubixError(ErrorCode.YATA_CONNECTION_FAILED, 'Failed to connect to YATA MCP server', {
      cause,
      recovery: [
        RecoverySuggestions.retry(),
        RecoverySuggestions.fallback('Continue with neural-only mode'),
      ],
    }),

  validationFailed: (violations: string[]): MuSubixError =>
    new MuSubixError(ErrorCode.VALIDATION_FAILED, 'Validation failed', {
      details: violations.join('\n'),
      context: { violationCount: violations.length },
    }),

  fileNotFound: (path: string): MuSubixError =>
    new MuSubixError(ErrorCode.FILE_NOT_FOUND, `File not found: ${path}`, {
      context: { path },
    }),

  internal: (message: string, cause?: Error): MuSubixError =>
    new MuSubixError(ErrorCode.INTERNAL, message, { cause }),
};

/**
 * Global error handler instance
 */
export const errorHandler = new ErrorHandler();
