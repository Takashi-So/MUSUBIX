/**
 * Error Type Definitions for MUSUBIX
 * 
 * @packageDocumentation
 * @module types/errors
 * 
 * @see REQ-ERR-001 - Graceful Degradation
 * @see REQ-MNT-002 - Error Handler
 * @see DES-MUSUBIX-001 Section 10 - Error Handling Design
 */

import type { ID, Timestamp, Location } from './common.js';

// ============================================================================
// Error Codes
// ============================================================================

/**
 * MUSUBIX error codes
 */
export enum ErrorCode {
  // General errors (1xxx)
  UNKNOWN = 1000,
  INTERNAL = 1001,
  INVALID_ARGUMENT = 1002,
  NOT_FOUND = 1003,
  ALREADY_EXISTS = 1004,
  PERMISSION_DENIED = 1005,
  
  // Configuration errors (2xxx)
  CONFIG_NOT_FOUND = 2000,
  CONFIG_INVALID = 2001,
  CONFIG_MISSING_FIELD = 2002,
  
  // Integration errors (3xxx)
  LLM_CONNECTION_FAILED = 3000,
  LLM_RESPONSE_ERROR = 3001,
  LLM_RATE_LIMIT = 3002,
  /** @deprecated Use KNOWLEDGE_CONNECTION_FAILED */
  YATA_CONNECTION_FAILED = 3100,
  /** @deprecated Use KNOWLEDGE_QUERY_ERROR */
  YATA_QUERY_ERROR = 3101,
  /** @deprecated Use KNOWLEDGE_TIMEOUT */
  YATA_TIMEOUT = 3102,
  KNOWLEDGE_CONNECTION_FAILED = 3110,
  KNOWLEDGE_QUERY_ERROR = 3111,
  KNOWLEDGE_TIMEOUT = 3112,
  INTEGRATION_MISMATCH = 3200,
  CONTRADICTION_DETECTED = 3201,
  
  // Validation errors (4xxx)
  VALIDATION_FAILED = 4000,
  EARS_SYNTAX_ERROR = 4001,
  DESIGN_VIOLATION = 4002,
  CODE_QUALITY_ERROR = 4003,
  TEST_COVERAGE_LOW = 4004,
  
  // File system errors (5xxx)
  FILE_NOT_FOUND = 5000,
  FILE_READ_ERROR = 5001,
  FILE_WRITE_ERROR = 5002,
  DIRECTORY_NOT_FOUND = 5003,
  
  // CLI errors (6xxx)
  CLI_INVALID_COMMAND = 6000,
  CLI_MISSING_ARGUMENT = 6001,
  CLI_INVALID_OPTION = 6002,
}

// ============================================================================
// Base Error Class
// ============================================================================

/**
 * Base MUSUBIX error
 */
export interface MuSubixErrorData {
  /** Error code */
  code: ErrorCode;
  /** Human-readable message */
  message: string;
  /** Detailed description */
  details?: string;
  /** Timestamp */
  timestamp: Timestamp;
  /** Correlation ID for tracing */
  correlationId?: ID;
  /** Original error */
  cause?: Error;
  /** Location in source */
  location?: Location;
  /** Additional context */
  context?: Record<string, unknown>;
  /** Recovery suggestions */
  recovery?: RecoverySuggestion[];
}

/**
 * Recovery suggestion for errors
 */
export interface RecoverySuggestion {
  /** Suggestion type */
  type: RecoveryType;
  /** Description */
  description: string;
  /** Automated action available */
  automatable: boolean;
  /** Action command if automatable */
  action?: string;
}

/**
 * Recovery types
 */
export type RecoveryType =
  | 'retry'
  | 'fallback'
  | 'configure'
  | 'manual'
  | 'ignore';

// ============================================================================
// Specific Error Types
// ============================================================================

/**
 * Configuration error
 */
export interface ConfigurationError extends MuSubixErrorData {
  code: ErrorCode.CONFIG_NOT_FOUND | ErrorCode.CONFIG_INVALID | ErrorCode.CONFIG_MISSING_FIELD;
  configPath?: string;
  missingField?: string;
}

/**
 * Integration error
 */
export interface IntegrationError extends MuSubixErrorData {
  code: 
    | ErrorCode.LLM_CONNECTION_FAILED
    | ErrorCode.LLM_RESPONSE_ERROR
    | ErrorCode.LLM_RATE_LIMIT
    | ErrorCode.YATA_CONNECTION_FAILED
    | ErrorCode.YATA_QUERY_ERROR
    | ErrorCode.YATA_TIMEOUT
    | ErrorCode.KNOWLEDGE_CONNECTION_FAILED
    | ErrorCode.KNOWLEDGE_QUERY_ERROR
    | ErrorCode.KNOWLEDGE_TIMEOUT
    | ErrorCode.INTEGRATION_MISMATCH
    | ErrorCode.CONTRADICTION_DETECTED;
  service: 'llm' | 'knowledge' | 'integration';
  endpoint?: string;
  statusCode?: number;
}

/**
 * Validation error
 */
export interface ValidationError extends MuSubixErrorData {
  code:
    | ErrorCode.VALIDATION_FAILED
    | ErrorCode.EARS_SYNTAX_ERROR
    | ErrorCode.DESIGN_VIOLATION
    | ErrorCode.CODE_QUALITY_ERROR
    | ErrorCode.TEST_COVERAGE_LOW;
  validationType: string;
  violations: ValidationViolation[];
}

/**
 * Validation violation detail
 */
export interface ValidationViolation {
  /** Rule that was violated */
  rule: string;
  /** Violation message */
  message: string;
  /** Severity */
  severity: 'error' | 'warning' | 'info';
  /** Location */
  location?: Location;
  /** Suggestion */
  suggestion?: string;
}

/**
 * File system error
 */
export interface FileSystemError extends MuSubixErrorData {
  code:
    | ErrorCode.FILE_NOT_FOUND
    | ErrorCode.FILE_READ_ERROR
    | ErrorCode.FILE_WRITE_ERROR
    | ErrorCode.DIRECTORY_NOT_FOUND;
  path: string;
  operation: 'read' | 'write' | 'delete' | 'create';
}

/**
 * CLI error
 */
export interface CLIError extends MuSubixErrorData {
  code:
    | ErrorCode.CLI_INVALID_COMMAND
    | ErrorCode.CLI_MISSING_ARGUMENT
    | ErrorCode.CLI_INVALID_OPTION;
  command?: string;
  argument?: string;
  option?: string;
  usage?: string;
}

// ============================================================================
// Error Factory Types
// ============================================================================

/**
 * Error factory options
 */
export interface ErrorOptions {
  cause?: Error;
  details?: string;
  context?: Record<string, unknown>;
  recovery?: RecoverySuggestion[];
}

/**
 * Error severity levels
 */
export type ErrorSeverity = 'fatal' | 'error' | 'warn' | 'warning' | 'info';

/**
 * Error classification
 */
export interface ErrorClassification {
  /** Error category */
  category: ErrorCategory;
  /** Whether error is recoverable */
  recoverable: boolean;
  /** Whether to log error */
  shouldLog: boolean;
  /** Log level */
  logLevel: ErrorSeverity;
  /** Whether to report to user */
  userFacing: boolean;
}

/**
 * Error categories
 */
export type ErrorCategory =
  | 'configuration'
  | 'integration'
  | 'validation'
  | 'filesystem'
  | 'cli'
  | 'internal';
