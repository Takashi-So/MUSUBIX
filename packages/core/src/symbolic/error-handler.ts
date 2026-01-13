/**
 * Error Handler
 *
 * Provides graceful degradation and fallback mechanisms
 * for symbolic reasoning components.
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-ERR-001 - Error Handling Strategy
 * @see DES-SYMB-001 §4.16 - ErrorHandlingStrategy
 * @see TSK-SYMB-007
 */

import type {
  ErrorHandlingStrategy,
  FallbackAction,
  AuditLogEntry,
  Explanation,
} from './types.js';

/**
 * Error severity levels
 */
export type ErrorSeverity = 'recoverable' | 'degraded' | 'fatal';

/**
 * Error classification result
 */
export interface ErrorClassification {
  severity: ErrorSeverity;
  category: string;
  recoverable: boolean;
  fallbackAvailable: boolean;
}

/**
 * Recovery result
 */
export interface RecoveryResult {
  success: boolean;
  fallbackUsed?: FallbackAction;
  explanation: Explanation;
  auditEntry: AuditLogEntry;
}

/**
 * Error handler configuration
 */
export interface ErrorHandlerConfig {
  enableGracefulDegradation: boolean;
  enableAuditLogging: boolean;
  maxRetryAttempts: number;
  retryDelayMs: number;
}

/**
 * Default configuration
 */
export const DEFAULT_ERROR_HANDLER_CONFIG: ErrorHandlerConfig = {
  enableGracefulDegradation: true,
  enableAuditLogging: true,
  maxRetryAttempts: 3,
  retryDelayMs: 1000,
};

/**
 * Error Handler
 */
export class ErrorHandler {
  private readonly config: ErrorHandlerConfig;
  private readonly auditLog: AuditLogEntry[] = [];

  constructor(config: Partial<ErrorHandlerConfig> = {}) {
    this.config = { ...DEFAULT_ERROR_HANDLER_CONFIG, ...config };
  }

  /**
   * Handle an error with graceful degradation
   */
  async handleError(
    error: Error,
    context: { component: string; operation: string; input?: unknown },
  ): Promise<RecoveryResult> {
    const classification = this.classifyError(error);
    const strategy = this.selectStrategy(classification);
    const fallback = this.selectFallback(classification, context);

    const auditEntry = this.createAuditEntry(error, context, classification, fallback);
    if (this.config.enableAuditLogging) {
      this.auditLog.push(auditEntry);
    }

    if (classification.recoverable && this.config.enableGracefulDegradation) {
      const recovered = await this.attemptRecovery(strategy, fallback);
      if (recovered) {
        return {
          success: true,
          fallbackUsed: fallback,
          explanation: this.buildRecoveryExplanation(classification, fallback),
          auditEntry,
        };
      }
    }

    return {
      success: false,
      explanation: this.buildFailureExplanation(error, classification),
      auditEntry,
    };
  }

  /**
   * Classify an error by severity and recoverability
   */
  classifyError(error: Error): ErrorClassification {
    const message = error.message.toLowerCase();
    const name = error.name.toLowerCase();

    if (
      name === 'typeerror' ||
      name === 'referenceerror' ||
      message.includes('cannot read') ||
      message.includes('is not defined')
    ) {
      return {
        severity: 'fatal',
        category: 'programming_error',
        recoverable: false,
        fallbackAvailable: false,
      };
    }

    if (
      message.includes('timeout') ||
      message.includes('network') ||
      message.includes('connection')
    ) {
      return {
        severity: 'degraded',
        category: 'network_error',
        recoverable: true,
        fallbackAvailable: true,
      };
    }

    if (message.includes('not found') || message.includes('missing')) {
      return {
        severity: 'degraded',
        category: 'resource_error',
        recoverable: true,
        fallbackAvailable: true,
      };
    }

    if (
      message.includes('validation') ||
      message.includes('invalid') ||
      message.includes('format')
    ) {
      return {
        severity: 'recoverable',
        category: 'validation_error',
        recoverable: true,
        fallbackAvailable: true,
      };
    }

    return {
      severity: 'degraded',
      category: 'unknown_error',
      recoverable: true,
      fallbackAvailable: true,
    };
  }

  private selectStrategy(classification: ErrorClassification): ErrorHandlingStrategy {
    switch (classification.severity) {
      case 'fatal':
        return 'fail_fast';
      case 'degraded':
        return classification.fallbackAvailable ? 'graceful_degradation' : 'retry_with_backoff';
      case 'recoverable':
        return 'retry_with_backoff';
    }
  }

  private selectFallback(
    classification: ErrorClassification,
    context: { component: string },
  ): FallbackAction {
    if (!classification.fallbackAvailable) {
      return 'none';
    }

    switch (context.component) {
      case 'HallucinationDetector':
        return 'skip_hallucination_check';
      case 'ConstitutionRegistry':
        return 'apply_default_rules';
      case 'ConfidenceEstimator':
        return 'use_default_confidence';
      case 'KnowledgeStore':
        return 'use_cached_response';
      default:
        return classification.severity === 'degraded' ? 'use_cached_response' : 'none';
    }
  }

  private async attemptRecovery(
    strategy: ErrorHandlingStrategy,
    fallback: FallbackAction,
  ): Promise<boolean> {
    if (strategy === 'fail_fast') {
      return false;
    }

    if (strategy === 'graceful_degradation' && fallback !== 'none') {
      return true;
    }

    if (strategy === 'retry_with_backoff') {
      for (let attempt = 0; attempt < this.config.maxRetryAttempts; attempt++) {
        await this.delay(this.config.retryDelayMs * Math.pow(2, attempt));
        if (fallback !== 'none') {
          return true;
        }
      }
    }

    return false;
  }

  private createAuditEntry(
    error: Error,
    context: { component: string; operation: string },
    classification: ErrorClassification,
    fallback: FallbackAction,
  ): AuditLogEntry {
    return {
      id: `AUDIT-${Date.now()}-${Math.random().toString(36).substring(2, 9)}`,
      timestamp: new Date().toISOString(),
      component: context.component,
      operation: context.operation,
      result: classification.recoverable ? 'partial' : 'fail',
      details: {
        error: { name: error.name, message: error.message },
        classification,
        fallbackUsed: fallback,
      },
    };
  }

  private buildRecoveryExplanation(
    classification: ErrorClassification,
    fallback: FallbackAction,
  ): Explanation {
    return {
      summary: `Recovered from ${classification.category} using ${fallback}`,
      reasoning: [
        `Error severity: ${classification.severity}`,
        `Recovery method: graceful degradation`,
        `Fallback action: ${fallback}`,
      ],
      evidence: [
        {
          type: 'rule_match',
          description: `Applied fallback: ${fallback}`,
          artifacts: [],
          confidence: 0.8,
        },
      ],
      relatedRequirements: ['REQ-ERR-001'],
    };
  }

  private buildFailureExplanation(
    error: Error,
    classification: ErrorClassification,
  ): Explanation {
    return {
      summary: `Unrecoverable ${classification.category}: ${error.message}`,
      reasoning: [
        `Error severity: ${classification.severity}`,
        `Category: ${classification.category}`,
        `Error: ${error.message}`,
      ],
      evidence: [
        {
          type: 'rule_match',
          description: `Error: ${error.name}`,
          artifacts: [],
          confidence: 0,
        },
      ],
      relatedRequirements: ['REQ-ERR-001'],
    };
  }

  getAuditLog(): AuditLogEntry[] {
    return [...this.auditLog];
  }

  clearAuditLog(): void {
    this.auditLog.length = 0;
  }

  getRecentErrors(count: number = 10): AuditLogEntry[] {
    return this.auditLog.slice(-count);
  }

  private delay(ms: number): Promise<void> {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }
}

/**
 * Factory function
 */
export function createErrorHandler(config?: Partial<ErrorHandlerConfig>): ErrorHandler {
  return new ErrorHandler(config);
}

/**
 * Wrap an async function with error handling
 */
export function withErrorHandling<T>(
  handler: ErrorHandler,
  component: string,
  operation: string,
  fn: () => Promise<T>,
  defaultValue?: T,
): Promise<T> {
  return fn().catch(async (error: Error) => {
    const result = await handler.handleError(error, { component, operation });
    if (result.success && defaultValue !== undefined) {
      return defaultValue;
    }
    throw error;
  });
}
