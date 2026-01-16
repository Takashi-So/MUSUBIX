// Custom Error Classes for Deep Research
// REQ: REQ-DR-NFR-005

/**
 * Base Error Class for Deep Research
 */
export class DeepResearchError extends Error {
  constructor(
    message: string,
    public readonly code: string,
    public readonly context?: Record<string, unknown>
  ) {
    super(message);
    this.name = 'DeepResearchError';
  }
}

/**
 * All Providers Failed Error
 * REQ: REQ-DR-NFR-005
 * Thrown when all search providers fail to return results
 */
export class AllProvidersFailedError extends DeepResearchError {
  constructor(message: string, context?: Record<string, unknown>) {
    super(message, 'ALL_PROVIDERS_FAILED', context);
    this.name = 'AllProvidersFailedError';
  }
}

/**
 * Token Budget Exceeded Error
 * REQ: REQ-DR-CORE-006, REQ-DR-NFR-005
 * Thrown when token usage exceeds the configured budget
 */
export class TokenBudgetExceededError extends DeepResearchError {
  constructor(
    public readonly used: number,
    public readonly budget: number
  ) {
    super(
      `Token budget exceeded: ${used}/${budget} tokens`,
      'TOKEN_BUDGET_EXCEEDED',
      { used, budget }
    );
    this.name = 'TokenBudgetExceededError';
  }
}

/**
 * LM API Timeout Error
 * REQ: REQ-DR-NFR-005
 * Thrown when LM API request times out
 */
export class LMAPITimeoutError extends DeepResearchError {
  constructor(
    public readonly timeoutMs: number,
    context?: Record<string, unknown>
  ) {
    super(
      `LM API request timed out after ${timeoutMs}ms`,
      'LM_API_TIMEOUT',
      { timeoutMs, ...context }
    );
    this.name = 'LMAPITimeoutError';
  }
}

/**
 * Content Sanitization Error
 * REQ: REQ-DR-NFR-004, REQ-DR-NFR-005
 * Thrown when content fails sanitization checks
 */
export class ContentSanitizationError extends DeepResearchError {
  constructor(
    message: string,
    public readonly url?: string,
    context?: Record<string, unknown>
  ) {
    super(message, 'CONTENT_SANITIZATION_FAILED', { url, ...context });
    this.name = 'ContentSanitizationError';
  }
}

/**
 * Invalid Configuration Error
 * REQ: REQ-DR-NFR-005
 * Thrown when configuration is invalid
 */
export class InvalidConfigurationError extends DeepResearchError {
  constructor(message: string, context?: Record<string, unknown>) {
    super(message, 'INVALID_CONFIGURATION', context);
    this.name = 'InvalidConfigurationError';
  }
}
