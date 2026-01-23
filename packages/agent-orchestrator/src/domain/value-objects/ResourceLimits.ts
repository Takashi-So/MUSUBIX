/**
 * ResourceLimits Value Object
 *
 * Defines resource limits for agent operations.
 *
 * @see TSK-FR-001 - ResourceLimiter型定義
 * @see REQ-FR-060〜063 - ResourceLimiter
 * @trace DES-MUSUBIX-FR-001 DES-ORCH-002
 */

/**
 * Resource limit configuration
 * Defines maximum allowed resources per session/operation
 */
export interface ResourceLimits {
  /** Maximum number of API calls per session */
  readonly maxApiCalls: number;
  /** Maximum tokens allowed per session */
  readonly maxTokens: number;
  /** Maximum execution time in milliseconds */
  readonly maxExecutionTimeMs: number;
  /** Maximum number of concurrent operations */
  readonly maxConcurrentOperations: number;
  /** Maximum number of file operations */
  readonly maxFileOperations: number;
}

/**
 * Current resource usage snapshot
 */
export interface ResourceUsage {
  /** Number of API calls made */
  readonly apiCalls: number;
  /** Tokens consumed */
  readonly tokensUsed: number;
  /** Execution time elapsed in milliseconds */
  readonly executionTimeMs: number;
  /** Current concurrent operations */
  readonly concurrentOperations: number;
  /** File operations performed */
  readonly fileOperations: number;
  /** Timestamp of last update */
  readonly lastUpdated: Date;
}

/**
 * Resource limit check result
 */
export interface ResourceLimitCheckResult {
  /** Whether all limits are within bounds */
  readonly withinLimits: boolean;
  /** Exceeded limits (if any) */
  readonly exceededLimits: readonly ExceededLimit[];
  /** Warning limits approaching threshold */
  readonly warnings: readonly ResourceWarning[];
  /** Current usage snapshot */
  readonly usage: ResourceUsage;
}

/**
 * Information about an exceeded limit
 */
export interface ExceededLimit {
  /** Resource type that exceeded limit */
  readonly resource: keyof ResourceLimits;
  /** Current value */
  readonly current: number;
  /** Maximum allowed value */
  readonly limit: number;
  /** Percentage over limit */
  readonly percentageOver: number;
}

/**
 * Warning for resource approaching limit
 */
export interface ResourceWarning {
  /** Resource type approaching limit */
  readonly resource: keyof ResourceLimits;
  /** Current value */
  readonly current: number;
  /** Maximum allowed value */
  readonly limit: number;
  /** Percentage of limit used */
  readonly percentageUsed: number;
}

/**
 * ResourceLimiter configuration
 */
export interface ResourceLimiterConfig {
  /** Resource limits */
  readonly limits: ResourceLimits;
  /** Warning threshold percentage (default: 80) */
  readonly warningThreshold?: number;
  /** Whether to throw on limit exceeded (default: false) */
  readonly throwOnExceeded?: boolean;
}

/**
 * Default resource limits
 */
export const DEFAULT_RESOURCE_LIMITS: ResourceLimits = Object.freeze({
  maxApiCalls: 100,
  maxTokens: 100000,
  maxExecutionTimeMs: 300000, // 5 minutes
  maxConcurrentOperations: 5,
  maxFileOperations: 50,
});

/**
 * Create resource limits with defaults
 *
 * @param overrides - Partial limits to override defaults
 * @returns Complete ResourceLimits
 */
export function createResourceLimits(
  overrides: Partial<ResourceLimits> = {}
): ResourceLimits {
  return Object.freeze({
    ...DEFAULT_RESOURCE_LIMITS,
    ...overrides,
  });
}

/**
 * Create initial resource usage (all zeros)
 *
 * @returns Initial ResourceUsage
 */
export function createInitialUsage(): ResourceUsage {
  return Object.freeze({
    apiCalls: 0,
    tokensUsed: 0,
    executionTimeMs: 0,
    concurrentOperations: 0,
    fileOperations: 0,
    lastUpdated: new Date(),
  });
}

/**
 * Create ResourceLimiter configuration
 *
 * @param limits - Resource limits
 * @param options - Additional options
 * @returns ResourceLimiterConfig
 */
export function createResourceLimiterConfig(
  limits: Partial<ResourceLimits> = {},
  options: { warningThreshold?: number; throwOnExceeded?: boolean } = {}
): ResourceLimiterConfig {
  return Object.freeze({
    limits: createResourceLimits(limits),
    warningThreshold: options.warningThreshold ?? 80,
    throwOnExceeded: options.throwOnExceeded ?? false,
  });
}
