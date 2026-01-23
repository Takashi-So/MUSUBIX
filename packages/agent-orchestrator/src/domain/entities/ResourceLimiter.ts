/**
 * ResourceLimiter Entity
 *
 * Manages and enforces resource limits for agent operations.
 * Prevents runaway operations by tracking API calls, tokens, time, etc.
 *
 * @see TSK-FR-001〜006 - ResourceLimiter
 * @see REQ-FR-060〜063 - ResourceLimiter
 * @trace DES-MUSUBIX-FR-001 DES-ORCH-002
 */

import {
  type ResourceLimits,
  type ResourceUsage,
  type ResourceLimitCheckResult,
  type ExceededLimit,
  type ResourceWarning,
  type ResourceLimiterConfig,
  createResourceLimits,
  createInitialUsage,
} from '../value-objects/ResourceLimits.js';

/**
 * Resource Limiter Interface
 */
export interface IResourceLimiter {
  /** Check if current usage is within limits */
  checkLimits(): ResourceLimitCheckResult;

  /** Record an API call */
  recordApiCall(): void;

  /** Record tokens consumed */
  recordTokens(count: number): void;

  /** Record a file operation */
  recordFileOperation(): void;

  /** Record execution time */
  recordExecutionTime(ms: number): void;

  /** Start tracking a concurrent operation */
  startConcurrentOperation(): void;

  /** End tracking a concurrent operation */
  endConcurrentOperation(): void;

  /** Get current usage snapshot */
  getUsage(): ResourceUsage;

  /** Get formatted usage report */
  getUsageReport(): string;

  /** Reset all usage counters */
  reset(): void;
}

/**
 * Resource Limiter Implementation
 *
 * Tracks resource usage and enforces limits to prevent runaway operations.
 *
 * @example
 * ```typescript
 * const limiter = createResourceLimiter();
 *
 * limiter.recordApiCall();
 * limiter.recordTokens(1500);
 *
 * const result = limiter.checkLimits();
 * if (!result.withinLimits) {
 *   console.error('Resource limits exceeded:', result.exceededLimits);
 * }
 * ```
 */
export class ResourceLimiter implements IResourceLimiter {
  private readonly limits: ResourceLimits;
  private readonly warningThreshold: number;
  private readonly throwOnExceeded: boolean;

  // Mutable state
  private apiCalls: number = 0;
  private tokensUsed: number = 0;
  private executionTimeMs: number = 0;
  private concurrentOperations: number = 0;
  private fileOperations: number = 0;
  private lastUpdated: Date = new Date();

  constructor(config?: ResourceLimiterConfig) {
    this.limits = config?.limits ?? createResourceLimits();
    this.warningThreshold = config?.warningThreshold ?? 80;
    this.throwOnExceeded = config?.throwOnExceeded ?? false;
  }

  /**
   * Check if current usage is within limits
   */
  checkLimits(): ResourceLimitCheckResult {
    const usage = this.getUsage();
    const exceededLimits: ExceededLimit[] = [];
    const warnings: ResourceWarning[] = [];

    // Check each resource type
    this.checkResource('maxApiCalls', this.apiCalls, exceededLimits, warnings);
    this.checkResource('maxTokens', this.tokensUsed, exceededLimits, warnings);
    this.checkResource('maxExecutionTimeMs', this.executionTimeMs, exceededLimits, warnings);
    this.checkResource('maxConcurrentOperations', this.concurrentOperations, exceededLimits, warnings);
    this.checkResource('maxFileOperations', this.fileOperations, exceededLimits, warnings);

    const withinLimits = exceededLimits.length === 0;

    if (!withinLimits && this.throwOnExceeded) {
      const exceeded = exceededLimits.map(e => `${e.resource}: ${e.current}/${e.limit}`).join(', ');
      throw new Error(`Resource limits exceeded: ${exceeded}`);
    }

    return Object.freeze({
      withinLimits,
      exceededLimits: Object.freeze(exceededLimits),
      warnings: Object.freeze(warnings),
      usage,
    });
  }

  /**
   * Record an API call
   */
  recordApiCall(): void {
    this.apiCalls++;
    this.updateTimestamp();
  }

  /**
   * Record tokens consumed
   */
  recordTokens(count: number): void {
    this.tokensUsed += count;
    this.updateTimestamp();
  }

  /**
   * Record a file operation
   */
  recordFileOperation(): void {
    this.fileOperations++;
    this.updateTimestamp();
  }

  /**
   * Record execution time
   */
  recordExecutionTime(ms: number): void {
    this.executionTimeMs += ms;
    this.updateTimestamp();
  }

  /**
   * Start tracking a concurrent operation
   */
  startConcurrentOperation(): void {
    this.concurrentOperations++;
    this.updateTimestamp();
  }

  /**
   * End tracking a concurrent operation
   */
  endConcurrentOperation(): void {
    if (this.concurrentOperations > 0) {
      this.concurrentOperations--;
    }
    this.updateTimestamp();
  }

  /**
   * Get current usage snapshot
   */
  getUsage(): ResourceUsage {
    return Object.freeze({
      apiCalls: this.apiCalls,
      tokensUsed: this.tokensUsed,
      executionTimeMs: this.executionTimeMs,
      concurrentOperations: this.concurrentOperations,
      fileOperations: this.fileOperations,
      lastUpdated: this.lastUpdated,
    });
  }

  /**
   * Get formatted usage report
   */
  getUsageReport(): string {
    const lines = [
      '=== Resource Usage Report ===',
      `API Calls: ${this.apiCalls}/${this.limits.maxApiCalls} (${this.percentage(this.apiCalls, this.limits.maxApiCalls)}%)`,
      `Tokens: ${this.tokensUsed}/${this.limits.maxTokens} (${this.percentage(this.tokensUsed, this.limits.maxTokens)}%)`,
      `Execution Time: ${this.executionTimeMs}ms/${this.limits.maxExecutionTimeMs}ms (${this.percentage(this.executionTimeMs, this.limits.maxExecutionTimeMs)}%)`,
      `Concurrent Ops: ${this.concurrentOperations}/${this.limits.maxConcurrentOperations}`,
      `File Operations: ${this.fileOperations}/${this.limits.maxFileOperations} (${this.percentage(this.fileOperations, this.limits.maxFileOperations)}%)`,
      `Last Updated: ${this.lastUpdated.toISOString()}`,
    ];
    return lines.join('\n');
  }

  /**
   * Reset all usage counters
   */
  reset(): void {
    this.apiCalls = 0;
    this.tokensUsed = 0;
    this.executionTimeMs = 0;
    this.concurrentOperations = 0;
    this.fileOperations = 0;
    this.updateTimestamp();
  }

  // Private helpers

  private checkResource(
    resource: keyof ResourceLimits,
    current: number,
    exceededLimits: ExceededLimit[],
    warnings: ResourceWarning[]
  ): void {
    const limit = this.limits[resource];
    const percentageUsed = this.percentage(current, limit);

    if (current > limit) {
      exceededLimits.push({
        resource,
        current,
        limit,
        percentageOver: percentageUsed - 100,
      });
    } else if (percentageUsed >= this.warningThreshold) {
      warnings.push({
        resource,
        current,
        limit,
        percentageUsed,
      });
    }
  }

  private percentage(current: number, limit: number): number {
    if (limit === 0) return 0;
    return Math.round((current / limit) * 100);
  }

  private updateTimestamp(): void {
    this.lastUpdated = new Date();
  }
}

/**
 * Create a ResourceLimiter instance
 *
 * @param config - Optional configuration
 * @returns IResourceLimiter instance
 */
export function createResourceLimiter(config?: ResourceLimiterConfig): IResourceLimiter {
  return new ResourceLimiter(config);
}
