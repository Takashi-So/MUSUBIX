/**
 * @fileoverview Resource limiter for wake-sleep operations
 * @traceability TSK-WAKE-007, REQ-WAKE-001-F007
 */

import type { ResourceLimits, ResourceMetrics } from '../types.js';

/**
 * Resource limiter for wake-sleep operations
 * 
 * @description
 * Enforces resource limits to prevent runaway operations:
 * - Memory limits
 * - CPU time limits
 * - Pattern count limits
 * - Concurrency limits
 */
export class ResourceLimiter {
  private limits: ResourceLimits;
  private activeOperations = 0;
  private operationStartTimes = new Map<string, number>();

  constructor(limits: Partial<ResourceLimits> = {}) {
    this.limits = {
      maxMemoryMB: limits.maxMemoryMB ?? 512,
      maxCpuTimeMs: limits.maxCpuTimeMs ?? 30000,
      maxPatterns: limits.maxPatterns ?? 10000,
      maxConcurrency: limits.maxConcurrency ?? 4,
    };
  }

  /**
   * Check if operation can start
   */
  canStartOperation(): boolean {
    return this.activeOperations < this.limits.maxConcurrency;
  }

  /**
   * Register operation start
   */
  startOperation(operationId: string): boolean {
    if (!this.canStartOperation()) return false;
    
    this.activeOperations++;
    this.operationStartTimes.set(operationId, Date.now());
    return true;
  }

  /**
   * Register operation end
   */
  endOperation(operationId: string): void {
    this.operationStartTimes.delete(operationId);
    this.activeOperations = Math.max(0, this.activeOperations - 1);
  }

  /**
   * Check if operation has exceeded time limit
   */
  isOperationTimedOut(operationId: string): boolean {
    const startTime = this.operationStartTimes.get(operationId);
    if (!startTime) return false;
    return Date.now() - startTime > this.limits.maxCpuTimeMs;
  }

  /**
   * Check if pattern count is within limit
   */
  canAddPatterns(count: number, currentCount: number): boolean {
    return currentCount + count <= this.limits.maxPatterns;
  }

  /**
   * Get current resource metrics
   */
  getMetrics(): ResourceMetrics {
    const memoryUsage = process.memoryUsage();
    return {
      memoryUsedMB: Math.round(memoryUsage.heapUsed / 1024 / 1024),
      cpuTimeMs: 0, // Would need process-level tracking
      patternCount: 0, // Would need connection to pattern library
      activeOperations: this.activeOperations,
    };
  }

  /**
   * Check if memory is within limits
   */
  isMemoryWithinLimits(): boolean {
    const metrics = this.getMetrics();
    return metrics.memoryUsedMB < this.limits.maxMemoryMB;
  }

  /**
   * Get limits
   */
  getLimits(): ResourceLimits {
    return { ...this.limits };
  }
}
