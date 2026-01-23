/**
 * ResourceLimiter Unit Tests
 *
 * @see TSK-FR-001〜006 - ResourceLimiter
 * @see REQ-FR-060〜063 - ResourceLimiter
 * @trace DES-MUSUBIX-FR-001 DES-ORCH-002
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  ResourceLimiter,
  createResourceLimiter,
  type IResourceLimiter,
} from '../ResourceLimiter.js';
import {
  type ResourceLimits,
  type ResourceUsage,
  createResourceLimits,
  createResourceLimiterConfig,
  DEFAULT_RESOURCE_LIMITS,
} from '../../value-objects/ResourceLimits.js';

describe('ResourceLimiter', () => {
  let limiter: IResourceLimiter;

  beforeEach(() => {
    limiter = createResourceLimiter();
  });

  describe('createResourceLimits', () => {
    it('should create default limits', () => {
      const limits = createResourceLimits();

      expect(limits.maxApiCalls).toBe(100);
      expect(limits.maxTokens).toBe(100000);
      expect(limits.maxExecutionTimeMs).toBe(300000);
      expect(limits.maxConcurrentOperations).toBe(5);
      expect(limits.maxFileOperations).toBe(50);
    });

    it('should allow overriding specific limits', () => {
      const limits = createResourceLimits({
        maxApiCalls: 50,
        maxTokens: 50000,
      });

      expect(limits.maxApiCalls).toBe(50);
      expect(limits.maxTokens).toBe(50000);
      expect(limits.maxExecutionTimeMs).toBe(300000); // default
    });

    it('should be immutable', () => {
      const limits = createResourceLimits();
      expect(Object.isFrozen(limits)).toBe(true);
    });
  });

  describe('ResourceLimiter.checkLimits', () => {
    it('should return within limits for initial state', () => {
      const result = limiter.checkLimits();

      expect(result.withinLimits).toBe(true);
      expect(result.exceededLimits).toHaveLength(0);
    });

    it('should detect exceeded API calls limit', () => {
      // Record many API calls
      for (let i = 0; i < 101; i++) {
        limiter.recordApiCall();
      }

      const result = limiter.checkLimits();

      expect(result.withinLimits).toBe(false);
      expect(result.exceededLimits).toHaveLength(1);
      expect(result.exceededLimits[0].resource).toBe('maxApiCalls');
    });

    it('should detect exceeded tokens limit', () => {
      limiter.recordTokens(100001);

      const result = limiter.checkLimits();

      expect(result.withinLimits).toBe(false);
      expect(result.exceededLimits.some(e => e.resource === 'maxTokens')).toBe(true);
    });

    it('should detect exceeded file operations limit', () => {
      for (let i = 0; i < 51; i++) {
        limiter.recordFileOperation();
      }

      const result = limiter.checkLimits();

      expect(result.withinLimits).toBe(false);
      expect(result.exceededLimits.some(e => e.resource === 'maxFileOperations')).toBe(true);
    });

    it('should return warnings when approaching limits', () => {
      // Use 85% of API calls (above 80% threshold)
      for (let i = 0; i < 85; i++) {
        limiter.recordApiCall();
      }

      const result = limiter.checkLimits();

      expect(result.withinLimits).toBe(true);
      expect(result.warnings.length).toBeGreaterThan(0);
      expect(result.warnings[0].resource).toBe('maxApiCalls');
      expect(result.warnings[0].percentageUsed).toBeGreaterThanOrEqual(80);
    });
  });

  describe('ResourceLimiter.recordApiCall', () => {
    it('should increment API call count', () => {
      limiter.recordApiCall();
      limiter.recordApiCall();
      limiter.recordApiCall();

      const usage = limiter.getUsage();

      expect(usage.apiCalls).toBe(3);
    });
  });

  describe('ResourceLimiter.recordTokens', () => {
    it('should accumulate tokens', () => {
      limiter.recordTokens(1000);
      limiter.recordTokens(2000);

      const usage = limiter.getUsage();

      expect(usage.tokensUsed).toBe(3000);
    });
  });

  describe('ResourceLimiter.recordFileOperation', () => {
    it('should increment file operation count', () => {
      limiter.recordFileOperation();
      limiter.recordFileOperation();

      const usage = limiter.getUsage();

      expect(usage.fileOperations).toBe(2);
    });
  });

  describe('ResourceLimiter.recordExecutionTime', () => {
    it('should accumulate execution time', () => {
      limiter.recordExecutionTime(1000);
      limiter.recordExecutionTime(2000);

      const usage = limiter.getUsage();

      expect(usage.executionTimeMs).toBe(3000);
    });
  });

  describe('ResourceLimiter.startConcurrentOperation / endConcurrentOperation', () => {
    it('should track concurrent operations', () => {
      limiter.startConcurrentOperation();
      limiter.startConcurrentOperation();

      expect(limiter.getUsage().concurrentOperations).toBe(2);

      limiter.endConcurrentOperation();

      expect(limiter.getUsage().concurrentOperations).toBe(1);
    });

    it('should not go below zero', () => {
      limiter.endConcurrentOperation();
      limiter.endConcurrentOperation();

      expect(limiter.getUsage().concurrentOperations).toBe(0);
    });

    it('should detect exceeded concurrent operations', () => {
      for (let i = 0; i < 6; i++) {
        limiter.startConcurrentOperation();
      }

      const result = limiter.checkLimits();

      expect(result.withinLimits).toBe(false);
      expect(result.exceededLimits.some(e => e.resource === 'maxConcurrentOperations')).toBe(true);
    });
  });

  describe('ResourceLimiter.getUsage', () => {
    it('should return current usage snapshot', () => {
      limiter.recordApiCall();
      limiter.recordTokens(500);
      limiter.recordFileOperation();

      const usage = limiter.getUsage();

      expect(usage.apiCalls).toBe(1);
      expect(usage.tokensUsed).toBe(500);
      expect(usage.fileOperations).toBe(1);
      expect(usage.lastUpdated).toBeInstanceOf(Date);
    });
  });

  describe('ResourceLimiter.getUsageReport', () => {
    it('should return formatted usage report', () => {
      limiter.recordApiCall();
      limiter.recordTokens(5000);

      const report = limiter.getUsageReport();

      expect(report).toContain('API Calls:');
      expect(report).toContain('1/100');
      expect(report).toContain('Tokens:');
      expect(report).toContain('5000/100000');
    });
  });

  describe('ResourceLimiter.reset', () => {
    it('should reset all usage counters', () => {
      limiter.recordApiCall();
      limiter.recordTokens(1000);
      limiter.recordFileOperation();
      limiter.startConcurrentOperation();

      limiter.reset();

      const usage = limiter.getUsage();

      expect(usage.apiCalls).toBe(0);
      expect(usage.tokensUsed).toBe(0);
      expect(usage.fileOperations).toBe(0);
      expect(usage.concurrentOperations).toBe(0);
    });
  });

  describe('ResourceLimiter with custom config', () => {
    it('should use custom limits', () => {
      const customLimiter = createResourceLimiter(
        createResourceLimiterConfig({
          maxApiCalls: 10,
        })
      );

      for (let i = 0; i < 11; i++) {
        customLimiter.recordApiCall();
      }

      const result = customLimiter.checkLimits();

      expect(result.withinLimits).toBe(false);
    });

    it('should use custom warning threshold', () => {
      const customLimiter = createResourceLimiter(
        createResourceLimiterConfig(
          { maxApiCalls: 100 },
          { warningThreshold: 50 }
        )
      );

      // Use 55% of API calls (above 50% threshold)
      for (let i = 0; i < 55; i++) {
        customLimiter.recordApiCall();
      }

      const result = customLimiter.checkLimits();

      expect(result.warnings.length).toBeGreaterThan(0);
    });
  });
});
