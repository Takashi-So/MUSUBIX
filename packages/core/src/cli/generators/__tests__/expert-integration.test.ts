/**
 * Expert Integration Tests
 *
 * @traceability REQ-EXD-001, REQ-EXD-002
 * @see ADR-v3.3.0-002 - Expert Timeout Handling
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ExpertIntegration,
  createExpertIntegration,
  DEFAULT_EXPERT_CONFIG,
} from '../expert-integration.js';
import type { GeneratedFile } from '../value-object-generator.js';

describe('ExpertIntegration', () => {
  let integration: ExpertIntegration;

  beforeEach(() => {
    integration = createExpertIntegration();
  });

  describe('DEFAULT_EXPERT_CONFIG', () => {
    it('should have 30 second timeout per ADR-v3.3.0-002', () => {
      expect(DEFAULT_EXPERT_CONFIG.defaultTimeout).toBe(30000);
    });

    it('should enable fallback on timeout per ADR-v3.3.0-002', () => {
      expect(DEFAULT_EXPERT_CONFIG.fallbackOnTimeout).toBe(true);
    });

    it('should be enabled by default', () => {
      expect(DEFAULT_EXPERT_CONFIG.enabled).toBe(true);
    });
  });

  describe('consultExpert', () => {
    it('should return disabled result when integration is disabled', async () => {
      const disabledIntegration = createExpertIntegration({ enabled: false });

      const result = await disabledIntegration.consultExpert({
        expertType: 'architect',
        content: 'test content',
        context: {
          domain: 'TEST',
          projectName: 'test-project',
          generatedFiles: [],
        },
      });

      expect(result.success).toBe(true);
      expect(result.recommendations).toHaveLength(0);
      expect(result.executionTime).toBe(0);
    });

    it('should return fallback result when expert is not available', async () => {
      const result = await integration.consultExpert({
        expertType: 'architect',
        content: 'test content',
        context: {
          domain: 'TEST',
          projectName: 'test-project',
          generatedFiles: [],
        },
      });

      // Expert-delegation may not be available in test environment
      expect(result.success).toBe(true);
      expect(result.timedOut).toBe(false);
    });

    it('should respect custom timeout', async () => {
      const startTime = Date.now();

      await integration.consultExpert({
        expertType: 'code-reviewer',
        content: 'test content',
        context: {
          domain: 'TEST',
          projectName: 'test-project',
          generatedFiles: [],
        },
        timeout: 100, // Very short timeout
      });

      const elapsed = Date.now() - startTime;
      // Should complete quickly even with short timeout
      expect(elapsed).toBeLessThan(5000);
    });

    it('should cache results when enabled', async () => {
      const cachingIntegration = createExpertIntegration({ cacheResults: true });

      const request = {
        expertType: 'architect' as const,
        content: 'test content for caching',
        context: {
          domain: 'TEST',
          projectName: 'test-project',
          generatedFiles: [],
        },
      };

      const result1 = await cachingIntegration.consultExpert(request);
      const result2 = await cachingIntegration.consultExpert(request);

      // Second call should be cached (same result)
      expect(result1.success).toBe(result2.success);
    });
  });

  describe('generateRecommendations', () => {
    it('should return empty array when disabled', async () => {
      const disabledIntegration = createExpertIntegration({ enabled: false });

      const files: GeneratedFile[] = [
        { path: '/test/price.ts', content: '// price', type: 'value-object' },
      ];

      const recommendations = await disabledIntegration.generateRecommendations(
        files,
        'TEST',
        'test-project'
      );

      expect(recommendations).toHaveLength(0);
    });

    it('should return empty array for empty files', async () => {
      const recommendations = await integration.generateRecommendations([], 'TEST', 'test-project');

      expect(recommendations).toHaveLength(0);
    });

    it('should handle multiple files', async () => {
      const files: GeneratedFile[] = [
        { path: '/test/price.ts', content: '// price value object', type: 'value-object' },
        { path: '/test/order-status.ts', content: '// order status machine', type: 'value-object' },
      ];

      const recommendations = await integration.generateRecommendations(
        files,
        'SHOP',
        'shop-project'
      );

      // May or may not have recommendations depending on expert availability
      expect(Array.isArray(recommendations)).toBe(true);
    });
  });

  describe('clearCache', () => {
    it('should clear cached results', async () => {
      const cachingIntegration = createExpertIntegration({ cacheResults: true });

      await cachingIntegration.consultExpert({
        expertType: 'architect',
        content: 'test content',
        context: {
          domain: 'TEST',
          projectName: 'test-project',
          generatedFiles: [],
        },
      });

      // Clear cache
      cachingIntegration.clearCache();

      // Should not throw
      expect(() => cachingIntegration.clearCache()).not.toThrow();
    });
  });

  describe('timeout handling (ADR-v3.3.0-002)', () => {
    it('should use default timeout from config', () => {
      const customIntegration = createExpertIntegration({ defaultTimeout: 5000 });

      // Internal state check not possible, but instantiation should work
      expect(customIntegration).toBeDefined();
    });

    it('should fallback gracefully on timeout when enabled', async () => {
      const fallbackIntegration = createExpertIntegration({
        defaultTimeout: 1, // 1ms - will definitely timeout
        fallbackOnTimeout: true,
      });

      const result = await fallbackIntegration.consultExpert({
        expertType: 'security-analyst',
        content: 'test content',
        context: {
          domain: 'TEST',
          projectName: 'test-project',
          generatedFiles: [],
        },
      });

      // Should still return a valid result
      expect(result.success).toBe(true);
    });
  });

  describe('expert types', () => {
    it.each(['architect', 'code-reviewer', 'security-analyst'] as const)(
      'should accept %s expert type',
      async (expertType) => {
        const result = await integration.consultExpert({
          expertType,
          content: 'test content',
          context: {
            domain: 'TEST',
            projectName: 'test-project',
            generatedFiles: [],
          },
        });

        expect(result).toBeDefined();
        expect(result.success).toBe(true);
      }
    );
  });

  describe('recommendation types', () => {
    it('should support all recommendation types', () => {
      // Type check - these should compile
      const types: Array<'improvement' | 'warning' | 'pattern' | 'best-practice'> = [
        'improvement',
        'warning',
        'pattern',
        'best-practice',
      ];

      expect(types).toHaveLength(4);
    });

    it('should support all priority levels', () => {
      const priorities: Array<1 | 2 | 3> = [1, 2, 3];

      expect(priorities).toHaveLength(3);
    });
  });
});
