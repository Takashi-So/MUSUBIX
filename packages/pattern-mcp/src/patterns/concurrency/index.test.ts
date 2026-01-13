/**
 * Concurrency Patterns Tests
 *
 * @packageDocumentation
 * @module patterns/concurrency.test
 *
 * @see REQ-PAT-001 - 同時実行パターン追加
 * @see TSK-PAT-001 - 同時実行パターンタスク
 */

import { describe, it, expect } from 'vitest';
import {
  CONCURRENCY_PATTERNS,
  OPTIMISTIC_LOCKING,
  PESSIMISTIC_LOCKING,
  HOLD_PATTERN,
  IDEMPOTENCY_KEY,
  getConcurrencyPattern,
  getConcurrencyPatternsByTag,
  getConcurrencyPatternIds,
} from './index.js';

describe('Concurrency Patterns', () => {
  describe('CONCURRENCY_PATTERNS', () => {
    it('should have 4 patterns defined', () => {
      expect(CONCURRENCY_PATTERNS).toHaveLength(4);
    });

    it('should have unique IDs', () => {
      const ids = CONCURRENCY_PATTERNS.map((p) => p.id);
      const uniqueIds = new Set(ids);
      expect(uniqueIds.size).toBe(ids.length);
    });

    it('should follow PAT-CONC-XXX naming convention', () => {
      CONCURRENCY_PATTERNS.forEach((pattern) => {
        expect(pattern.id).toMatch(/^PAT-CONC-\d{3}$/);
      });
    });
  });

  describe('PAT-CONC-001: Optimistic Locking', () => {
    it('should have required fields', () => {
      expect(OPTIMISTIC_LOCKING.id).toBe('PAT-CONC-001');
      expect(OPTIMISTIC_LOCKING.name).toBe('Optimistic Locking');
      expect(OPTIMISTIC_LOCKING.description).toBeTruthy();
      expect(OPTIMISTIC_LOCKING.useCase).toBeTruthy();
      expect(OPTIMISTIC_LOCKING.template).toBeTruthy();
      expect(OPTIMISTIC_LOCKING.example).toBeTruthy();
    });

    it('should have template with version field', () => {
      expect(OPTIMISTIC_LOCKING.template).toContain('version');
      expect(OPTIMISTIC_LOCKING.template).toContain('WithVersion');
    });

    it('should have high confidence', () => {
      expect(OPTIMISTIC_LOCKING.confidence).toBeGreaterThanOrEqual(0.9);
    });

    it('should have concurrency tag', () => {
      expect(OPTIMISTIC_LOCKING.tags).toContain('concurrency');
    });
  });

  describe('PAT-CONC-002: Pessimistic Locking', () => {
    it('should have required fields', () => {
      expect(PESSIMISTIC_LOCKING.id).toBe('PAT-CONC-002');
      expect(PESSIMISTIC_LOCKING.name).toBe('Pessimistic Locking');
      expect(PESSIMISTIC_LOCKING.template).toContain('Lock');
      expect(PESSIMISTIC_LOCKING.template).toContain('acquire');
      expect(PESSIMISTIC_LOCKING.template).toContain('release');
    });

    it('should reference optimistic locking as related', () => {
      expect(PESSIMISTIC_LOCKING.relatedPatterns).toContain('PAT-CONC-001');
    });
  });

  describe('PAT-CONC-003: Hold Pattern', () => {
    it('should have required fields', () => {
      expect(HOLD_PATTERN.id).toBe('PAT-CONC-003');
      expect(HOLD_PATTERN.name).toBe('Hold Pattern');
      expect(HOLD_PATTERN.template).toContain('Hold');
      expect(HOLD_PATTERN.template).toContain('expiresAt');
    });

    it('should have expiry tag', () => {
      expect(HOLD_PATTERN.tags).toContain('expiry');
    });

    it('should have checkout-related use case', () => {
      expect(HOLD_PATTERN.useCase.toLowerCase()).toContain('checkout');
    });
  });

  describe('PAT-CONC-004: Idempotency Key', () => {
    it('should have required fields', () => {
      expect(IDEMPOTENCY_KEY.id).toBe('PAT-CONC-004');
      expect(IDEMPOTENCY_KEY.name).toBe('Idempotency Key');
      expect(IDEMPOTENCY_KEY.template).toContain('IdempotencyRecord');
      expect(IDEMPOTENCY_KEY.template).toContain('idempotencyKey');
    });

    it('should have payment tag', () => {
      expect(IDEMPOTENCY_KEY.tags).toContain('payment');
    });

    it('should have high confidence', () => {
      expect(IDEMPOTENCY_KEY.confidence).toBeGreaterThanOrEqual(0.9);
    });
  });

  describe('getConcurrencyPattern', () => {
    it('should return pattern by ID', () => {
      const pattern = getConcurrencyPattern('PAT-CONC-001');
      expect(pattern).toBe(OPTIMISTIC_LOCKING);
    });

    it('should return undefined for unknown ID', () => {
      const pattern = getConcurrencyPattern('PAT-CONC-999');
      expect(pattern).toBeUndefined();
    });
  });

  describe('getConcurrencyPatternsByTag', () => {
    it('should return all patterns with concurrency tag', () => {
      const patterns = getConcurrencyPatternsByTag('concurrency');
      expect(patterns).toHaveLength(4);
    });

    it('should return only locking patterns', () => {
      const patterns = getConcurrencyPatternsByTag('locking');
      expect(patterns).toHaveLength(1);
      expect(patterns[0].id).toBe('PAT-CONC-002');
    });

    it('should return empty array for unknown tag', () => {
      const patterns = getConcurrencyPatternsByTag('unknown-tag');
      expect(patterns).toHaveLength(0);
    });
  });

  describe('getConcurrencyPatternIds', () => {
    it('should return all pattern IDs', () => {
      const ids = getConcurrencyPatternIds();
      expect(ids).toEqual([
        'PAT-CONC-001',
        'PAT-CONC-002',
        'PAT-CONC-003',
        'PAT-CONC-004',
      ]);
    });
  });

  describe('template code quality', () => {
    it('should have valid TypeScript-like syntax in templates', () => {
      CONCURRENCY_PATTERNS.forEach((pattern) => {
        // Check for interface definitions
        expect(pattern.template).toMatch(/interface\s+\w+/);
        // Check for function definitions
        expect(pattern.template).toMatch(/(?:async\s+)?function\s+\w+/);
      });
    });

    it('should have examples that reference template types', () => {
      CONCURRENCY_PATTERNS.forEach((pattern) => {
        // Examples should use types/functions from template
        const templateHasVersion = pattern.template.includes('WithVersion');
        const exampleHasVersion = pattern.example.includes('version');
        
        if (templateHasVersion) {
          expect(exampleHasVersion).toBe(true);
        }
      });
    });
  });
});
