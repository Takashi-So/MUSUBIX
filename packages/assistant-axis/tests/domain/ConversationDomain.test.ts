/**
 * ConversationDomain Value Object Tests
 *
 * @see REQ-AA-DRIFT-002
 * @see REQ-AA-DRIFT-005
 */

import { describe, it, expect } from 'vitest';
import {
  createConversationDomain,
  isSafeDomain,
  isRiskyDomain,
  DOMAIN_SAFETY,
  getAllDomainTypes,
  getSafeDomainTypes,
  getRiskyDomainTypes,
} from '../../src/domain/value-objects/ConversationDomain.js';

describe('ConversationDomain', () => {
  describe('createConversationDomain', () => {
    it('should create coding domain as safe', () => {
      const result = createConversationDomain('coding', 0.9);

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(result.value.type).toBe('coding');
        expect(result.value.isSafe).toBe(true);
        expect(result.value.confidence).toBe(0.9);
      }
    });

    it('should create writing domain as safe', () => {
      const result = createConversationDomain('writing', 0.85);

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(result.value.type).toBe('writing');
        expect(result.value.isSafe).toBe(true);
      }
    });

    it('should create therapy domain as risky', () => {
      const result = createConversationDomain('therapy', 0.7);

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(result.value.type).toBe('therapy');
        expect(result.value.isSafe).toBe(false);
      }
    });

    it('should create philosophy domain as risky', () => {
      const result = createConversationDomain('philosophy', 0.8);

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(result.value.type).toBe('philosophy');
        expect(result.value.isSafe).toBe(false);
      }
    });

    it('should reject confidence below 0', () => {
      const result = createConversationDomain('coding', -0.1);

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.message).toContain('0.0 and 1.0');
      }
    });

    it('should reject confidence above 1', () => {
      const result = createConversationDomain('coding', 1.5);

      expect(result.ok).toBe(false);
    });
  });

  describe('domain safety', () => {
    it('should have correct safety mapping', () => {
      expect(DOMAIN_SAFETY.coding).toBe(true);
      expect(DOMAIN_SAFETY.writing).toBe(true);
      expect(DOMAIN_SAFETY.therapy).toBe(false);
      expect(DOMAIN_SAFETY.philosophy).toBe(false);
    });

    it('isSafeDomain should work correctly', () => {
      const safeDomain = createConversationDomain('coding', 0.9);
      const riskyDomain = createConversationDomain('therapy', 0.9);

      expect(safeDomain.ok && isSafeDomain(safeDomain.value)).toBe(true);
      expect(riskyDomain.ok && isSafeDomain(riskyDomain.value)).toBe(false);
    });

    it('isRiskyDomain should work correctly', () => {
      const safeDomain = createConversationDomain('writing', 0.9);
      const riskyDomain = createConversationDomain('philosophy', 0.9);

      expect(safeDomain.ok && isRiskyDomain(safeDomain.value)).toBe(false);
      expect(riskyDomain.ok && isRiskyDomain(riskyDomain.value)).toBe(true);
    });
  });

  describe('domain type lists', () => {
    it('getAllDomainTypes should return all 4 types', () => {
      const types = getAllDomainTypes();
      expect(types).toHaveLength(4);
      expect(types).toContain('coding');
      expect(types).toContain('writing');
      expect(types).toContain('therapy');
      expect(types).toContain('philosophy');
    });

    it('getSafeDomainTypes should return coding and writing', () => {
      const types = getSafeDomainTypes();
      expect(types).toHaveLength(2);
      expect(types).toContain('coding');
      expect(types).toContain('writing');
    });

    it('getRiskyDomainTypes should return therapy and philosophy', () => {
      const types = getRiskyDomainTypes();
      expect(types).toHaveLength(2);
      expect(types).toContain('therapy');
      expect(types).toContain('philosophy');
    });
  });
});
