/**
 * DriftScore Value Object Tests
 *
 * @see REQ-AA-DRIFT-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createDriftScore,
  getDriftLevel,
  isHighDrift,
  isMediumDrift,
  isLowDrift,
  compareDriftScores,
} from '../../src/domain/value-objects/DriftScore.js';
import { DEFAULT_CONFIG } from '../../src/config/defaults.js';

describe('DriftScore', () => {
  describe('createDriftScore', () => {
    it('should create valid drift score for value 0.0', () => {
      const result = createDriftScore(0.0);

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(result.value.value).toBe(0.0);
        expect(result.value.level).toBe('LOW');
      }
    });

    it('should create valid drift score for value 1.0', () => {
      const result = createDriftScore(1.0);

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(result.value.value).toBe(1.0);
        expect(result.value.level).toBe('HIGH');
      }
    });

    it('should reject negative values', () => {
      const result = createDriftScore(-0.1);

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.message).toContain('>= 0.0');
      }
    });

    it('should reject values greater than 1.0', () => {
      const result = createDriftScore(1.1);

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.message).toContain('<= 1.0');
      }
    });

    it('should reject NaN', () => {
      const result = createDriftScore(NaN);

      expect(result.ok).toBe(false);
      if (!result.ok) {
        expect(result.error.message).toContain('finite');
      }
    });

    it('should reject Infinity', () => {
      const result = createDriftScore(Infinity);

      expect(result.ok).toBe(false);
    });
  });

  describe('getDriftLevel', () => {
    it('should return LOW for values below medium threshold', () => {
      expect(getDriftLevel(0.0)).toBe('LOW');
      expect(getDriftLevel(0.29)).toBe('LOW');
    });

    it('should return MEDIUM for values at or above medium threshold', () => {
      expect(getDriftLevel(0.5)).toBe('MEDIUM');
      expect(getDriftLevel(0.69)).toBe('MEDIUM');
    });

    it('should return HIGH for values at or above high threshold', () => {
      expect(getDriftLevel(0.7)).toBe('HIGH');
      expect(getDriftLevel(1.0)).toBe('HIGH');
    });

    it('should respect custom thresholds', () => {
      const customThresholds = { low: 0.1, medium: 0.4, high: 0.8 };
      expect(getDriftLevel(0.35, customThresholds)).toBe('LOW');
      expect(getDriftLevel(0.5, customThresholds)).toBe('MEDIUM');
      expect(getDriftLevel(0.85, customThresholds)).toBe('HIGH');
    });
  });

  describe('level helpers', () => {
    it('isHighDrift should return true for HIGH level scores', () => {
      const result = createDriftScore(0.8); // >= 0.7 is HIGH

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(isHighDrift(result.value)).toBe(true);
      }
    });

    it('isMediumDrift should return true for MEDIUM level scores', () => {
      const result = createDriftScore(0.55); // >= 0.5 and < 0.7 is MEDIUM

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(isMediumDrift(result.value)).toBe(true);
        expect(isHighDrift(result.value)).toBe(false);
      }
    });

    it('isLowDrift should return true for LOW level scores', () => {
      const result = createDriftScore(0.1); // < 0.5 is LOW

      expect(result.ok).toBe(true);
      if (result.ok) {
        expect(isLowDrift(result.value)).toBe(true);
        expect(isMediumDrift(result.value)).toBe(false);
      }
    });
  });

  describe('compareDriftScores', () => {
    it('should return negative when first score is less', () => {
      const a = createDriftScore(0.2);
      const b = createDriftScore(0.5);

      expect(a.ok && b.ok).toBe(true);
      if (a.ok && b.ok) {
        expect(compareDriftScores(a.value, b.value)).toBeLessThan(0);
      }
    });

    it('should return positive when first score is greater', () => {
      const a = createDriftScore(0.7);
      const b = createDriftScore(0.3);

      expect(a.ok && b.ok).toBe(true);
      if (a.ok && b.ok) {
        expect(compareDriftScores(a.value, b.value)).toBeGreaterThan(0);
      }
    });

    it('should return 0 when scores are equal', () => {
      const a = createDriftScore(0.5);
      const b = createDriftScore(0.5);

      expect(a.ok && b.ok).toBe(true);
      if (a.ok && b.ok) {
        expect(compareDriftScores(a.value, b.value)).toBe(0);
      }
    });
  });
});
