/**
 * Time Constraint Patterns Tests
 *
 * @see TSK-PAT-002
 */

import { describe, it, expect } from 'vitest';
import {
  TIME_PATTERNS,
  EXPIRY_PATTERN,
  SCHEDULED_PATTERN,
  INTERVAL_PATTERN,
  STREAK_PATTERN,
  COOLDOWN_PATTERN,
  getTimePattern,
  getTimePatternsByDomain,
  TIME_PATTERN_EXAMPLES,
} from './index.js';

describe('Time Constraint Patterns', () => {
  describe('TIME_PATTERNS', () => {
    it('should export 5 time patterns', () => {
      expect(TIME_PATTERNS).toHaveLength(5);
    });

    it('should have unique IDs', () => {
      const ids = TIME_PATTERNS.map((p) => p.id);
      expect(new Set(ids).size).toBe(ids.length);
    });

    it('should all be in temporal category', () => {
      for (const pattern of TIME_PATTERNS) {
        expect(pattern.category).toBe('temporal');
      }
    });

    it('should all have required fields', () => {
      for (const pattern of TIME_PATTERNS) {
        expect(pattern.id).toMatch(/^PAT-TIME-\d{3}$/);
        expect(pattern.name).toBeTruthy();
        expect(pattern.description).toBeTruthy();
        expect(pattern.problem).toBeTruthy();
        expect(pattern.solution).toBeTruthy();
        expect(pattern.implementation).toBeTruthy();
        expect(pattern.applicability).toBeInstanceOf(Array);
        expect(pattern.consequences.positive).toBeInstanceOf(Array);
        expect(pattern.consequences.negative).toBeInstanceOf(Array);
      }
    });
  });

  describe('EXPIRY_PATTERN', () => {
    it('should have correct ID and name', () => {
      expect(EXPIRY_PATTERN.id).toBe('PAT-TIME-001');
      expect(EXPIRY_PATTERN.name).toBe('Expiry Pattern');
    });

    it('should be applicable to all domains', () => {
      expect(EXPIRY_PATTERN.domain).toContain('all');
    });

    it('should include implementation with isExpired function', () => {
      expect(EXPIRY_PATTERN.implementation).toContain('isExpired');
      expect(EXPIRY_PATTERN.implementation).toContain('expiresAt');
    });

    it('should reference related patterns', () => {
      expect(EXPIRY_PATTERN.relatedPatterns).toContain('PAT-TIME-002');
      expect(EXPIRY_PATTERN.relatedPatterns).toContain('PAT-TIME-003');
    });
  });

  describe('SCHEDULED_PATTERN', () => {
    it('should have correct ID and name', () => {
      expect(SCHEDULED_PATTERN.id).toBe('PAT-TIME-002');
      expect(SCHEDULED_PATTERN.name).toBe('Scheduled Event Pattern');
    });

    it('should include status field in implementation', () => {
      expect(SCHEDULED_PATTERN.implementation).toContain('pending');
      expect(SCHEDULED_PATTERN.implementation).toContain('executed');
      expect(SCHEDULED_PATTERN.implementation).toContain('cancelled');
    });

    it('should include reschedule function', () => {
      expect(SCHEDULED_PATTERN.implementation).toContain('reschedule');
    });
  });

  describe('INTERVAL_PATTERN', () => {
    it('should have correct ID and name', () => {
      expect(INTERVAL_PATTERN.id).toBe('PAT-TIME-003');
      expect(INTERVAL_PATTERN.name).toBe('Interval Pattern');
    });

    it('should include intervalMs in implementation', () => {
      expect(INTERVAL_PATTERN.implementation).toContain('intervalMs');
      expect(INTERVAL_PATTERN.implementation).toContain('lastRunAt');
    });

    it('should include getNextRunAt function', () => {
      expect(INTERVAL_PATTERN.implementation).toContain('getNextRunAt');
      expect(INTERVAL_PATTERN.implementation).toContain('isDue');
    });
  });

  describe('STREAK_PATTERN', () => {
    it('should have correct ID and name', () => {
      expect(STREAK_PATTERN.id).toBe('PAT-TIME-004');
      expect(STREAK_PATTERN.name).toBe('Streak Pattern');
    });

    it('should be applicable to specific domains', () => {
      expect(STREAK_PATTERN.domain).toContain('fitness');
      expect(STREAK_PATTERN.domain).toContain('education');
      expect(STREAK_PATTERN.domain).toContain('gaming');
    });

    it('should include streak tracking fields', () => {
      expect(STREAK_PATTERN.implementation).toContain('currentStreak');
      expect(STREAK_PATTERN.implementation).toContain('longestStreak');
      expect(STREAK_PATTERN.implementation).toContain('lastActivityAt');
    });

    it('should include recordActivity function', () => {
      expect(STREAK_PATTERN.implementation).toContain('recordActivity');
      expect(STREAK_PATTERN.implementation).toContain('gracePeriod');
    });
  });

  describe('COOLDOWN_PATTERN', () => {
    it('should have correct ID and name', () => {
      expect(COOLDOWN_PATTERN.id).toBe('PAT-TIME-005');
      expect(COOLDOWN_PATTERN.name).toBe('Cooldown Pattern');
    });

    it('should be applicable to all domains', () => {
      expect(COOLDOWN_PATTERN.domain).toContain('all');
    });

    it('should include cooldown checking', () => {
      expect(COOLDOWN_PATTERN.implementation).toContain('canPerformAction');
      expect(COOLDOWN_PATTERN.implementation).toContain('cooldownMs');
      expect(COOLDOWN_PATTERN.implementation).toContain('remainingMs');
    });

    it('should reference related patterns', () => {
      expect(COOLDOWN_PATTERN.relatedPatterns).toContain('PAT-CONC-004');
    });
  });

  describe('getTimePattern', () => {
    it('should return pattern by ID', () => {
      const pattern = getTimePattern('PAT-TIME-001');
      expect(pattern).toBeDefined();
      expect(pattern?.name).toBe('Expiry Pattern');
    });

    it('should return undefined for unknown ID', () => {
      const pattern = getTimePattern('PAT-UNKNOWN');
      expect(pattern).toBeUndefined();
    });

    it('should find all patterns by their IDs', () => {
      for (const p of TIME_PATTERNS) {
        const found = getTimePattern(p.id);
        expect(found).toBe(p);
      }
    });
  });

  describe('getTimePatternsByDomain', () => {
    it('should return patterns for fitness domain', () => {
      const patterns = getTimePatternsByDomain('fitness');
      expect(patterns.length).toBeGreaterThan(0);
      expect(patterns.some((p) => p.id === 'PAT-TIME-004')).toBe(true);
    });

    it('should return all patterns for "all" domain', () => {
      const patterns = getTimePatternsByDomain('all');
      // Only patterns with domain=['all'] are returned
      expect(patterns.every((p) => p.domain.includes('all'))).toBe(true);
    });

    it('should return generic patterns for unknown domain', () => {
      const patterns = getTimePatternsByDomain('random-domain');
      // Should return patterns with 'all' domain
      expect(patterns.every((p) => p.domain.includes('all'))).toBe(true);
    });
  });

  describe('TIME_PATTERN_EXAMPLES', () => {
    it('should have examples for multiple patterns', () => {
      expect(TIME_PATTERN_EXAMPLES.length).toBeGreaterThanOrEqual(3);
    });

    it('should have valid pattern references', () => {
      for (const example of TIME_PATTERN_EXAMPLES) {
        const pattern = getTimePattern(example.patternId);
        expect(pattern).toBeDefined();
      }
    });

    it('should include domain and scenario', () => {
      for (const example of TIME_PATTERN_EXAMPLES) {
        expect(example.domain).toBeTruthy();
        expect(example.scenario).toBeTruthy();
        expect(example.code).toBeTruthy();
      }
    });

    it('should have coupon example for expiry pattern', () => {
      const expiryExample = TIME_PATTERN_EXAMPLES.find(
        (e) => e.patternId === 'PAT-TIME-001'
      );
      expect(expiryExample).toBeDefined();
      expect(expiryExample?.scenario).toContain('クーポン');
      expect(expiryExample?.domain).toBe('ecommerce');
    });

    it('should have appointment example for scheduled pattern', () => {
      const scheduledExample = TIME_PATTERN_EXAMPLES.find(
        (e) => e.patternId === 'PAT-TIME-002'
      );
      expect(scheduledExample).toBeDefined();
      expect(scheduledExample?.scenario).toContain('予約');
      expect(scheduledExample?.domain).toBe('healthcare');
    });

    it('should have fitness example for streak pattern', () => {
      const streakExample = TIME_PATTERN_EXAMPLES.find(
        (e) => e.patternId === 'PAT-TIME-004'
      );
      expect(streakExample).toBeDefined();
      expect(streakExample?.domain).toBe('fitness');
    });
  });

  describe('Pattern implementation code quality', () => {
    it('should have TypeScript-valid implementation snippets', () => {
      for (const pattern of TIME_PATTERNS) {
        // Check for interface or type definitions
        expect(pattern.implementation).toMatch(/interface|type|function/);
      }
    });

    it('should include default parameter for now in time functions', () => {
      // All patterns should allow injecting current time for testing
      for (const pattern of TIME_PATTERNS) {
        expect(pattern.implementation).toContain('now: Date = new Date()');
      }
    });
  });
});
