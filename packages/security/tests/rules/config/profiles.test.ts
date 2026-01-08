/**
 * @fileoverview Profiles Tests
 * @module @nahisaho/musubix-security/rules/config/profiles.test
 * @trace TSK-RULE-002
 */

import { describe, it, expect } from 'vitest';
import {
  getProfile,
  getProfileNames,
  hasProfile,
  getProfileRuleIds,
  mergeProfileConfig,
  PROFILES,
  PROFILE_MINIMAL,
  PROFILE_STANDARD,
  PROFILE_STRICT,
  PROFILE_OWASP,
  PROFILE_CWE,
} from '../../../src/rules/config/profiles.js';

describe('Profiles', () => {
  describe('PROFILE_MINIMAL', () => {
    it('should have correct properties', () => {
      expect(PROFILE_MINIMAL.name).toBe('minimal');
      expect(PROFILE_MINIMAL.severityThreshold).toBe('high');
      expect(PROFILE_MINIMAL.enableTaintAnalysis).toBe(false);
      expect(PROFILE_MINIMAL.enableDFG).toBe(false);
    });

    it('should contain essential rules only', () => {
      expect(PROFILE_MINIMAL.rules.length).toBeLessThan(PROFILE_STANDARD.rules.length);
      
      // Should include critical OWASP rules
      const ruleIds = PROFILE_MINIMAL.rules.map(r => r.id);
      expect(ruleIds).toContain('owasp-a01-broken-access-control');
      expect(ruleIds).toContain('owasp-a03-injection');
      
      // Should include critical CWE rules
      expect(ruleIds).toContain('cwe-79-xss');
      expect(ruleIds).toContain('cwe-89-sql-injection');
    });
  });

  describe('PROFILE_STANDARD', () => {
    it('should have correct properties', () => {
      expect(PROFILE_STANDARD.name).toBe('standard');
      expect(PROFILE_STANDARD.severityThreshold).toBe('medium');
      expect(PROFILE_STANDARD.enableTaintAnalysis).toBe(true);
      expect(PROFILE_STANDARD.enableDFG).toBe(false);
    });

    it('should contain all OWASP Top 10', () => {
      const ruleIds = PROFILE_STANDARD.rules.map(r => r.id);
      for (let i = 1; i <= 10; i++) {
        const prefix = `owasp-a${String(i).padStart(2, '0')}`;
        const hasRule = ruleIds.some(id => id.startsWith(prefix));
        expect(hasRule, `Missing OWASP A${i}`).toBe(true);
      }
    });

    it('should contain CWE Top 25 rules', () => {
      const cweRules = PROFILE_STANDARD.rules.filter(r => r.id.startsWith('cwe-'));
      expect(cweRules.length).toBeGreaterThanOrEqual(20);
    });
  });

  describe('PROFILE_STRICT', () => {
    it('should have correct properties', () => {
      expect(PROFILE_STRICT.name).toBe('strict');
      expect(PROFILE_STRICT.severityThreshold).toBe('info');
      expect(PROFILE_STRICT.enableTaintAnalysis).toBe(true);
      expect(PROFILE_STRICT.enableDFG).toBe(true);
    });

    it('should include all standard rules plus more', () => {
      expect(PROFILE_STRICT.rules.length).toBeGreaterThan(PROFILE_STANDARD.rules.length);
    });
  });

  describe('PROFILE_OWASP', () => {
    it('should have correct properties', () => {
      expect(PROFILE_OWASP.name).toBe('owasp');
      expect(PROFILE_OWASP.rules.length).toBe(10);
    });

    it('should only contain OWASP rules', () => {
      const allOwasp = PROFILE_OWASP.rules.every(r => r.id.startsWith('owasp-'));
      expect(allOwasp).toBe(true);
    });
  });

  describe('PROFILE_CWE', () => {
    it('should have correct properties', () => {
      expect(PROFILE_CWE.name).toBe('cwe');
      expect(PROFILE_CWE.rules.length).toBe(25);
    });

    it('should only contain CWE rules', () => {
      const allCwe = PROFILE_CWE.rules.every(r => r.id.startsWith('cwe-'));
      expect(allCwe).toBe(true);
    });
  });

  describe('getProfile', () => {
    it('should return profile by name', () => {
      expect(getProfile('minimal')).toBe(PROFILE_MINIMAL);
      expect(getProfile('standard')).toBe(PROFILE_STANDARD);
      expect(getProfile('strict')).toBe(PROFILE_STRICT);
    });

    it('should be case insensitive', () => {
      expect(getProfile('MINIMAL')).toBe(PROFILE_MINIMAL);
      expect(getProfile('Standard')).toBe(PROFILE_STANDARD);
    });

    it('should return undefined for unknown profile', () => {
      expect(getProfile('unknown')).toBeUndefined();
    });
  });

  describe('getProfileNames', () => {
    it('should return all profile names', () => {
      const names = getProfileNames();
      expect(names).toContain('minimal');
      expect(names).toContain('standard');
      expect(names).toContain('strict');
      expect(names).toContain('owasp');
      expect(names).toContain('cwe');
    });
  });

  describe('hasProfile', () => {
    it('should return true for existing profiles', () => {
      expect(hasProfile('minimal')).toBe(true);
      expect(hasProfile('standard')).toBe(true);
    });

    it('should return false for non-existent profiles', () => {
      expect(hasProfile('unknown')).toBe(false);
    });
  });

  describe('getProfileRuleIds', () => {
    it('should return rule IDs for profile', () => {
      const ids = getProfileRuleIds('minimal');
      expect(ids).toContain('owasp-a01-broken-access-control');
    });

    it('should return empty array for unknown profile', () => {
      expect(getProfileRuleIds('unknown')).toEqual([]);
    });
  });

  describe('mergeProfileConfig', () => {
    it('should merge custom config with profile', () => {
      const merged = mergeProfileConfig('minimal', {
        'cwe-79-xss': { severity: 'critical' },
        'custom-rule': { enabled: true },
      });

      const xssRule = merged.find(r => r.id === 'cwe-79-xss');
      expect(xssRule?.severity).toBe('critical');

      const customRule = merged.find(r => r.id === 'custom-rule');
      expect(customRule).toBeDefined();
    });

    it('should respect disabled rules', () => {
      const merged = mergeProfileConfig('minimal', {
        'cwe-79-xss': { enabled: false },
        'new-rule': { enabled: false },
      });

      const xssRule = merged.find(r => r.id === 'cwe-79-xss');
      expect(xssRule?.enabled).toBe(false);

      // Disabled new rules should not be added
      const newRule = merged.find(r => r.id === 'new-rule');
      expect(newRule).toBeUndefined();
    });

    it('should return empty array for unknown profile', () => {
      const merged = mergeProfileConfig('unknown', {});
      expect(merged).toEqual([]);
    });
  });

  describe('PROFILES', () => {
    it('should contain all profiles', () => {
      expect(Object.keys(PROFILES)).toEqual(['minimal', 'standard', 'strict', 'owasp', 'cwe']);
    });
  });
});
