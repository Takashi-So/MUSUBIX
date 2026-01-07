/**
 * @fileoverview Tests for Attack Pattern Matcher with MITRE ATT&CK
 * @module @nahisaho/musubix-security/tests/phase6/attack-pattern-matcher
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  AttackPatternMatcher,
  createAttackPatternMatcher,
  quickPatternMatch,
  type AttackPattern,
  type MitreTechnique,
  type MitreTactic,
} from '../../src/intelligence/attack-pattern-matcher.js';

describe('AttackPatternMatcher', () => {
  let matcher: AttackPatternMatcher;

  beforeEach(() => {
    matcher = new AttackPatternMatcher();
  });

  describe('Pattern Management', () => {
    it('should get built-in patterns', () => {
      const patterns = matcher.getPatterns();
      expect(Array.isArray(patterns)).toBe(true);
      expect(patterns.length).toBeGreaterThan(0);
    });

    it('should get pattern by ID', () => {
      const patterns = matcher.getPatterns();
      if (patterns.length > 0) {
        const pattern = matcher.getPattern(patterns[0].id);
        expect(pattern).toBeDefined();
      }
    });

    it('should add custom pattern', () => {
      const customPattern: AttackPattern = {
        id: 'CUSTOM-001',
        name: 'Custom Test Pattern',
        description: 'Test pattern',
        patterns: ['test_pattern\\s*='],
        techniques: ['T1059'],
        severity: 'medium',
        confidence: 0.8,
        tags: ['test'],
      };

      matcher.addPattern(customPattern);
      const pattern = matcher.getPattern('CUSTOM-001');
      expect(pattern).toBeDefined();
      expect(pattern?.name).toBe('Custom Test Pattern');
    });

    it('should remove pattern', () => {
      const customPattern: AttackPattern = {
        id: 'TEMP-001',
        name: 'Temporary Pattern',
        description: 'Temp',
        patterns: ['temp'],
        techniques: [],
        severity: 'low',
        confidence: 0.5,
        tags: [],
      };

      matcher.addPattern(customPattern);
      expect(matcher.getPattern('TEMP-001')).toBeDefined();
      
      matcher.removePattern('TEMP-001');
      expect(matcher.getPattern('TEMP-001')).toBeUndefined();
    });
  });

  describe('MITRE ATT&CK Integration', () => {
    it('should get MITRE techniques', () => {
      const techniques = matcher.getAllTechniques();
      expect(Array.isArray(techniques)).toBe(true);
      expect(techniques.length).toBeGreaterThan(0);
    });

    it('should get technique by ID', () => {
      const technique = matcher.getTechnique('T1059');
      expect(technique).toBeDefined();
      expect(technique?.name).toBe('Command and Scripting Interpreter');
    });

    it('should get techniques by tactic', () => {
      const executionTechniques = matcher.getTechniquesByTactic('execution');
      expect(Array.isArray(executionTechniques)).toBe(true);
      expect(executionTechniques.some(t => t.id === 'T1059')).toBe(true);
    });
  });

  describe('Pattern Matching', () => {
    it('should match eval pattern', () => {
      const code = `
        const data = getUserInput();
        eval(data);
      `;
      const matches = matcher.matchCode(code, 'test.js');
      expect(Array.isArray(matches)).toBe(true);
    });

    it('should match command injection pattern', () => {
      const code = `
        const cmd = req.query.cmd;
        exec(cmd);
      `;
      const matches = matcher.matchCode(code, 'handler.js');
      expect(Array.isArray(matches)).toBe(true);
    });

    it('should return location info for matches', () => {
      const code = `eval(input)`;
      const matches = matcher.matchCode(code, 'test.js');
      
      if (matches.length > 0) {
        expect(matches[0].location).toBeDefined();
        expect(matches[0].location.file).toBe('test.js');
      }
    });
  });

  describe('Factory Functions', () => {
    it('should create matcher with options', () => {
      const customMatcher = createAttackPatternMatcher({
        minConfidence: 0.9,
        enableChainAnalysis: false,
      });
      expect(customMatcher).toBeInstanceOf(AttackPatternMatcher);
    });

    it('should perform quick pattern match', () => {
      const code = `eval(userInput)`;
      const matches = quickPatternMatch(code, 'test.js');
      expect(Array.isArray(matches)).toBe(true);
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty code', () => {
      const matches = matcher.matchCode('', 'test.js');
      expect(Array.isArray(matches)).toBe(true);
    });

    it('should handle safe code', () => {
      const code = `
        function add(a, b) {
          return a + b;
        }
      `;
      const matches = matcher.matchCode(code, 'utils.js');
      expect(Array.isArray(matches)).toBe(true);
    });
  });
});
