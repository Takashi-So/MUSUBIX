/**
 * @nahisaho/musubix-expert-delegation
 * Expert Manager Tests
 *
 * Traces to: REQ-EXP-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { ExpertManager } from '../../src/experts/expert-manager.js';
import { architectExpert } from '../../src/experts/architect.js';
import { securityAnalystExpert } from '../../src/experts/security-analyst.js';

describe('ExpertManager', () => {
  let manager: ExpertManager;

  beforeEach(() => {
    manager = new ExpertManager();
  });

  describe('getExpert', () => {
    it('should return architect expert', () => {
      const expert = manager.getExpert('architect');
      expect(expert.type).toBe('architect');
      expect(expert.name).toBe('Architect Expert');
    });

    it('should return security-analyst expert', () => {
      const expert = manager.getExpert('security-analyst');
      expect(expert.type).toBe('security-analyst');
      expect(expert.name).toBe('Security Analyst Expert');
    });

    it('should return all 7 expert types', () => {
      const types = [
        'architect',
        'security-analyst',
        'code-reviewer',
        'plan-reviewer',
        'ears-analyst',
        'formal-verifier',
        'ontology-reasoner',
      ] as const;

      for (const type of types) {
        const expert = manager.getExpert(type);
        expect(expert).toBeDefined();
        expect(expert.type).toBe(type);
      }
    });

    it('should throw for unknown expert type', () => {
      expect(() => manager.getExpert('unknown' as any)).toThrow();
    });
  });

  describe('registerExpert', () => {
    it('should register a custom expert', () => {
      const customExpert = {
        type: 'architect' as const,
        name: 'Custom Architect',
        description: 'Custom description',
        systemPrompt: 'Custom prompt',
        triggers: [],
        capabilities: [{ name: 'advisory', mode: 'advisory' as const, description: 'Advisory' }],
        ontologyClass: 'custom:Architect',
      };

      manager.registerExpert(customExpert);
      const expert = manager.getExpert('architect');
      expect(expert.name).toBe('Custom Architect');
    });
  });

  describe('getAllExperts', () => {
    it('should return all registered experts', () => {
      const experts = manager.getAllExperts();
      expect(experts.length).toBe(7);
    });
  });

  describe('getExpertByTrigger', () => {
    it('should find architect by "architecture" keyword', () => {
      const result = manager.getExpertByTrigger('How should I structure my architecture?');
      expect(result).not.toBeNull();
      expect(result!.type).toBe('architect');
    });

    it('should find security-analyst by "security" keyword', () => {
      const result = manager.getExpertByTrigger('Is this code secure?');
      expect(result).not.toBeNull();
      expect(result!.type).toBe('security-analyst');
    });

    it('should find ears-analyst by "EARS" keyword', () => {
      const result = manager.getExpertByTrigger('Convert to EARS format');
      expect(result).not.toBeNull();
      expect(result!.type).toBe('ears-analyst');
    });

    it('should find formal-verifier by "Z3" keyword', () => {
      const result = manager.getExpertByTrigger('Generate Z3 verification');
      expect(result).not.toBeNull();
      expect(result!.type).toBe('formal-verifier');
    });

    it('should find ontology-reasoner by Japanese keyword', () => {
      const result = manager.getExpertByTrigger('オントロジーを使って推論してください');
      expect(result).not.toBeNull();
      expect(result!.type).toBe('ontology-reasoner');
    });

    it('should return null for no match', () => {
      const result = manager.getExpertByTrigger('hello world');
      expect(result).toBeNull();
    });
  });

  describe('getAllMatchingExperts', () => {
    it('should return multiple matches sorted by priority', () => {
      const results = manager.getAllMatchingExperts('Review the architecture security');
      expect(results.length).toBeGreaterThan(1);
      // Should be sorted by priority (descending)
      for (let i = 1; i < results.length; i++) {
        expect(results[i - 1].priority).toBeGreaterThanOrEqual(results[i].priority);
      }
    });
  });
});
