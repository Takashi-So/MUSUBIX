/**
 * @nahisaho/musubix-expert-delegation
 * Proactive Delegation Tests
 *
 * Traces to: REQ-TRG-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { ProactiveDelegation } from '../../src/triggers/proactive-delegation.js';

describe('ProactiveDelegation', () => {
  let proactive: ProactiveDelegation;

  beforeEach(() => {
    proactive = new ProactiveDelegation({ escalationThreshold: 3 });
  });

  describe('checkEscalation', () => {
    it('should not escalate on first failure', () => {
      expect(proactive.checkEscalation('task-1')).toBe(false);
    });

    it('should not escalate on second failure', () => {
      proactive.checkEscalation('task-1');
      expect(proactive.checkEscalation('task-1')).toBe(false);
    });

    it('should escalate on third failure', () => {
      proactive.checkEscalation('task-1');
      proactive.checkEscalation('task-1');
      expect(proactive.checkEscalation('task-1')).toBe(true);
    });

    it('should track failures per task', () => {
      proactive.checkEscalation('task-1');
      proactive.checkEscalation('task-1');
      expect(proactive.checkEscalation('task-2')).toBe(false);
    });
  });

  describe('resetFailureCount', () => {
    it('should reset failure count', () => {
      proactive.checkEscalation('task-1');
      proactive.checkEscalation('task-1');
      proactive.resetFailureCount('task-1');
      expect(proactive.getFailureCount('task-1')).toBe(0);
    });
  });

  describe('detectSecurityPattern', () => {
    it('should detect SQL injection', () => {
      const code = 'db.query(`SELECT * FROM users WHERE id = ${userId}`)';
      const patterns = proactive.detectSecurityPattern(code);
      expect(patterns.length).toBeGreaterThan(0);
      expect(patterns.some(p => p.pattern === 'SQL Injection')).toBe(true);
      expect(patterns.find(p => p.pattern === 'SQL Injection')?.severity).toBe('high');
    });

    it('should detect hardcoded credentials', () => {
      const code = 'const password = "secret123"';
      const patterns = proactive.detectSecurityPattern(code);
      expect(patterns.some(p => p.pattern === 'Hardcoded Credentials')).toBe(true);
    });

    it('should detect eval usage', () => {
      const code = 'eval(userInput)';
      const patterns = proactive.detectSecurityPattern(code);
      expect(patterns.some(p => p.pattern === 'eval() Usage')).toBe(true);
    });

    it('should detect dangerouslySetInnerHTML', () => {
      const code = '<div dangerouslySetInnerHTML={{__html: content}} />';
      const patterns = proactive.detectSecurityPattern(code);
      expect(patterns.some(p => p.pattern.includes('XSS'))).toBe(true);
    });

    it('should detect unencrypted HTTP', () => {
      const code = 'fetch("http://api.example.com/data")';
      const patterns = proactive.detectSecurityPattern(code);
      expect(patterns.some(p => p.pattern === 'Unencrypted HTTP')).toBe(true);
    });

    it('should allow localhost HTTP', () => {
      const code = 'fetch("http://localhost:3000/api")';
      const patterns = proactive.detectSecurityPattern(code);
      expect(patterns.some(p => p.pattern === 'Unencrypted HTTP')).toBe(false);
    });

    it('should return empty for safe code', () => {
      const code = 'const x = 1 + 2;';
      const patterns = proactive.detectSecurityPattern(code);
      expect(patterns.length).toBe(0);
    });
  });

  describe('detectNonEarsRequirement', () => {
    it('should detect non-EARS requirement', () => {
      const text = 'The system must authenticate users';
      const match = proactive.detectNonEarsRequirement(text);
      expect(match).not.toBeNull();
      expect(match!.suggestedPattern).toBeDefined();
    });

    it('should skip EARS format text', () => {
      const text = 'THE system SHALL authenticate users';
      const match = proactive.detectNonEarsRequirement(text);
      expect(match).toBeNull();
    });

    it('should skip non-requirement text', () => {
      const text = 'Hello world';
      const match = proactive.detectNonEarsRequirement(text);
      expect(match).toBeNull();
    });

    it('should suggest event-driven for "when"', () => {
      const text = 'When user clicks, the system should respond';
      const match = proactive.detectNonEarsRequirement(text);
      expect(match).not.toBeNull();
      expect(match!.suggestedPattern).toBe('event-driven');
    });

    it('should suggest state-driven for "while"', () => {
      const text = 'While in maintenance mode, the system should show warning';
      const match = proactive.detectNonEarsRequirement(text);
      expect(match).not.toBeNull();
      expect(match!.suggestedPattern).toBe('state-driven');
    });

    it('should suggest unwanted for "not"', () => {
      const text = 'The system must not expose user data';
      const match = proactive.detectNonEarsRequirement(text);
      expect(match).not.toBeNull();
      expect(match!.suggestedPattern).toBe('unwanted');
    });
  });

  describe('suggestDelegation', () => {
    it('should suggest security-analyst for vulnerable code', () => {
      const code = 'eval(userInput)';
      const suggestions = proactive.suggestDelegation(code, []);
      expect(suggestions.some(s => s.expert === 'security-analyst')).toBe(true);
    });

    it('should suggest ears-analyst for non-EARS requirements', () => {
      const requirements = ['The system must do X', 'Users should be able to Y'];
      const suggestions = proactive.suggestDelegation('', requirements);
      expect(suggestions.some(s => s.expert === 'ears-analyst')).toBe(true);
    });

    it('should sort suggestions by priority', () => {
      const code = 'eval(userInput)';
      const requirements = ['The system must do X'];
      const suggestions = proactive.suggestDelegation(code, requirements);
      
      for (let i = 1; i < suggestions.length; i++) {
        expect(suggestions[i - 1].priority).toBeGreaterThanOrEqual(suggestions[i].priority);
      }
    });
  });

  describe('clearAll', () => {
    it('should clear all failure counts', () => {
      proactive.checkEscalation('task-1');
      proactive.checkEscalation('task-2');
      proactive.clearAll();
      expect(proactive.getFailureCount('task-1')).toBe(0);
      expect(proactive.getFailureCount('task-2')).toBe(0);
    });
  });
});
