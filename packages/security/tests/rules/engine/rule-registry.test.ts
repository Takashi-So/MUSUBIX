/**
 * @fileoverview Rule Registry Tests
 * @module @nahisaho/musubix-security/rules/engine/rule-registry.test
 * @trace TSK-RULE-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  RuleRegistry,
  createRegistry,
  getGlobalRegistry,
} from '../../../src/rules/engine/rule-registry.js';
import type { SecurityRule, RuleContext, RuleFinding } from '../../../src/rules/types.js';

// Mock rule for testing
function createMockRule(overrides: Partial<SecurityRule> = {}): SecurityRule {
  return {
    id: 'test-rule-001',
    name: 'Test Rule',
    description: 'A test security rule',
    defaultSeverity: 'medium',
    detectionMethod: 'pattern-match',
    tags: ['test'],
    analyze: async (_context: RuleContext): Promise<RuleFinding[]> => [],
    ...overrides,
  };
}

describe('RuleRegistry', () => {
  let registry: RuleRegistry;

  beforeEach(() => {
    registry = createRegistry();
  });

  describe('register', () => {
    it('should register a rule', () => {
      const rule = createMockRule();
      
      registry.register(rule);
      
      expect(registry.has('test-rule-001')).toBe(true);
    });

    it('should throw on duplicate registration without overwrite', () => {
      const rule = createMockRule();
      registry.register(rule);
      
      expect(() => registry.register(rule)).toThrow(/already registered/);
    });

    it('should allow duplicate registration with overwrite flag', () => {
      const rule1 = createMockRule({ description: 'First' });
      const rule2 = createMockRule({ description: 'Second' });
      
      registry.register(rule1);
      registry.register(rule2, true);
      
      expect(registry.get('test-rule-001')?.description).toBe('Second');
    });
  });

  describe('get', () => {
    it('should return registered rule', () => {
      const rule = createMockRule();
      registry.register(rule);
      
      const retrieved = registry.get('test-rule-001');
      
      expect(retrieved).toBe(rule);
    });

    it('should return undefined for non-existent rule', () => {
      expect(registry.get('non-existent')).toBeUndefined();
    });
  });

  describe('has', () => {
    it('should return true for registered rule', () => {
      const rule = createMockRule();
      registry.register(rule);
      
      expect(registry.has('test-rule-001')).toBe(true);
    });

    it('should return false for non-registered rule', () => {
      expect(registry.has('non-existent')).toBe(false);
    });
  });

  describe('getAll', () => {
    it('should return all registered rules', () => {
      const rule1 = createMockRule({ id: 'rule-1' });
      const rule2 = createMockRule({ id: 'rule-2' });
      
      registry.register(rule1);
      registry.register(rule2);
      
      const all = registry.getAll();
      
      expect(all).toHaveLength(2);
      expect(all).toContain(rule1);
      expect(all).toContain(rule2);
    });

    it('should return empty array when no rules registered', () => {
      expect(registry.getAll()).toEqual([]);
    });
  });

  describe('unregister', () => {
    it('should remove a registered rule', () => {
      const rule = createMockRule();
      registry.register(rule);
      
      const removed = registry.unregister('test-rule-001');
      
      expect(removed).toBe(true);
      expect(registry.has('test-rule-001')).toBe(false);
    });

    it('should return false for non-existent rule', () => {
      expect(registry.unregister('non-existent')).toBe(false);
    });
  });

  describe('clear', () => {
    it('should remove all rules', () => {
      registry.register(createMockRule({ id: 'rule-1' }));
      registry.register(createMockRule({ id: 'rule-2' }));
      
      registry.clear();
      
      expect(registry.getAll()).toEqual([]);
    });
  });

  describe('getByCategory', () => {
    it('should return rules by owasp category', () => {
      const rule1 = createMockRule({ 
        id: 'owasp-a01',
        owasp: ['A01:2021'],
      });
      const rule2 = createMockRule({ 
        id: 'owasp-a03',
        owasp: ['A03:2021'],
      });
      
      registry.register(rule1);
      registry.register(rule2);
      
      const owaspRules = registry.getByCategory('owasp');
      
      expect(owaspRules).toHaveLength(2);
    });

    it('should return rules by cwe category', () => {
      const rule1 = createMockRule({ 
        id: 'cwe-79',
        cwe: ['79'],
      });
      const rule2 = createMockRule({ 
        id: 'other',
      });
      
      registry.register(rule1);
      registry.register(rule2);
      
      const cweRules = registry.getByCategory('cwe');
      
      expect(cweRules).toHaveLength(1);
      expect(cweRules[0].id).toBe('cwe-79');
    });

    it('should return custom rules', () => {
      const rule1 = createMockRule({ 
        id: 'custom-rule',
      });
      const rule2 = createMockRule({ 
        id: 'owasp-a01',
        owasp: ['A01:2021'],
      });
      
      registry.register(rule1);
      registry.register(rule2);
      
      const customRules = registry.getByCategory('custom');
      
      expect(customRules).toHaveLength(1);
      expect(customRules[0].id).toBe('custom-rule');
    });
  });

  describe('getByTag', () => {
    it('should return rules with specific tag', () => {
      const rule1 = createMockRule({ 
        id: 'rule-1',
        tags: ['injection', 'sql'],
      });
      const rule2 = createMockRule({ 
        id: 'rule-2',
        tags: ['xss', 'injection'],
      });
      const rule3 = createMockRule({ 
        id: 'rule-3',
        tags: ['crypto'],
      });
      
      registry.register(rule1);
      registry.register(rule2);
      registry.register(rule3);
      
      const injectionRules = registry.getByTag('injection');
      
      expect(injectionRules).toHaveLength(2);
      expect(injectionRules.map(r => r.id)).toContain('rule-1');
      expect(injectionRules.map(r => r.id)).toContain('rule-2');
    });

    it('should return empty array for non-existent tag', () => {
      const rule = createMockRule({ tags: ['test'] });
      registry.register(rule);
      
      expect(registry.getByTag('non-existent')).toEqual([]);
    });
  });

  describe('getBySeverity', () => {
    it('should return rules by default severity', () => {
      const rule1 = createMockRule({ 
        id: 'rule-1',
        defaultSeverity: 'high',
      });
      const rule2 = createMockRule({ 
        id: 'rule-2',
        defaultSeverity: 'medium',
      });
      const rule3 = createMockRule({ 
        id: 'rule-3',
        defaultSeverity: 'high',
      });
      
      registry.register(rule1);
      registry.register(rule2);
      registry.register(rule3);
      
      const highRules = registry.getBySeverity('high');
      
      expect(highRules).toHaveLength(2);
    });
  });

  describe('getByDetectionMethod', () => {
    it('should return rules by detection method', () => {
      const rule1 = createMockRule({ 
        id: 'rule-1',
        detectionMethod: 'taint-analysis',
      });
      const rule2 = createMockRule({ 
        id: 'rule-2',
        detectionMethod: 'pattern-match',
      });
      const rule3 = createMockRule({ 
        id: 'rule-3',
        detectionMethod: 'taint-analysis',
      });
      
      registry.register(rule1);
      registry.register(rule2);
      registry.register(rule3);
      
      const taintRules = registry.getByDetectionMethod('taint-analysis');
      
      expect(taintRules).toHaveLength(2);
    });
  });

  describe('filter', () => {
    it('should filter rules by predicate', () => {
      const rule1 = createMockRule({ id: 'rule-1', defaultSeverity: 'high' });
      const rule2 = createMockRule({ id: 'rule-2', defaultSeverity: 'medium' });
      const rule3 = createMockRule({ id: 'rule-3', defaultSeverity: 'high' });
      
      registry.register(rule1);
      registry.register(rule2);
      registry.register(rule3);
      
      const filtered = registry.filter(r => r.defaultSeverity === 'high');
      
      expect(filtered).toHaveLength(2);
    });
  });

  describe('count', () => {
    it('should return total rule count', () => {
      registry.register(createMockRule({ id: 'rule-1' }));
      registry.register(createMockRule({ id: 'rule-2' }));
      registry.register(createMockRule({ id: 'rule-3' }));
      
      expect(registry.count()).toBe(3);
    });
  });

  describe('getIds', () => {
    it('should return all rule IDs', () => {
      registry.register(createMockRule({ id: 'rule-1' }));
      registry.register(createMockRule({ id: 'rule-2' }));
      
      const ids = registry.getIds();
      
      expect(ids).toContain('rule-1');
      expect(ids).toContain('rule-2');
    });
  });
});

describe('Global Registry', () => {
  it('should return same instance', () => {
    const instance1 = getGlobalRegistry();
    const instance2 = getGlobalRegistry();
    
    expect(instance1).toBe(instance2);
  });
});
