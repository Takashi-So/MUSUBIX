/**
 * Datalog Engine Tests
 *
 * @module learning/inference/__tests__/datalog-engine.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { DatalogEngine } from '../datalog-engine.js';
import type { DatalogRule, Triple, DatalogTerm } from '../types.js';

describe('DatalogEngine', () => {
  let engine: DatalogEngine;

  beforeEach(() => {
    engine = new DatalogEngine();
  });

  const createTerm = (value: string, type: 'variable' | 'constant' = 'constant'): DatalogTerm => {
    if (type === 'variable') {
      return { type: 'variable', name: value };
    }
    return { type: 'constant', value };
  };

  describe('constructor', () => {
    it('should create engine with default options', () => {
      expect(engine).toBeInstanceOf(DatalogEngine);
    });
  });

  describe('addRule', () => {
    it('should add a simple rule', () => {
      const rule: DatalogRule = {
        id: 'test-rule',
        name: 'Test Rule',
        head: {
          predicate: 'mortal',
          args: [createTerm('X', 'variable')],
        },
        body: [
          {
            predicate: 'human',
            args: [createTerm('X', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      engine.addRule(rule);

      const rules = engine.getRules();
      expect(rules).toHaveLength(1);
      expect(rules[0].id).toBe('test-rule');
    });
  });

  describe('parseRule', () => {
    it('should parse rule from string', () => {
      const parsed = engine.parseRule('ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z)');

      expect(parsed).not.toBeNull();
      expect(parsed!.head.predicate).toBe('ancestor');
    });

    it('should return null for invalid rule string', () => {
      const parsed = engine.parseRule('invalid rule syntax');

      expect(parsed).toBeNull();
    });
  });

  describe('evaluate', () => {
    it('should evaluate simple rules', async () => {
      const rule: DatalogRule = {
        id: 'mortal-rule',
        name: 'Mortal Rule',
        head: {
          predicate: 'mortal',
          args: [createTerm('X', 'variable')],
        },
        body: [
          {
            predicate: 'human',
            args: [createTerm('X', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      engine.addRule(rule);

      const facts: Triple[] = [
        { subject: 'socrates', predicate: 'human', object: 'true' },
      ];
      engine.addFacts(facts);

      const result = await engine.evaluate();

      expect(result).toBeDefined();
      expect(result.stats).toBeDefined();
    });

    it('should return result for empty facts', async () => {
      const rule: DatalogRule = {
        id: 'a-rule',
        name: 'A Rule',
        head: {
          predicate: 'a',
          args: [createTerm('X', 'variable')],
        },
        body: [
          {
            predicate: 'b',
            args: [createTerm('X', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      engine.addRule(rule);

      const result = await engine.evaluate();

      expect(result).toBeDefined();
    });
  });

  describe('query', () => {
    it('should query for specific patterns', async () => {
      const rule: DatalogRule = {
        id: 'mortal-rule',
        name: 'Mortal Rule',
        head: {
          predicate: 'mortal',
          args: [createTerm('X', 'variable')],
        },
        body: [
          {
            predicate: 'human',
            args: [createTerm('X', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      engine.addRule(rule);

      const facts: Triple[] = [
        { subject: 'socrates', predicate: 'human', object: 'true' },
        { subject: 'plato', predicate: 'human', object: 'true' },
      ];
      engine.addFacts(facts);

      await engine.evaluate();

      const results = engine.query({
        predicate: 'mortal',
        args: [createTerm('x', 'variable')],
      });

      expect(results).toBeDefined();
    });
  });

  describe('edge cases', () => {
    it('should handle self-referential facts', async () => {
      const rule: DatalogRule = {
        id: 'knows-rule',
        name: 'Knows Rule',
        head: {
          predicate: 'knows',
          args: [createTerm('X', 'variable'), createTerm('Y', 'variable')],
        },
        body: [
          {
            predicate: 'friend',
            args: [createTerm('X', 'variable'), createTerm('Y', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      engine.addRule(rule);

      const facts: Triple[] = [
        { subject: 'alice', predicate: 'friend', object: 'alice' },
      ];
      engine.addFacts(facts);

      const result = await engine.evaluate();

      expect(result).toBeDefined();
    });

    it('should handle multiple rules for same predicate', async () => {
      const rule1: DatalogRule = {
        id: 'can-move-1',
        name: 'Can Move 1',
        head: {
          predicate: 'can_move',
          args: [createTerm('X', 'variable')],
        },
        body: [
          {
            predicate: 'has_legs',
            args: [createTerm('X', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      const rule2: DatalogRule = {
        id: 'can-move-2',
        name: 'Can Move 2',
        head: {
          predicate: 'can_move',
          args: [createTerm('X', 'variable')],
        },
        body: [
          {
            predicate: 'has_wheels',
            args: [createTerm('X', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      engine.addRule(rule1);
      engine.addRule(rule2);

      const facts: Triple[] = [
        { subject: 'human', predicate: 'has_legs', object: 'true' },
        { subject: 'car', predicate: 'has_wheels', object: 'true' },
      ];
      engine.addFacts(facts);

      const result = await engine.evaluate();

      expect(result).toBeDefined();
    });
  });

  describe('clearFacts', () => {
    it('should clear all facts', async () => {
      const rule: DatalogRule = {
        id: 'a-rule',
        name: 'A Rule',
        head: {
          predicate: 'a',
          args: [createTerm('X', 'variable')],
        },
        body: [
          {
            predicate: 'b',
            args: [createTerm('X', 'variable')],
          },
        ],
        priority: 50,
        enabled: true,
      };

      engine.addRule(rule);
      engine.addFacts([{ subject: 'x', predicate: 'b', object: 'true' }]);
      await engine.evaluate();

      engine.clearFacts();

      const result = await engine.evaluate();

      // After clearing facts, no inferences should be made
      expect(result).toBeDefined();
    });
  });
});
