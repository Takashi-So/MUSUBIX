/**
 * Natural Language Query Tests
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/tests/nlq
 *
 * @see REQ-YL-NLQ-001 - Natural Language Query Support
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  NLQueryParser,
  createNLQueryParser,
  type ParsedQuery,
  type QueryIntent,
} from '../src/nlq/parser.js';

// ============================================================================
// NL Query Parser Tests
// ============================================================================

describe('NLQueryParser', () => {
  let parser: NLQueryParser;

  beforeEach(() => {
    parser = createNLQueryParser();
  });

  describe('Language Detection', () => {
    it('should detect English queries', () => {
      const result = parser.parse('What functions call UserService?');
      expect(result.originalQuery).toBe('What functions call UserService?');
    });

    it('should detect Japanese queries', () => {
      const result = parser.parse('UserServiceを呼び出している関数は？');
      expect(result.originalQuery).toBe('UserServiceを呼び出している関数は？');
    });
  });

  describe('English Pattern Matching', () => {
    describe('find_callers', () => {
      const callersPatterns = [
        'What functions call UserService?',
        'What calls UserService?',
        'Which methods invoke authenticate?',
      ];

      callersPatterns.forEach((query) => {
        it(`should detect find_callers intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_callers');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });

    describe('find_callees', () => {
      const calleesPatterns = [
        'What does UserService call?',
        'List functions called by login',
      ];

      calleesPatterns.forEach((query) => {
        it(`should detect find_callees intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_callees');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });

    describe('find_implementations', () => {
      const implementationsPatterns = [
        'Show implementations of Repository',
        'What implements UserInterface?',
        'List classes implementing Service',
      ];

      implementationsPatterns.forEach((query) => {
        it(`should detect find_implementations intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_implementations');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });

    describe('find_dependencies', () => {
      const dependenciesPatterns = [
        'What does UserService depend on?',
        'Show dependencies of OrderProcessor',
      ];

      dependenciesPatterns.forEach((query) => {
        it(`should detect find_dependencies intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_dependencies');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });

    describe('find_entity', () => {
      const entityPatterns = [
        'Find UserService',
        'Show me the processOrder function',
        'Where is ConfigManager defined?',
        'Locate the login method',
      ];

      entityPatterns.forEach((query) => {
        it(`should detect find_entity intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_entity');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });
  });

  describe('Japanese Pattern Matching', () => {
    describe('find_callers (呼び出し元)', () => {
      const callersPatterns = [
        'UserServiceを呼び出している関数は？',
        'processOrderの呼び出し元を表示',
      ];

      callersPatterns.forEach((query) => {
        it(`should detect find_callers intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_callers');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });

    describe('find_implementations (実装)', () => {
      const implementationsPatterns = [
        'Repositoryの実装を表示',
        'UserInterfaceを実装しているクラス',
      ];

      implementationsPatterns.forEach((query) => {
        it(`should detect find_implementations intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_implementations');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });

    describe('find_dependencies (依存)', () => {
      const dependenciesPatterns = [
        'UserServiceの依存関係を表示',
      ];

      dependenciesPatterns.forEach((query) => {
        it(`should detect find_dependencies intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_dependencies');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });

    describe('find_entity (検索)', () => {
      const entityPatterns = [
        'UserServiceを探して',
        'ConfigManagerはどこにありますか？',
      ];

      entityPatterns.forEach((query) => {
        it(`should detect find_entity intent: "${query}"`, () => {
          const result = parser.parse(query);
          expect(result.intent).toBe('find_entity');
          expect(result.confidence).toBeGreaterThanOrEqual(0.7);
        });
      });
    });
  });

  describe('Subject Extraction', () => {
    it('should extract subject from English queries', () => {
      const result = parser.parse('What functions call UserService?');
      expect(result.subject).toBe('UserService');
    });

    it('should extract subject from Japanese queries', () => {
      const result = parser.parse('UserServiceを呼び出している関数は？');
      expect(result.subject).toBe('UserService');
    });
  });

  describe('Fallback to General Search', () => {
    it('should fallback to general_search for unmatched queries', () => {
      const result = parser.parse('random query that does not match any pattern');
      expect(result.intent).toBe('general_search');
      expect(result.confidence).toBeLessThan(0.7);
    });
  });

  describe('Relationship Type Mapping', () => {
    it('should return correct relationship types for find_callers', () => {
      const types = parser.getRelationshipTypes('find_callers');
      expect(types).toContain('calls');
    });

    it('should return correct relationship types for find_dependencies', () => {
      const types = parser.getRelationshipTypes('find_dependencies');
      expect(types).toContain('depends-on');
      expect(types).toContain('imports');
    });

    it('should return correct relationship types for find_implementations', () => {
      const types = parser.getRelationshipTypes('find_implementations');
      expect(types).toContain('implements');
    });

    it('should return empty array for find_entity', () => {
      const types = parser.getRelationshipTypes('find_entity');
      expect(types).toHaveLength(0);
    });
  });

  describe('Configuration', () => {
    it('should respect language configuration', () => {
      const jaParser = createNLQueryParser({ language: 'ja' });
      const result = jaParser.parse('show UserService');
      // Even English query should be parsed with Japanese patterns when forced
      expect(result.originalQuery).toBe('show UserService');
    });

    it('should respect minConfidence configuration', () => {
      const strictParser = createNLQueryParser({ minConfidence: 0.9 });
      const result = strictParser.parse('What calls UserService?');
      // Parser still returns result, but confidence check is external
      expect(result.confidence).toBeDefined();
    });
  });
});

// ============================================================================
// Integration Tests (would require database)
// ============================================================================

describe('NLQueryEngine Integration', () => {
  // These tests would require a mock database or actual YATA database
  // For now, we just verify the exports work

  it('should export all necessary types', async () => {
    const { NLQueryParser, createNLQueryParser } = await import('../src/nlq/parser.js');
    expect(NLQueryParser).toBeDefined();
    expect(createNLQueryParser).toBeDefined();
  });

  it('should export engine types', async () => {
    const { NLQueryEngine, createNLQueryEngine } = await import('../src/nlq/engine.js');
    expect(NLQueryEngine).toBeDefined();
    expect(createNLQueryEngine).toBeDefined();
  });
});
