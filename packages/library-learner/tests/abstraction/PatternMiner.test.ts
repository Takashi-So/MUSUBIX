/**
 * PatternMiner Tests
 *
 * REQ-LL-001: 階層的抽象化
 * Test-First approach: Red phase
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createPatternMiner, type PatternMiner } from '../../src/abstraction/PatternMiner.js';
import type { CodeCorpus } from '../../src/types.js';
import { PatternMiningError } from '../../src/errors.js';

describe('PatternMiner', () => {
  let miner: PatternMiner;

  beforeEach(() => {
    miner = createPatternMiner();
  });

  describe('createPatternMiner', () => {
    it('should create a PatternMiner instance with default config', () => {
      expect(miner).toBeDefined();
      expect(miner.getConfig()).toEqual({
        minOccurrences: 2,
        maxDepth: 10,
        minSize: 3,
        maxSize: 50,
      });
    });

    it('should create a PatternMiner with custom config', () => {
      const customMiner = createPatternMiner({
        minOccurrences: 5,
        maxDepth: 15,
        minSize: 2,
        maxSize: 100,
      });

      expect(customMiner.getConfig()).toEqual({
        minOccurrences: 5,
        maxDepth: 15,
        minSize: 2,
        maxSize: 100,
      });
    });
  });

  describe('setMinOccurrences', () => {
    it('should update minOccurrences', () => {
      miner.setMinOccurrences(10);
      expect(miner.getConfig().minOccurrences).toBe(10);
    });

    it('should throw error for invalid minOccurrences', () => {
      expect(() => miner.setMinOccurrences(0)).toThrow(PatternMiningError);
      expect(() => miner.setMinOccurrences(-1)).toThrow(PatternMiningError);
    });
  });

  describe('mine', () => {
    it('should throw error for empty corpus', async () => {
      const emptyCorpus: CodeCorpus = {
        id: 'empty',
        files: [],
      };

      await expect(miner.mine(emptyCorpus)).rejects.toThrow(PatternMiningError);
    });

    it('should throw error for null corpus', async () => {
      await expect(miner.mine(null as unknown as CodeCorpus)).rejects.toThrow(PatternMiningError);
    });

    it('should extract patterns from single file corpus', async () => {
      const corpus: CodeCorpus = {
        id: 'single-file',
        files: [
          {
            path: 'test.ts',
            content: `
              function add(a: number, b: number): number {
                return a + b;
              }

              function subtract(a: number, b: number): number {
                return a - b;
              }
            `,
            language: 'typescript',
          },
        ],
      };

      const patterns = await miner.mine(corpus);

      expect(patterns).toBeDefined();
      expect(Array.isArray(patterns)).toBe(true);
    });

    it('should extract patterns from multi-file corpus', async () => {
      const corpus: CodeCorpus = {
        id: 'multi-file',
        files: [
          {
            path: 'file1.ts',
            content: `
              const x = 1;
              const y = 2;
            `,
            language: 'typescript',
          },
          {
            path: 'file2.ts',
            content: `
              const a = 1;
              const b = 2;
            `,
            language: 'typescript',
          },
        ],
      };

      const patterns = await miner.mine(corpus);

      expect(patterns).toBeDefined();
      expect(Array.isArray(patterns)).toBe(true);
    });

    it('should respect minOccurrences threshold', async () => {
      const miner5 = createPatternMiner({ minOccurrences: 5 });

      const corpus: CodeCorpus = {
        id: 'min-occurrences-test',
        files: [
          {
            path: 'test.ts',
            content: `
              const a = 1;
              const b = 2;
            `,
            language: 'typescript',
          },
        ],
      };

      const patterns = await miner5.mine(corpus);

      // With high threshold, few patterns should be extracted
      expect(patterns.length).toBeLessThanOrEqual(1);
    });

    it('should include pattern occurrences information', async () => {
      const corpus: CodeCorpus = {
        id: 'occurrences-test',
        files: [
          {
            path: 'test.ts',
            content: `
              const x = 1;
              const y = 2;
              const z = 3;
            `,
            language: 'typescript',
          },
        ],
      };

      miner.setMinOccurrences(1);
      const patterns = await miner.mine(corpus);

      if (patterns.length > 0) {
        const pattern = patterns[0];
        expect(pattern.occurrences).toBeDefined();
        expect(Array.isArray(pattern.occurrences)).toBe(true);
      }
    });

    it('should calculate pattern scores', async () => {
      const corpus: CodeCorpus = {
        id: 'score-test',
        files: [
          {
            path: 'test.ts',
            content: `
              function foo() { return 1; }
              function bar() { return 2; }
              function baz() { return 3; }
            `,
            language: 'typescript',
          },
        ],
      };

      miner.setMinOccurrences(1);
      const patterns = await miner.mine(corpus);

      if (patterns.length > 0) {
        patterns.forEach((pattern) => {
          expect(typeof pattern.score).toBe('number');
          expect(pattern.score).toBeGreaterThanOrEqual(0);
        });
      }
    });

    it('should sort patterns by score descending', async () => {
      const corpus: CodeCorpus = {
        id: 'sort-test',
        files: [
          {
            path: 'test.ts',
            content: `
              const a = 1;
              const b = 2;
              const c = 3;
              const d = 4;
              const e = 5;
            `,
            language: 'typescript',
          },
        ],
      };

      miner.setMinOccurrences(1);
      const patterns = await miner.mine(corpus);

      if (patterns.length > 1) {
        for (let i = 1; i < patterns.length; i++) {
          expect(patterns[i - 1].score).toBeGreaterThanOrEqual(patterns[i].score);
        }
      }
    });

    it('should assign unique IDs to patterns', async () => {
      const corpus: CodeCorpus = {
        id: 'id-test',
        files: [
          {
            path: 'test.ts',
            content: `
              const a = 1;
              const b = 2;
              const c = 3;
            `,
            language: 'typescript',
          },
        ],
      };

      miner.setMinOccurrences(1);
      const patterns = await miner.mine(corpus);

      const ids = patterns.map((p) => p.id);
      const uniqueIds = new Set(ids);
      expect(uniqueIds.size).toBe(ids.length);
    });

    it('should handle malformed code gracefully', async () => {
      const corpus: CodeCorpus = {
        id: 'malformed-test',
        files: [
          {
            path: 'test.ts',
            content: 'function broken( { return; }',
            language: 'typescript',
          },
        ],
      };

      // Should not throw, but may return empty or partial results
      const patterns = await miner.mine(corpus);
      expect(patterns).toBeDefined();
    });

    it('should extract patterns with AST information', async () => {
      const corpus: CodeCorpus = {
        id: 'ast-test',
        files: [
          {
            path: 'test.ts',
            content: `
              if (x > 0) { console.log('positive'); }
              if (y > 0) { console.log('also positive'); }
            `,
            language: 'typescript',
          },
        ],
      };

      miner.setMinOccurrences(1);
      const patterns = await miner.mine(corpus);

      if (patterns.length > 0) {
        const pattern = patterns[0];
        expect(pattern.ast).toBeDefined();
        expect(pattern.ast.type).toBeDefined();
      }
    });
  });

  describe('getConfig', () => {
    it('should return a copy of config, not reference', () => {
      const config1 = miner.getConfig();
      const config2 = miner.getConfig();

      expect(config1).toEqual(config2);
      expect(config1).not.toBe(config2);
    });
  });
});
