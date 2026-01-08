/**
 * Abstractor Tests
 *
 * REQ-LL-001: 階層的抽象化
 * Test-First approach: Red phase
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { createAbstractor, type Abstractor } from '../../src/abstraction/Abstractor.js';
import type { PatternCandidate, ConcretePattern } from '../../src/types.js';

describe('Abstractor', () => {
  let abstractor: Abstractor;

  beforeEach(() => {
    abstractor = createAbstractor();
  });

  describe('createAbstractor', () => {
    it('should create an Abstractor instance', () => {
      expect(abstractor).toBeDefined();
      expect(abstractor.extractConcretePatterns).toBeDefined();
      expect(abstractor.parameterize).toBeDefined();
      expect(abstractor.generalize).toBeDefined();
      expect(abstractor.abstract).toBeDefined();
    });
  });

  describe('extractConcretePatterns', () => {
    it('should return empty array for empty input', () => {
      const result = abstractor.extractConcretePatterns([]);
      expect(result).toEqual([]);
    });

    it('should convert pattern candidates to concrete patterns', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration', kind: 'const' },
          occurrences: [
            { file: 'test.ts', startLine: 1, endLine: 1, bindings: new Map() },
            { file: 'test.ts', startLine: 5, endLine: 5, bindings: new Map() },
          ],
          score: 10,
        },
      ];

      const result = abstractor.extractConcretePatterns(candidates);

      expect(result).toHaveLength(1);
      expect(result[0].id).toBe('PAT-1');
      expect(result[0].ast).toEqual({ type: 'Declaration', kind: 'const' });
      expect(result[0].occurrenceCount).toBe(2);
    });

    it('should preserve all candidates', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration' },
          occurrences: [{ file: 'a.ts', startLine: 1, endLine: 1, bindings: new Map() }],
          score: 10,
        },
        {
          id: 'PAT-2',
          ast: { type: 'IfStatement' },
          occurrences: [{ file: 'b.ts', startLine: 1, endLine: 3, bindings: new Map() }],
          score: 5,
        },
        {
          id: 'PAT-3',
          ast: { type: 'ForLoop' },
          occurrences: [{ file: 'c.ts', startLine: 1, endLine: 5, bindings: new Map() }],
          score: 3,
        },
      ];

      const result = abstractor.extractConcretePatterns(candidates);

      expect(result).toHaveLength(3);
      expect(result.map((p) => p.id)).toEqual(['PAT-1', 'PAT-2', 'PAT-3']);
    });

    it('should include location information', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration' },
          occurrences: [
            { file: 'file1.ts', startLine: 10, endLine: 15, bindings: new Map() },
            { file: 'file2.ts', startLine: 20, endLine: 25, bindings: new Map() },
          ],
          score: 10,
        },
      ];

      const result = abstractor.extractConcretePatterns(candidates);

      expect(result[0].locations).toHaveLength(2);
      expect(result[0].locations[0].file).toBe('file1.ts');
      expect(result[0].locations[1].file).toBe('file2.ts');
    });
  });

  describe('parameterize', () => {
    it('should return empty array for empty input', () => {
      const result = abstractor.parameterize([]);
      expect(result).toEqual([]);
    });

    it('should create simple templates from single patterns', () => {
      const patterns: ConcretePattern[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration', kind: 'const' },
          occurrenceCount: 3,
          locations: [],
        },
      ];

      const result = abstractor.parameterize(patterns);

      expect(result).toHaveLength(1);
      expect(result[0].template).toBeDefined();
      expect(result[0].concretePatterns).toContain('PAT-1');
    });

    it('should group similar patterns into templates', () => {
      const patterns: ConcretePattern[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration', kind: 'const', name: 'x' },
          occurrenceCount: 2,
          locations: [],
        },
        {
          id: 'PAT-2',
          ast: { type: 'Declaration', kind: 'const', name: 'y' },
          occurrenceCount: 2,
          locations: [],
        },
      ];

      const result = abstractor.parameterize(patterns);

      // Should create a parameterized template from similar patterns
      expect(result.length).toBeGreaterThanOrEqual(1);
    });

    it('should extract parameters from similar patterns', () => {
      const patterns: ConcretePattern[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration', kind: 'const', name: 'a' },
          occurrenceCount: 2,
          locations: [],
        },
        {
          id: 'PAT-2',
          ast: { type: 'Declaration', kind: 'const', name: 'b' },
          occurrenceCount: 2,
          locations: [],
        },
      ];

      const result = abstractor.parameterize(patterns);

      // At least one template should have parameters or be a merged template
      expect(result.length).toBeGreaterThanOrEqual(1);
      const template = result[0];
      expect(template.id).toBeDefined();
      expect(template.template).toBeDefined();
    });

    it('should keep dissimilar patterns separate', () => {
      const patterns: ConcretePattern[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration', kind: 'const' },
          occurrenceCount: 2,
          locations: [],
        },
        {
          id: 'PAT-2',
          ast: { type: 'IfStatement' },
          occurrenceCount: 2,
          locations: [],
        },
      ];

      const result = abstractor.parameterize(patterns);

      // Dissimilar patterns should result in separate templates
      expect(result).toHaveLength(2);
    });
  });

  describe('generalize', () => {
    it('should return empty array for empty input', () => {
      const result = abstractor.generalize([]);
      expect(result).toEqual([]);
    });

    it('should create concepts from templates', () => {
      const templates = [
        {
          id: 'TMPL-1',
          template: { type: 'Declaration' },
          parameters: [],
          concretePatterns: ['PAT-1'],
        },
      ];

      const result = abstractor.generalize(templates);

      expect(result.length).toBeGreaterThanOrEqual(1);
      expect(result[0].id).toBeDefined();
      expect(result[0].name).toBeDefined();
      expect(result[0].templates).toBeDefined();
    });

    it('should categorize templates by type', () => {
      const templates = [
        {
          id: 'TMPL-1',
          template: { type: 'Declaration' },
          parameters: [],
          concretePatterns: ['PAT-1'],
        },
        {
          id: 'TMPL-2',
          template: { type: 'IfStatement' },
          parameters: [],
          concretePatterns: ['PAT-2'],
        },
        {
          id: 'TMPL-3',
          template: { type: 'ForLoop' },
          parameters: [],
          concretePatterns: ['PAT-3'],
        },
      ];

      const result = abstractor.generalize(templates);

      // Should have concepts for different categories
      expect(result.length).toBeGreaterThanOrEqual(1);
      result.forEach((concept) => {
        expect(concept.category).toBeDefined();
      });
    });

    it('should assign unique IDs to concepts', () => {
      const templates = [
        {
          id: 'TMPL-1',
          template: { type: 'Declaration' },
          parameters: [],
          concretePatterns: ['PAT-1'],
        },
        {
          id: 'TMPL-2',
          template: { type: 'IfStatement' },
          parameters: [],
          concretePatterns: ['PAT-2'],
        },
      ];

      const result = abstractor.generalize(templates);

      const ids = result.map((c) => c.id);
      const uniqueIds = new Set(ids);
      expect(uniqueIds.size).toBe(ids.length);
    });

    it('should include descriptions for concepts', () => {
      const templates = [
        {
          id: 'TMPL-1',
          template: { type: 'Declaration' },
          parameters: [],
          concretePatterns: ['PAT-1'],
        },
      ];

      const result = abstractor.generalize(templates);

      expect(result[0].description).toBeDefined();
      expect(typeof result[0].description).toBe('string');
      expect(result[0].description.length).toBeGreaterThan(0);
    });
  });

  describe('abstract', () => {
    it('should return all three levels for empty input', () => {
      const result = abstractor.abstract([]);

      expect(result.concrete).toEqual([]);
      expect(result.templates).toEqual([]);
      expect(result.concepts).toEqual([]);
    });

    it('should perform full abstraction pipeline', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'Declaration', kind: 'const' },
          occurrences: [
            { file: 'test.ts', startLine: 1, endLine: 1, bindings: new Map() },
          ],
          score: 10,
        },
        {
          id: 'PAT-2',
          ast: { type: 'Declaration', kind: 'let' },
          occurrences: [
            { file: 'test.ts', startLine: 5, endLine: 5, bindings: new Map() },
          ],
          score: 8,
        },
      ];

      const result = abstractor.abstract(candidates);

      expect(result.concrete).toHaveLength(2);
      expect(result.templates.length).toBeGreaterThanOrEqual(1);
      expect(result.concepts.length).toBeGreaterThanOrEqual(1);
    });

    it('should maintain relationships between levels', () => {
      const candidates: PatternCandidate[] = [
        {
          id: 'PAT-1',
          ast: { type: 'IfStatement' },
          occurrences: [
            { file: 'a.ts', startLine: 1, endLine: 3, bindings: new Map() },
          ],
          score: 5,
        },
      ];

      const result = abstractor.abstract(candidates);

      // Concrete pattern IDs should appear in templates
      const concreteIds = result.concrete.map((c) => c.id);
      result.templates.forEach((template) => {
        template.concretePatterns.forEach((id) => {
          expect(concreteIds).toContain(id);
        });
      });

      // Template IDs should appear in concepts
      const templateIds = result.templates.map((t) => t.id);
      result.concepts.forEach((concept) => {
        concept.templates.forEach((id) => {
          expect(templateIds).toContain(id);
        });
      });
    });
  });
});
