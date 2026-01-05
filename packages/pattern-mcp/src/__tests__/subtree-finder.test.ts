/**
 * @fileoverview Subtree finder tests
 * @traceability TSK-PATTERN-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { SubtreeFinder } from '../extractor/subtree-finder.js';
import { TypeScriptParser } from '../extractor/typescript-parser.js';

describe('SubtreeFinder', () => {
  let finder: SubtreeFinder;
  let parser: TypeScriptParser;

  beforeEach(() => {
    finder = new SubtreeFinder({ minFrequency: 2, minDepth: 2 });
    parser = new TypeScriptParser();
  });

  it('should find repeated patterns', () => {
    const source = `
const x = 1 + 2;
const y = 3 + 4;
const z = 5 + 6;
`;
    const ast = parser.parse(source);
    const candidates = finder.find(ast);

    // Should find repeated binary expressions
    expect(candidates.length).toBeGreaterThan(0);
  });

  it('should respect minimum frequency', () => {
    const strictFinder = new SubtreeFinder({ minFrequency: 10, minDepth: 2 });
    const source = `
const a = 1;
const b = 2;
`;
    const ast = parser.parse(source);
    const candidates = strictFinder.find(ast);

    // No patterns should meet frequency 10
    expect(candidates.length).toBe(0);
  });

  it('should track locations', () => {
    const source = `
function foo() { return 1; }
function bar() { return 2; }
`;
    const ast = parser.parse(source);
    const candidates = finder.find(ast);

    // Should have location information
    for (const candidate of candidates) {
      expect(candidate.locations.length).toBeGreaterThan(0);
      for (const loc of candidate.locations) {
        expect(loc.startRow).toBeDefined();
        expect(loc.startColumn).toBeDefined();
      }
    }
  });
});
