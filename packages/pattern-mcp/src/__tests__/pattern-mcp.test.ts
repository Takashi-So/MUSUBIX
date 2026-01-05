/**
 * @fileoverview Pattern MCP tests
 * @traceability TSK-PATTERN-001, TSK-PATTERN-005, TSK-PATTERN-007
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PatternExtractor } from '../extractor/pattern-extractor.js';
import { PatternLibrary } from '../library/pattern-library.js';
import { PrivacyFilter } from '../privacy/privacy-filter.js';
import type { Pattern } from '../types.js';

describe('PatternExtractor', () => {
  let extractor: PatternExtractor;

  beforeEach(() => {
    extractor = new PatternExtractor({ language: 'typescript' });
  });

  it('should create extractor with default options', () => {
    expect(extractor).toBeDefined();
  });

  it('should extract patterns from source code', async () => {
    const source = 'const x = 1;';
    const patterns = await extractor.extract(source);
    expect(Array.isArray(patterns)).toBe(true);
  });
});

describe('PatternLibrary', () => {
  let library: PatternLibrary;

  beforeEach(() => {
    library = new PatternLibrary({
      storagePath: '/tmp/test-patterns.json',
    });
  });

  it('should start with empty library', () => {
    expect(library.size).toBe(0);
  });

  it('should add and retrieve patterns', () => {
    const pattern: Pattern = {
      id: 'test-001',
      name: 'test_pattern',
      language: 'typescript',
      ast: { type: 'program', children: [], startPosition: { row: 0, column: 0 }, endPosition: { row: 0, column: 0 } },
      holes: [],
      frequency: 1,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    };

    expect(library.add(pattern)).toBe(true);
    expect(library.size).toBe(1);
    expect(library.get('test-001')).toEqual(pattern);
  });

  it('should delete patterns', () => {
    const pattern: Pattern = {
      id: 'test-002',
      name: 'test_pattern',
      language: 'typescript',
      ast: { type: 'program', children: [], startPosition: { row: 0, column: 0 }, endPosition: { row: 0, column: 0 } },
      holes: [],
      frequency: 1,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    };

    library.add(pattern);
    expect(library.delete('test-002')).toBe(true);
    expect(library.size).toBe(0);
  });

  it('should export and import patterns', () => {
    const pattern: Pattern = {
      id: 'test-003',
      name: 'export_test',
      language: 'typescript',
      ast: { type: 'program', children: [], startPosition: { row: 0, column: 0 }, endPosition: { row: 0, column: 0 } },
      holes: [],
      frequency: 1,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    };

    library.add(pattern);
    const exported = library.export();

    const newLibrary = new PatternLibrary();
    const imported = newLibrary.import(exported);
    expect(imported).toBe(1);
    expect(newLibrary.get('test-003')?.name).toBe('export_test');
  });
});

describe('PrivacyFilter', () => {
  let filter: PrivacyFilter;

  beforeEach(() => {
    filter = new PrivacyFilter();
  });

  it('should block external communication by default', () => {
    expect(filter.isExternalCommunicationBlocked()).toBe(true);
  });

  it('should filter patterns with sensitive names', () => {
    const sensitivePattern: Pattern = {
      id: 'sensitive-001',
      name: 'api_key_handler',
      language: 'typescript',
      ast: { type: 'program', children: [], startPosition: { row: 0, column: 0 }, endPosition: { row: 0, column: 0 } },
      holes: [],
      frequency: 1,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    };

    const result = filter.filter(sensitivePattern);
    expect(result.filtered).toBe(true);
    expect(result.reason).toContain('sensitive');
  });

  it('should allow safe patterns', () => {
    const safePattern: Pattern = {
      id: 'safe-001',
      name: 'calculate_sum',
      language: 'typescript',
      ast: { type: 'program', children: [], startPosition: { row: 0, column: 0 }, endPosition: { row: 0, column: 0 } },
      holes: [],
      frequency: 1,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    };

    const result = filter.filter(safePattern);
    expect(result.filtered).toBe(false);
  });
});
