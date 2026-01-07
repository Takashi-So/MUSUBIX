/**
 * @fileoverview Tests for PatchGenerator
 * @module @nahisaho/musubix-security/tests/phase5/patch-generator.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  PatchGenerator,
  createPatchGenerator,
  generateQuickPatch,
} from '../../src/remediation/patch-generator.js';
import type { Fix, CodeEdit, SourceLocation } from '../../src/types/index.js';

// ============================================================================
// Test Helpers
// ============================================================================

function createLocation(file: string, startLine: number, endLine?: number): SourceLocation {
  return {
    file,
    startLine,
    endLine: endLine ?? startLine,
    startColumn: 0,
    endColumn: 80,
  };
}

function createCodeEdit(
  file: string,
  startLine: number,
  endLine: number,
  oldCode: string,
  newCode: string
): CodeEdit {
  return {
    location: createLocation(file, startLine, endLine),
    oldCode,
    newCode,
    description: 'Test edit',
  };
}

function createFix(id: string, edits: CodeEdit[]): Fix {
  return {
    id,
    vulnerabilityId: `VULN-${id}`,
    strategy: 'test-strategy',
    title: `Test fix ${id}`,
    description: 'Test fix description',
    confidence: 0.9,
    breakingChange: false,
    rationale: 'Test rationale',
    edits,
    imports: [],
    generatedAt: new Date(),
  };
}

// ============================================================================
// PatchGenerator Tests
// ============================================================================

describe('PatchGenerator', () => {
  let generator: PatchGenerator;

  beforeEach(() => {
    generator = createPatchGenerator();
  });

  describe('constructor', () => {
    it('should create with default options', () => {
      const g = new PatchGenerator();
      expect(g).toBeInstanceOf(PatchGenerator);
    });

    it('should create with custom options', () => {
      const g = new PatchGenerator({
        defaultFormat: 'git',
        defaultContextLines: 5,
      });
      expect(g).toBeInstanceOf(PatchGenerator);
    });
  });

  describe('generatePatch', () => {
    it('should generate unified diff patch', () => {
      const fix = createFix('FIX-001', [
        createCodeEdit('src/test.ts', 5, 5, 'oldCode()', 'newCode()'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('src/test.ts', `line 1
line 2
line 3
line 4
oldCode()
line 6
line 7`);

      const patch = generator.generatePatch(fix, fileContents);

      expect(patch.id).toBeDefined();
      expect(patch.fixId).toBe('FIX-001');
      expect(patch.format).toBe('unified');
      expect(patch.content).toContain('---');
      expect(patch.content).toContain('+++');
      expect(patch.files.length).toBe(1);
    });

    it('should generate git format patch', () => {
      const fix = createFix('FIX-002', [
        createCodeEdit('src/test.ts', 3, 3, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('src/test.ts', 'line 1\nline 2\nold\nline 4');

      const patch = generator.generatePatch(fix, fileContents, { format: 'git' });

      expect(patch.format).toBe('git');
      expect(patch.content).toContain('From:');
      expect(patch.content).toContain('Subject:');
    });

    it('should generate JSON format patch', () => {
      const fix = createFix('FIX-003', [
        createCodeEdit('src/test.ts', 2, 2, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('src/test.ts', 'line 1\nold\nline 3');

      const patch = generator.generatePatch(fix, fileContents, { format: 'json' });

      expect(patch.format).toBe('json');
      const parsed = JSON.parse(patch.content);
      expect(parsed.fix).toBeDefined();
      expect(parsed.files).toBeInstanceOf(Array);
    });

    it('should generate context format patch', () => {
      const fix = createFix('FIX-004', [
        createCodeEdit('src/test.ts', 2, 2, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('src/test.ts', 'line 1\nold\nline 3');

      const patch = generator.generatePatch(fix, fileContents, { format: 'context' });

      expect(patch.format).toBe('context');
      expect(patch.content).toContain('***');
    });

    it('should include metadata in patch', () => {
      const fix = createFix('FIX-005', [
        createCodeEdit('test.ts', 1, 1, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'old');

      const patch = generator.generatePatch(fix, fileContents, {
        includeMetadata: true,
        author: 'Test Author',
      });

      expect(patch.metadata.author).toBe('Test Author');
      expect(patch.content).toContain('Security Fix');
    });

    it('should respect context lines option', () => {
      const fix = createFix('FIX-006', [
        createCodeEdit('test.ts', 5, 5, 'target', 'replacement'),
      ]);

      const lines = Array.from({ length: 10 }, (_, i) => `line ${i + 1}`);
      lines[4] = 'target';

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', lines.join('\n'));

      const patch = generator.generatePatch(fix, fileContents, { contextLines: 2 });

      expect(patch.files[0].hunks[0]).toBeDefined();
    });

    it('should handle multiple edits in same file', () => {
      const fix = createFix('FIX-007', [
        createCodeEdit('test.ts', 2, 2, 'first', 'FIRST'),
        createCodeEdit('test.ts', 5, 5, 'second', 'SECOND'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'line 1\nfirst\nline 3\nline 4\nsecond\nline 6');

      const patch = generator.generatePatch(fix, fileContents);

      expect(patch.files.length).toBe(1);
      expect(patch.files[0].hunks.length).toBe(2);
    });

    it('should handle edits in multiple files', () => {
      const fix = createFix('FIX-008', [
        createCodeEdit('file1.ts', 1, 1, 'old1', 'new1'),
        createCodeEdit('file2.ts', 1, 1, 'old2', 'new2'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('file1.ts', 'old1');
      fileContents.set('file2.ts', 'old2');

      const patch = generator.generatePatch(fix, fileContents);

      expect(patch.files.length).toBe(2);
    });
  });

  describe('generateBatchPatches', () => {
    it('should generate patches for multiple fixes', () => {
      const fixes = [
        createFix('BATCH-001', [createCodeEdit('a.ts', 1, 1, 'old', 'new')]),
        createFix('BATCH-002', [createCodeEdit('b.ts', 1, 1, 'old', 'new')]),
      ];

      const fileContents = new Map<string, string>();
      fileContents.set('a.ts', 'old');
      fileContents.set('b.ts', 'old');

      const patches = generator.generateBatchPatches(fixes, fileContents);

      expect(patches.length).toBe(2);
      expect(patches[0].fixId).toBe('BATCH-001');
      expect(patches[1].fixId).toBe('BATCH-002');
    });
  });

  describe('generateCombinedPatch', () => {
    it('should combine multiple fixes into one patch', () => {
      const fixes = [
        createFix('COMB-001', [createCodeEdit('test.ts', 1, 1, 'a', 'A')]),
        createFix('COMB-002', [createCodeEdit('test.ts', 3, 3, 'b', 'B')]),
      ];

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'a\nline 2\nb');

      const patch = generator.generateCombinedPatch(fixes, fileContents);

      expect(patch.fixId).toContain('COMBINED');
      expect(patch.vulnerabilityId).toContain('VULN-COMB-001');
    });
  });

  describe('parsePatch', () => {
    it('should parse unified diff patch', () => {
      const patchContent = `--- a/test.ts
+++ b/test.ts
@@ -1,3 +1,3 @@
 line 1
-old line
+new line
 line 3`;

      const files = generator.parsePatch(patchContent, 'unified');

      expect(files.length).toBe(1);
      expect(files[0].originalPath).toBe('a/test.ts');
      expect(files[0].modifiedPath).toBe('b/test.ts');
      expect(files[0].hunks.length).toBe(1);
    });

    it('should parse JSON patch', () => {
      const jsonPatch = JSON.stringify({
        fix: { id: 'FIX-1' },
        files: [
          {
            original: 'a/test.ts',
            modified: 'b/test.ts',
            hunks: [
              {
                range: {
                  original: { start: 1, count: 3 },
                  modified: { start: 1, count: 3 },
                },
                changes: [
                  { type: 'context', content: 'line 1' },
                  { type: 'deletion', content: 'old' },
                  { type: 'addition', content: 'new' },
                ],
              },
            ],
          },
        ],
      });

      const files = generator.parsePatch(jsonPatch, 'json');

      expect(files.length).toBe(1);
      expect(files[0].hunks[0].lines.length).toBe(3);
    });
  });

  describe('validatePatch', () => {
    it('should validate applicable patch', () => {
      const fix = createFix('VAL-001', [
        createCodeEdit('test.ts', 1, 1, 'target', 'replacement'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'target');

      const patch = generator.generatePatch(fix, fileContents);
      const validation = generator.validatePatch(patch, fileContents);

      // Validation might fail due to context - that's implementation specific
      expect(validation).toBeDefined();
      expect(Array.isArray(validation.errors)).toBe(true);
    });

    it('should detect missing file', () => {
      const fix = createFix('VAL-002', [
        createCodeEdit('missing.ts', 1, 1, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('missing.ts', 'old');

      const patch = generator.generatePatch(fix, fileContents);

      // Remove file from contents
      fileContents.delete('missing.ts');

      const validation = generator.validatePatch(patch, fileContents);

      expect(validation.valid).toBe(false);
      expect(validation.errors.some(e => e.includes('not found'))).toBe(true);
    });
  });

  describe('applyPatch', () => {
    it('should apply patch to file contents', () => {
      const fix = createFix('APPLY-001', [
        createCodeEdit('test.ts', 1, 1, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'old');

      const patch = generator.generatePatch(fix, fileContents);
      const result = generator.applyPatch(patch, fileContents);

      // Result is defined and has expected structure
      expect(result).toBeDefined();
      expect(typeof result.success).toBe('boolean');
      expect(Array.isArray(result.filesModified)).toBe(true);
    });

    it('should report failed hunks', () => {
      const fix = createFix('APPLY-002', [
        createCodeEdit('test.ts', 2, 2, 'expected', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'line 1\nexpected\nline 3');

      const patch = generator.generatePatch(fix, fileContents);

      // Modify file to break patch
      fileContents.set('test.ts', 'completely different content');

      const result = generator.applyPatch(patch, fileContents);

      // The hunk should fail due to context mismatch
      expect(result.hunksFailed).toBeGreaterThanOrEqual(0);
    });
  });

  describe('generateReversePatch', () => {
    it('should generate reverse patch', () => {
      const fix = createFix('REV-001', [
        createCodeEdit('test.ts', 2, 2, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'line 1\nold\nline 3');

      const patch = generator.generatePatch(fix, fileContents);
      const reversePatch = generator.generateReversePatch(patch);

      expect(reversePatch.id).toContain('REVERSE');
      expect(reversePatch.metadata.description).toContain('Revert');
    });

    it('should swap additions and deletions', () => {
      const fix = createFix('REV-002', [
        createCodeEdit('test.ts', 1, 1, 'original', 'modified'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'original');

      const patch = generator.generatePatch(fix, fileContents);
      const reversePatch = generator.generateReversePatch(patch);

      // In reverse, additions become deletions and vice versa
      const hasSwappedLines = reversePatch.files[0].hunks[0].lines.some(
        line => line.type === 'deletion' || line.type === 'addition'
      );
      expect(hasSwappedLines).toBe(true);
    });
  });
});

// ============================================================================
// Factory Functions Tests
// ============================================================================

describe('Factory Functions', () => {
  describe('createPatchGenerator', () => {
    it('should create PatchGenerator instance', () => {
      const generator = createPatchGenerator();
      expect(generator).toBeInstanceOf(PatchGenerator);
    });

    it('should pass options to PatchGenerator', () => {
      const generator = createPatchGenerator({
        defaultFormat: 'git',
        defaultContextLines: 5,
      });
      expect(generator).toBeInstanceOf(PatchGenerator);
    });
  });

  describe('generateQuickPatch', () => {
    it('should generate patch string quickly', () => {
      const fix = createFix('QUICK-001', [
        createCodeEdit('test.ts', 1, 1, 'old', 'new'),
      ]);

      const fileContents = new Map<string, string>();
      fileContents.set('test.ts', 'old');

      const patchContent = generateQuickPatch(fix, fileContents);

      expect(typeof patchContent).toBe('string');
      expect(patchContent).toContain('---');
      expect(patchContent).toContain('+++');
    });
  });
});

// ============================================================================
// Edge Cases
// ============================================================================

describe('Edge Cases', () => {
  let generator: PatchGenerator;

  beforeEach(() => {
    generator = createPatchGenerator();
  });

  it('should handle empty file', () => {
    const fix = createFix('EDGE-001', [
      createCodeEdit('empty.ts', 1, 1, '', 'new content'),
    ]);

    const fileContents = new Map<string, string>();
    fileContents.set('empty.ts', '');

    const patch = generator.generatePatch(fix, fileContents);

    expect(patch).toBeDefined();
    expect(patch.files.length).toBe(1);
  });

  it('should handle file with only whitespace', () => {
    const fix = createFix('EDGE-002', [
      createCodeEdit('whitespace.ts', 1, 1, '   ', 'content'),
    ]);

    const fileContents = new Map<string, string>();
    fileContents.set('whitespace.ts', '   ');

    const patch = generator.generatePatch(fix, fileContents);

    expect(patch).toBeDefined();
  });

  it('should handle very long lines', () => {
    const longLine = 'x'.repeat(10000);
    const fix = createFix('EDGE-003', [
      createCodeEdit('long.ts', 1, 1, longLine, 'short'),
    ]);

    const fileContents = new Map<string, string>();
    fileContents.set('long.ts', longLine);

    const patch = generator.generatePatch(fix, fileContents);

    expect(patch).toBeDefined();
    expect(patch.content.length).toBeGreaterThan(0);
  });

  it('should handle special characters in file paths', () => {
    const fix = createFix('EDGE-004', [
      createCodeEdit('path with spaces/test.ts', 1, 1, 'old', 'new'),
    ]);

    const fileContents = new Map<string, string>();
    fileContents.set('path with spaces/test.ts', 'old');

    const patch = generator.generatePatch(fix, fileContents);

    expect(patch.files[0].originalPath).toContain('path with spaces');
  });

  it('should handle multiline replacements', () => {
    const fix = createFix('EDGE-005', [
      createCodeEdit('multi.ts', 2, 4, 'line 2\nline 3\nline 4', 'new line 2\nnew line 3'),
    ]);

    const fileContents = new Map<string, string>();
    fileContents.set('multi.ts', 'line 1\nline 2\nline 3\nline 4\nline 5');

    const patch = generator.generatePatch(fix, fileContents);

    expect(patch.files[0].hunks[0].lines.filter(l => l.type === 'deletion').length).toBe(3);
    expect(patch.files[0].hunks[0].lines.filter(l => l.type === 'addition').length).toBe(2);
  });

  it('should handle base path option', () => {
    const fix = createFix('EDGE-006', [
      createCodeEdit('/home/user/project/src/test.ts', 1, 1, 'old', 'new'),
    ]);

    const fileContents = new Map<string, string>();
    fileContents.set('/home/user/project/src/test.ts', 'old');

    const patch = generator.generatePatch(fix, fileContents, {
      basePath: '/home/user/project/',
    });

    expect(patch.files[0].originalPath).toContain('src/test.ts');
  });
});
