/**
 * Markdown EARS Parser Tests
 *
 * @packageDocumentation
 * @module validators/markdown-ears-parser.test
 *
 * @see REQ-VAL-001 - Markdown内EARS形式検出
 * @see TSK-VAL-001 - Markdown内EARS検出タスク
 */

import { describe, it, expect } from 'vitest';
import {
  MarkdownEARSParser,
  parseMarkdownEARS,
  extractValidEARS,
} from './markdown-ears-parser.js';

describe('MarkdownEARSParser', () => {
  describe('table parsing', () => {
    it('should detect EARS in table cells', () => {
      const markdown = `
| ID | Requirement |
|----|-------------|
| REQ-001 | The system shall authenticate users |
| REQ-002 | When user logs in, the system shall create session |
`;
      const parser = new MarkdownEARSParser();
      const result = parser.parse(markdown);

      expect(result.statements).toHaveLength(2);
      expect(result.statements[0].source).toBe('table');
      expect(result.statements[0].text).toContain('system shall');
      expect(result.stats.tableStatements).toBe(2);
    });

    it('should extract requirement ID from table row', () => {
      const markdown = `
| ID | Requirement |
|----|-------------|
| REQ-AUTH-001 | The system shall validate credentials |
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].requirementId).toBe('REQ-AUTH-001');
    });

    it('should handle multi-column tables', () => {
      const markdown = `
| ID | Priority | Requirement | Notes |
|----|----------|-------------|-------|
| REQ-001 | P0 | The API shall return JSON responses | REST API |
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements).toHaveLength(1);
      expect(result.statements[0].text).toContain('shall return JSON');
    });
  });

  describe('bullet list parsing', () => {
    it('should detect EARS in bullet lists with hyphen', () => {
      const markdown = `
Requirements:
- The system shall log all errors
- When error occurs, the system shall notify admin
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements.filter((s) => s.source === 'bullet')).toHaveLength(2);
      expect(result.stats.bulletStatements).toBe(2);
    });

    it('should detect EARS in bullet lists with asterisk', () => {
      const markdown = `
* The system shall encrypt passwords
* While offline, the system shall cache data
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements.filter((s) => s.source === 'bullet')).toHaveLength(2);
    });

    it('should ignore non-EARS bullet items', () => {
      const markdown = `
- This is just a note
- Another comment
- The system shall validate input
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements).toHaveLength(1);
      expect(result.statements[0].text).toContain('shall validate');
    });
  });

  describe('code block skipping', () => {
    it('should not detect EARS inside code blocks', () => {
      const markdown = `
\`\`\`typescript
// The system shall not be detected here
function validate() {
  // When user clicks, the system shall respond
}
\`\`\`

The system shall be detected outside code block
`;
      const result = parseMarkdownEARS(markdown);

      // Only the statement outside code block should be detected
      expect(result.statements).toHaveLength(1);
      expect(result.statements[0].lineNumber).toBeGreaterThan(5);
    });

    it('should track skipped lines', () => {
      const markdown = `
Line 1
\`\`\`
Code line 1
Code line 2
\`\`\`
Line after code
`;
      const result = parseMarkdownEARS(markdown);

      // 2 lines for ``` markers + 2 code lines = 4 skipped
      expect(result.skippedLines).toBe(4);
    });
  });

  describe('line number accuracy', () => {
    it('should report correct line numbers for table statements', () => {
      const markdown = `Line 1
Line 2
| ID | Requirement |
|----|-------------|
| REQ-001 | The system shall work |
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].lineNumber).toBe(5);
    });

    it('should report correct line numbers for bullet statements', () => {
      const markdown = `Line 1
Line 2
Line 3
- The system shall validate
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].lineNumber).toBe(4);
    });
  });

  describe('EARS pattern detection', () => {
    it('should detect ubiquitous pattern', () => {
      const markdown = `- The system shall store user data`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].validation.valid).toBe(true);
      expect(result.statements[0].validation.patternMatch?.type).toBe('ubiquitous');
    });

    it('should detect event-driven pattern', () => {
      const markdown = `- When user submits form, the system shall validate input`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].validation.valid).toBe(true);
      expect(result.statements[0].validation.patternMatch?.type).toBe('event-driven');
    });

    it('should detect state-driven pattern', () => {
      const markdown = `- While system is offline, the system shall queue requests`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].validation.valid).toBe(true);
      expect(result.statements[0].validation.patternMatch?.type).toBe('state-driven');
    });

    it('should detect unwanted pattern', () => {
      const markdown = `- The system shall not expose passwords`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].validation.valid).toBe(true);
      expect(result.statements[0].validation.patternMatch?.type).toBe('unwanted');
    });

    it('should detect optional pattern', () => {
      const markdown = `- If premium user, then the system shall enable advanced features`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].validation.valid).toBe(true);
      expect(result.statements[0].validation.patternMatch?.type).toBe('optional');
    });
  });

  describe('Markdown formatting removal', () => {
    it('should remove bold markers', () => {
      const markdown = `- The **system** shall **validate** input`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].text).toBe('The system shall validate input');
    });

    it('should remove italic markers', () => {
      const markdown = `- The *system* shall _validate_ input`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].text).toBe('The system shall validate input');
    });

    it('should remove inline code markers', () => {
      const markdown = '- The `system` shall return `JSON`';
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].text).toBe('The system shall return JSON');
    });

    it('should remove link formatting', () => {
      const markdown = `- The [system](./system.md) shall [validate](./validate.md) input`;
      const result = parseMarkdownEARS(markdown);

      expect(result.statements[0].text).toBe('The system shall validate input');
    });
  });

  describe('statistics', () => {
    it('should calculate correct statistics', () => {
      const markdown = `
| ID | Req |
|----|-----|
| R1 | The system shall work |

- When error, the system shall log
- Not an EARS statement

The system shall process data
`;
      const result = parseMarkdownEARS(markdown);

      expect(result.stats.tableStatements).toBe(1);
      expect(result.stats.bulletStatements).toBe(1);
      expect(result.stats.plainStatements).toBe(1);
      expect(result.stats.validStatements).toBe(3);
    });
  });

  describe('extractValidEARS convenience function', () => {
    it('should return only valid EARS statements', () => {
      const markdown = `
- The system shall validate
- Not a valid EARS
- When event occurs, the system shall respond
`;
      const valid = extractValidEARS(markdown);

      expect(valid.length).toBeGreaterThanOrEqual(2);
      valid.forEach((s) => {
        expect(s.validation.valid).toBe(true);
      });
    });
  });

  describe('options', () => {
    it('should respect confidenceThreshold option', () => {
      const markdown = `- The system shall work`;
      const lowThreshold = parseMarkdownEARS(markdown, { confidenceThreshold: 0.5 });
      const highThreshold = parseMarkdownEARS(markdown, { confidenceThreshold: 0.99 });

      // Lower threshold should be more permissive
      expect(lowThreshold.statements.length).toBeGreaterThanOrEqual(
        highThreshold.statements.length
      );
    });

    it('should respect includePlainText option', () => {
      const markdown = `The system shall process data`;
      
      const withPlain = parseMarkdownEARS(markdown, { includePlainText: true });
      const withoutPlain = parseMarkdownEARS(markdown, { includePlainText: false });

      expect(withPlain.stats.plainStatements).toBe(1);
      expect(withoutPlain.stats.plainStatements).toBe(0);
    });

    it('should respect custom requirementIdPattern', () => {
      const markdown = `- CUSTOM-123: The system shall work`;
      const result = parseMarkdownEARS(markdown, {
        requirementIdPattern: /\b(CUSTOM-\d+)\b/,
      });

      expect(result.statements[0].requirementId).toBe('CUSTOM-123');
    });
  });
});
