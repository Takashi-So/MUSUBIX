/**
 * Markdown EARS Parser
 *
 * Extracts EARS patterns from Markdown documents including tables, bullet lists,
 * and plain text while skipping code blocks.
 *
 * @packageDocumentation
 * @module validators/markdown-ears-parser
 *
 * @see REQ-VAL-001 - Markdown内EARS形式検出
 * @see TSK-VAL-001 - Markdown内EARS検出タスク
 */

import { EARSValidator, type EARSValidationResult } from './ears-validator.js';

/**
 * Extracted EARS statement from Markdown
 */
export interface ExtractedEARS {
  /** Original text containing the EARS pattern */
  text: string;
  /** Line number (1-based) */
  lineNumber: number;
  /** Source format */
  source: 'table' | 'bullet' | 'plain';
  /** EARS validation result */
  validation: EARSValidationResult;
  /** Column index for table cells (0-based) */
  columnIndex?: number;
  /** Requirement ID if detected */
  requirementId?: string;
}

/**
 * Markdown EARS parsing result
 */
export interface MarkdownEARSResult {
  /** Successfully extracted EARS statements */
  statements: ExtractedEARS[];
  /** Total lines processed */
  totalLines: number;
  /** Lines skipped (code blocks, etc.) */
  skippedLines: number;
  /** Statistics */
  stats: {
    tableStatements: number;
    bulletStatements: number;
    plainStatements: number;
    validStatements: number;
    invalidStatements: number;
  };
}

/**
 * Markdown EARS Parser options
 */
export interface MarkdownEARSParserOptions {
  /** Minimum confidence for EARS pattern detection */
  confidenceThreshold?: number;
  /** Whether to extract from plain text (not just tables/bullets) */
  includePlainText?: boolean;
  /** Regex pattern for requirement IDs (e.g., REQ-001) */
  requirementIdPattern?: RegExp;
}

const DEFAULT_OPTIONS: Required<MarkdownEARSParserOptions> = {
  confidenceThreshold: 0.7,
  includePlainText: true,
  requirementIdPattern: /\b(REQ-[A-Z0-9-]+)\b/i,
};

/**
 * Markdown EARS Parser
 *
 * Extracts and validates EARS patterns from Markdown documents.
 */
export class MarkdownEARSParser {
  private options: Required<MarkdownEARSParserOptions>;
  private validator: EARSValidator;

  constructor(options?: MarkdownEARSParserOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
    this.validator = new EARSValidator({
      confidenceThreshold: this.options.confidenceThreshold,
    });
  }

  /**
   * Parse Markdown content and extract EARS statements
   *
   * @param content - Markdown content to parse
   * @returns Parsing result with extracted statements
   */
  parse(content: string): MarkdownEARSResult {
    const lines = content.split('\n');
    const statements: ExtractedEARS[] = [];
    let skippedLines = 0;

    let inCodeBlock = false;
    let inTable = false;
    let tableHeaderParsed = false;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const lineNumber = i + 1;

      // Track code blocks
      if (line.trim().startsWith('```')) {
        inCodeBlock = !inCodeBlock;
        skippedLines++;
        continue;
      }

      if (inCodeBlock) {
        skippedLines++;
        continue;
      }

      // Process table rows
      if (line.trim().startsWith('|')) {
        // Check if this is a table separator line
        if (/^\|[\s-:|]+\|$/.test(line.trim())) {
          tableHeaderParsed = true;
          inTable = true;
          continue;
        }

        // If we haven't seen the separator yet, this might be header
        if (!tableHeaderParsed && /^\|.*\|$/.test(line.trim())) {
          inTable = true;
          continue;
        }

        // Parse table data row
        if (inTable) {
          const extracted = this.parseTableRow(line, lineNumber);
          statements.push(...extracted);
        }
        continue;
      } else {
        // Reset table state when leaving table
        inTable = false;
        tableHeaderParsed = false;
      }

      // Process bullet lists
      if (/^\s*[-*+]\s+/.test(line)) {
        const extracted = this.parseBulletItem(line, lineNumber);
        if (extracted) {
          statements.push(extracted);
        }
        continue;
      }

      // Process plain text if enabled
      if (this.options.includePlainText) {
        const extracted = this.parsePlainText(line, lineNumber);
        if (extracted) {
          statements.push(extracted);
        }
      }
    }

    // Calculate statistics
    const stats = {
      tableStatements: statements.filter((s) => s.source === 'table').length,
      bulletStatements: statements.filter((s) => s.source === 'bullet').length,
      plainStatements: statements.filter((s) => s.source === 'plain').length,
      validStatements: statements.filter((s) => s.validation.valid).length,
      invalidStatements: statements.filter((s) => !s.validation.valid).length,
    };

    return {
      statements,
      totalLines: lines.length,
      skippedLines,
      stats,
    };
  }

  /**
   * Parse a table row and extract EARS patterns from cells
   */
  private parseTableRow(line: string, lineNumber: number): ExtractedEARS[] {
    const results: ExtractedEARS[] = [];

    // Split by | and filter empty cells
    const cells = line
      .split('|')
      .map((cell) => cell.trim())
      .filter((cell) => cell.length > 0);

    for (let colIndex = 0; colIndex < cells.length; colIndex++) {
      const cell = cells[colIndex];

      // Check if cell contains EARS keywords
      if (this.containsEARSKeywords(cell)) {
        const text = this.cleanText(cell);
        const validation = this.validator.validateRequirement(text);

        // Only include if it matches an EARS pattern
        if (validation.patternMatch || this.containsEARSKeywords(text)) {
          results.push({
            text,
            lineNumber,
            source: 'table',
            validation,
            columnIndex: colIndex,
            requirementId: this.extractRequirementId(line),
          });
        }
      }
    }

    return results;
  }

  /**
   * Parse a bullet list item and extract EARS pattern
   */
  private parseBulletItem(
    line: string,
    lineNumber: number
  ): ExtractedEARS | null {
    // Remove bullet marker
    const text = line.replace(/^\s*[-*+]\s+/, '').trim();

    if (!this.containsEARSKeywords(text)) {
      return null;
    }

    const cleanedText = this.cleanText(text);
    const validation = this.validator.validateRequirement(cleanedText);

    return {
      text: cleanedText,
      lineNumber,
      source: 'bullet',
      validation,
      requirementId: this.extractRequirementId(line),
    };
  }

  /**
   * Parse plain text and extract EARS pattern
   */
  private parsePlainText(
    line: string,
    lineNumber: number
  ): ExtractedEARS | null {
    const text = line.trim();

    if (!text || !this.containsEARSKeywords(text)) {
      return null;
    }

    const cleanedText = this.cleanText(text);
    const validation = this.validator.validateRequirement(cleanedText);

    // Only include if it's a valid EARS pattern
    if (!validation.valid && !validation.patternMatch) {
      return null;
    }

    return {
      text: cleanedText,
      lineNumber,
      source: 'plain',
      validation,
      requirementId: this.extractRequirementId(line),
    };
  }

  /**
   * Check if text contains EARS keywords
   */
  private containsEARSKeywords(text: string): boolean {
    const keywords = /\b(shall|when|while|if\s+.+\s+then|shall\s+not)\b/i;
    return keywords.test(text);
  }

  /**
   * Clean text by removing Markdown formatting
   */
  private cleanText(text: string): string {
    return (
      text
        // Remove bold/italic markers
        .replace(/\*\*(.+?)\*\*/g, '$1')
        .replace(/\*(.+?)\*/g, '$1')
        .replace(/__(.+?)__/g, '$1')
        .replace(/_(.+?)_/g, '$1')
        // Remove inline code
        .replace(/`(.+?)`/g, '$1')
        // Remove links, keep text
        .replace(/\[(.+?)\]\(.+?\)/g, '$1')
        // Remove requirement IDs at the start if followed by colon/dash
        .replace(/^REQ-[A-Z0-9-]+[:\-]\s*/i, '')
        .trim()
    );
  }

  /**
   * Extract requirement ID from text
   */
  private extractRequirementId(text: string): string | undefined {
    const match = text.match(this.options.requirementIdPattern);
    return match?.[1];
  }
}

/**
 * Convenience function to parse Markdown and extract EARS
 *
 * @param content - Markdown content
 * @param options - Parser options
 * @returns Parsing result
 */
export function parseMarkdownEARS(
  content: string,
  options?: MarkdownEARSParserOptions
): MarkdownEARSResult {
  const parser = new MarkdownEARSParser(options);
  return parser.parse(content);
}

/**
 * Convenience function to get valid EARS statements only
 *
 * @param content - Markdown content
 * @param options - Parser options
 * @returns Array of valid EARS statements
 */
export function extractValidEARS(
  content: string,
  options?: MarkdownEARSParserOptions
): ExtractedEARS[] {
  const result = parseMarkdownEARS(content, options);
  return result.statements.filter((s) => s.validation.valid);
}
