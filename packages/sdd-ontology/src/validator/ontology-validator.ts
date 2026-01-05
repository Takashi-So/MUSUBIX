/**
 * @fileoverview Ontology validator for TTL syntax and semantics
 * @traceability TSK-SDD-ONTO-006, REQ-SDD-ONTO-001-F006
 */

import type { ValidationResult, ValidationError, ValidationWarning } from '../types.js';

/**
 * Ontology validator
 */
export class OntologyValidator {
  /**
   * Validate TTL content (basic syntax check)
   */
  validateTTL(content: string): ValidationResult {
    const errors: ValidationError[] = [];
    const warnings: ValidationWarning[] = [];

    // Check for required prefixes
    if (!content.includes('@prefix')) {
      errors.push({
        code: 'MISSING_PREFIX',
        message: 'TTL file must contain @prefix declarations',
      });
    }

    // Check for unclosed quotes
    const quoteMatches = content.match(/"/g);
    if (quoteMatches && quoteMatches.length % 2 !== 0) {
      errors.push({
        code: 'UNCLOSED_QUOTE',
        message: 'TTL file contains unclosed string literal',
      });
    }

    // Check for statement termination
    const lines = content.split('\n');
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      if (line && !line.startsWith('#') && !line.startsWith('@')) {
        // Non-empty, non-comment, non-directive line should end with . , or ;
        if (!line.endsWith('.') && !line.endsWith(',') && !line.endsWith(';')) {
          // Could be multi-line - just a warning
          if (i === lines.length - 1 || !lines[i + 1].trim().match(/^[.,;]/)) {
            warnings.push({
              code: 'POSSIBLE_UNTERMINATED',
              message: `Line ${i + 1} may be unterminated`,
              suggestion: 'Check statement termination with . , or ;',
            });
          }
        }
      }
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings,
    };
  }

  /**
   * Validate EARS requirement text
   */
  validateEarsText(text: string): ValidationResult {
    const errors: ValidationError[] = [];
    const warnings: ValidationWarning[] = [];

    // Check for EARS keywords
    const hasEarsKeyword = /^(THE|WHEN|WHILE|IF)\s/i.test(text);
    if (!hasEarsKeyword) {
      errors.push({
        code: 'MISSING_EARS_KEYWORD',
        message: 'EARS requirement must start with THE, WHEN, WHILE, or IF',
      });
    }

    // Check for SHALL
    if (!text.includes('SHALL')) {
      errors.push({
        code: 'MISSING_SHALL',
        message: 'EARS requirement must contain SHALL',
      });
    }

    // Check for ambiguous words
    const ambiguousWords = ['might', 'could', 'should', 'may'];
    for (const word of ambiguousWords) {
      if (new RegExp(`\\b${word}\\b`, 'i').test(text)) {
        warnings.push({
          code: 'AMBIGUOUS_WORD',
          message: `Requirement contains ambiguous word: ${word}`,
          suggestion: `Consider using SHALL or SHALL NOT instead of ${word}`,
        });
      }
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings,
    };
  }

  /**
   * Validate C4 element ID format
   */
  validateC4ElementId(id: string): ValidationResult {
    const errors: ValidationError[] = [];
    const warnings: ValidationWarning[] = [];

    // ID should be alphanumeric with hyphens
    if (!/^[a-z][a-z0-9-]*$/i.test(id)) {
      errors.push({
        code: 'INVALID_C4_ID',
        message: 'C4 element ID must start with letter and contain only alphanumeric characters and hyphens',
      });
    }

    // Warn if ID is too long
    if (id.length > 50) {
      warnings.push({
        code: 'LONG_C4_ID',
        message: 'C4 element ID is longer than 50 characters',
        suggestion: 'Consider using a shorter, more descriptive ID',
      });
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings,
    };
  }
}
