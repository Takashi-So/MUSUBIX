/**
 * @fileoverview Sanitizer type definitions
 * @module @nahisaho/musubix-security/analysis/sanitizers/types
 * @trace REQ-SEC-001
 */

import type { TaintSinkCategory } from '../../types/taint.js';

/**
 * Sanitizer completeness level
 */
export type SanitizerCompleteness = 'complete' | 'partial' | 'conditional';

/**
 * Sanitizer definition for taint analysis
 * @trace REQ-SEC-001
 */
export interface SanitizerDefinition {
  /** Unique sanitizer ID */
  id: string;
  /** Function/method name */
  name: string;
  /** Alternative names for this sanitizer */
  aliases?: string[];
  /** Regex pattern for matching function names */
  namePattern?: string;
  /** Package/module containing the sanitizer */
  package?: string;
  /** Sink categories this sanitizer protects against */
  protects: TaintSinkCategory[];
  /** Whether sanitization is complete, partial, or conditional */
  completeness: SanitizerCompleteness;
  /** Argument index that gets sanitized (for transform functions) */
  sanitizedArg?: number;
  /** Whether the sanitizer returns sanitized data */
  returnsClean: boolean;
  /** Description of the sanitizer */
  description: string;
  /** Caveats or limitations */
  caveats?: string;
  /** Whether this sanitizer is enabled by default */
  enabled: boolean;
  /** Tags for filtering */
  tags: string[];
}

/**
 * Sanitizer match result
 */
export interface SanitizerMatchResult {
  /** Definition that matched */
  definition: SanitizerDefinition;
  /** Function name that matched */
  functionName: string;
  /** Whether sanitization is complete */
  isComplete: boolean;
  /** Any caveats to consider */
  caveats?: string;
}

/**
 * Sanitizer detector interface
 */
export interface ISanitizerDetector {
  /** Check if an expression is sanitized for a given sink category */
  isSanitized(
    expression: string,
    sinkCategory: TaintSinkCategory
  ): SanitizerMatchResult | undefined;

  /** Register custom sanitizer definition */
  registerSanitizer(definition: SanitizerDefinition): void;

  /** Get all registered sanitizers */
  getSanitizers(): readonly SanitizerDefinition[];
}

/**
 * Sanitizer detector options
 */
export interface SanitizerDetectorOptions {
  /** Custom sanitizers to add */
  customSanitizers?: SanitizerDefinition[];
  /** Packages to include */
  packages?: string[];
  /** Whether to include partial sanitizers */
  includePartial?: boolean;
}
