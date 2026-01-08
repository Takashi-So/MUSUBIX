/**
 * @fileoverview Source definition types for taint analysis
 * @module @nahisaho/musubix-security/analysis/sources/types
 * @trace REQ-SEC-001
 */

import type { TaintSourceCategory } from '../../types/taint.js';

/**
 * AST pattern for source matching
 */
export interface SourceASTPattern {
  /** Object/receiver name (e.g., 'req', 'ctx', 'process') */
  receiver?: string | string[];
  /** Method name to match */
  method?: string | string[];
  /** Property name to match */
  property?: string | string[];
  /** Specific argument that is tainted (for return values, use -1) */
  taintedArg?: number;
  /** Whether the whole return value is tainted */
  taintedReturn?: boolean;
  /** Pattern for import detection */
  importPattern?: {
    module: string | RegExp;
    named?: string[];
    default?: boolean;
  };
}

/**
 * Source definition for taint analysis
 * @trace REQ-SEC-001
 */
export interface SourceDefinition {
  /** Unique source definition ID */
  id: string;
  /** Human-readable name */
  name: string;
  /** Source category */
  category: TaintSourceCategory;
  /** Framework this source is associated with (e.g., 'express', 'koa', 'next') */
  framework?: string;
  /** AST patterns to match this source */
  patterns: SourceASTPattern[];
  /** Description of this source */
  description: string;
  /** Default confidence level (0-1) */
  confidence: number;
  /** Whether this source is enabled by default */
  enabled: boolean;
  /** Tags for filtering/grouping */
  tags: string[];
  /** CWE IDs this source can lead to if not sanitized */
  relatedCWE?: string[];
}

/**
 * Source match result
 */
export interface SourceMatchResult {
  /** Definition that matched */
  definition: SourceDefinition;
  /** Matched pattern */
  pattern: SourceASTPattern;
  /** Variable name holding tainted data */
  variableName: string;
  /** Expression that produces tainted data */
  expression: string;
  /** Match confidence */
  confidence: number;
}

/**
 * Source detector interface
 */
export interface ISourceDetector {
  /** Detect sources in an AST node */
  detect(
    ast: unknown,
    options?: SourceDetectorOptions
  ): Promise<SourceMatchResult[]>;
  
  /** Register custom source definition */
  registerSource(definition: SourceDefinition): void;
  
  /** Get all registered sources */
  getSources(): readonly SourceDefinition[];
}

/**
 * Source detector options
 */
export interface SourceDetectorOptions {
  /** Categories to include */
  categories?: TaintSourceCategory[];
  /** Frameworks to include */
  frameworks?: string[];
  /** Custom sources to add */
  customSources?: SourceDefinition[];
  /** Minimum confidence threshold */
  minConfidence?: number;
}
