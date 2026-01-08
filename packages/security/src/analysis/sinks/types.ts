/**
 * @fileoverview Sink definition types for taint analysis
 * @module @nahisaho/musubix-security/analysis/sinks/types
 * @trace REQ-SEC-001
 */

import type { TaintSinkCategory, Severity } from '../../types/index.js';

/**
 * AST pattern for sink matching
 */
export interface SinkASTPattern {
  /** Object/receiver name (e.g., 'db', 'fs', 'child_process') */
  receiver?: string | string[];
  /** Method name to match */
  method?: string | string[];
  /** Property name to match (for property access patterns) */
  property?: string | string[];
  /** Argument index that should not receive tainted data (0-based) */
  vulnerableArg?: number;
  /** Whether multiple arguments are vulnerable */
  vulnerableArgs?: number[];
  /** Pattern for import detection */
  importPattern?: {
    module: string | RegExp;
    named?: string[];
    default?: boolean;
  };
}

/**
 * Sink definition for taint analysis
 * @trace REQ-SEC-001
 */
export interface SinkDefinition {
  /** Unique sink definition ID */
  id: string;
  /** Human-readable name */
  name: string;
  /** Sink category */
  category: TaintSinkCategory;
  /** Severity if tainted data reaches this sink */
  severity: Severity;
  /** Framework this sink is associated with */
  framework?: string;
  /** AST patterns to match this sink */
  patterns: SinkASTPattern[];
  /** Sanitizers that can protect this sink */
  expectedSanitizers: string[];
  /** Description of this sink */
  description: string;
  /** Whether this sink is enabled by default */
  enabled: boolean;
  /** Tags for filtering/grouping */
  tags: string[];
  /** CWE IDs associated with this sink */
  relatedCWE: string[];
  /** OWASP Top 10 category */
  owaspCategory?: string;
}

/**
 * Sink match result
 */
export interface SinkMatchResult {
  /** Definition that matched */
  definition: SinkDefinition;
  /** Matched pattern */
  pattern: SinkASTPattern;
  /** Function/method name being called */
  functionName: string;
  /** Argument index receiving tainted data */
  argumentIndex: number;
  /** Expression at this sink */
  expression: string;
}

/**
 * Sink detector interface
 */
export interface ISinkDetector {
  /** Detect sinks in an AST node */
  detect(
    ast: unknown,
    options?: SinkDetectorOptions
  ): Promise<SinkMatchResult[]>;
  
  /** Register custom sink definition */
  registerSink(definition: SinkDefinition): void;
  
  /** Get all registered sinks */
  getSinks(): readonly SinkDefinition[];
}

/**
 * Sink detector options
 */
export interface SinkDetectorOptions {
  /** Categories to include */
  categories?: TaintSinkCategory[];
  /** Severity threshold */
  minSeverity?: Severity;
  /** Custom sinks to add */
  customSinks?: SinkDefinition[];
  /** Frameworks to include */
  frameworks?: string[];
}
