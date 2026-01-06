/**
 * @fileoverview Taint analysis type definitions
 * @module @nahisaho/musubix-security/types/taint
 * @trace REQ-SEC-TAINT-001, REQ-SEC-TAINT-002, REQ-SEC-TAINT-003, REQ-SEC-TAINT-004
 */

import type { SourceLocation, Severity } from './vulnerability.js';

/**
 * Taint source category
 * @trace REQ-SEC-TAINT-001
 */
export type TaintSourceCategory =
  | 'user-input' // Form data, query params, request body
  | 'database' // Database queries without sanitization
  | 'file-system' // File reads
  | 'network' // External API responses
  | 'environment' // Environment variables
  | 'config' // Configuration files
  | 'cli-args'; // Command line arguments

/**
 * Taint source (where untrusted data enters)
 * @trace REQ-SEC-TAINT-001
 */
export interface TaintSource {
  /** Unique source ID */
  id: string;
  /** Source category */
  category: TaintSourceCategory;
  /** Source code location */
  location: SourceLocation;
  /** Variable/parameter name holding tainted data */
  variableName: string;
  /** Expression that produces tainted data */
  expression: string;
  /** Human-readable description */
  description: string;
  /** Detection confidence */
  confidence: number;
}

/**
 * Taint sink category
 * @trace REQ-SEC-TAINT-002
 */
export type TaintSinkCategory =
  | 'sql-query' // SQL execution
  | 'nosql-query' // NoSQL query
  | 'command-exec' // OS command execution
  | 'file-write' // File system writes
  | 'file-read' // File system reads (path traversal)
  | 'html-output' // HTML rendering (XSS)
  | 'redirect' // URL redirects
  | 'eval' // Code evaluation
  | 'deserialization' // Object deserialization
  | 'ldap-query' // LDAP queries
  | 'xpath-query' // XPath queries
  | 'http-request'; // Outbound HTTP requests (SSRF)

/**
 * Taint sink (where tainted data could cause harm)
 * @trace REQ-SEC-TAINT-002
 */
export interface TaintSink {
  /** Unique sink ID */
  id: string;
  /** Sink category */
  category: TaintSinkCategory;
  /** Source code location */
  location: SourceLocation;
  /** Function/method name being called */
  functionName: string;
  /** Argument index receiving tainted data (0-based) */
  argumentIndex: number;
  /** Expected sanitization functions */
  expectedSanitizers: string[];
  /** Human-readable description */
  description: string;
  /** Severity if tainted data reaches this sink */
  severity: Severity;
}

/**
 * Taint flow step in the propagation path
 * @trace REQ-SEC-TAINT-003
 */
export interface TaintFlowStep {
  /** Step index in the path (0-based) */
  index: number;
  /** Source code location */
  location: SourceLocation;
  /** Expression at this step */
  expression: string;
  /** Variable name holding data at this step */
  variableName?: string;
  /** Type of operation (assignment, call, return, etc.) */
  operation: 'assignment' | 'call' | 'return' | 'parameter' | 'property-access' | 'array-access';
  /** Whether sanitization was applied at this step */
  sanitized: boolean;
  /** Sanitizer function if sanitization was applied */
  sanitizer?: string;
}

/**
 * Complete taint propagation path from source to sink
 * @trace REQ-SEC-TAINT-003
 */
export interface TaintPath {
  /** Unique path ID */
  id: string;
  /** Source where tainted data originates */
  source: TaintSource;
  /** Sink where tainted data is used unsafely */
  sink: TaintSink;
  /** Steps in the propagation path */
  steps: TaintFlowStep[];
  /** Whether any sanitization was applied */
  sanitized: boolean;
  /** Overall path confidence */
  confidence: number;
  /** Path length (number of steps) */
  length: number;
}

/**
 * Taint analysis result
 * @trace REQ-SEC-TAINT-001
 */
export interface TaintResult {
  /** Detected taint sources */
  sources: TaintSource[];
  /** Detected taint sinks */
  sinks: TaintSink[];
  /** Unsafe taint paths (source → sink without proper sanitization) */
  unsafePaths: TaintPath[];
  /** Number of files analyzed */
  analyzedFiles: number;
  /** Analysis duration in milliseconds */
  duration: number;
  /** Analysis timestamp */
  timestamp: Date;
  /** Summary statistics */
  summary: {
    totalSources: number;
    totalSinks: number;
    unsafePathCount: number;
    bySeverity: {
      critical: number;
      high: number;
      medium: number;
      low: number;
    };
    bySourceCategory: Record<TaintSourceCategory, number>;
    bySinkCategory: Record<TaintSinkCategory, number>;
  };
}

/**
 * Taint analysis options
 * @trace REQ-SEC-TAINT-004
 */
export interface TaintAnalysisOptions {
  /** Custom source patterns (regex patterns) */
  customSources?: {
    pattern: string;
    category: TaintSourceCategory;
    description: string;
  }[];
  /** Custom sink patterns */
  customSinks?: {
    pattern: string;
    category: TaintSinkCategory;
    severity: Severity;
    description: string;
  }[];
  /** Additional sanitizer functions to recognize */
  additionalSanitizers?: {
    functionName: string;
    sinkCategories: TaintSinkCategory[];
  }[];
  /** Maximum path depth to track */
  maxPathDepth?: number;
  /** Enable inter-procedural analysis */
  interprocedural?: boolean;
  /** Track through async/await boundaries */
  trackAsync?: boolean;
  /** File patterns to exclude */
  excludePatterns?: string[];
}

/**
 * Known sanitizer function
 */
export interface SanitizerDefinition {
  /** Function name or pattern */
  name: string;
  /** Package/module containing the sanitizer */
  package?: string;
  /** Sink categories this sanitizer protects against */
  protects: TaintSinkCategory[];
  /** Whether sanitization is complete or partial */
  complete: boolean;
  /** Notes about the sanitizer */
  notes?: string;
}

/**
 * Built-in sanitizer definitions
 */
export const BUILTIN_SANITIZERS: SanitizerDefinition[] = [
  // SQL
  { name: 'escape', package: 'mysql', protects: ['sql-query'], complete: true },
  { name: 'escape', package: 'pg', protects: ['sql-query'], complete: true },
  { name: 'parameterize', protects: ['sql-query', 'nosql-query'], complete: true },
  // XSS
  { name: 'escapeHtml', protects: ['html-output'], complete: true },
  { name: 'sanitizeHtml', package: 'sanitize-html', protects: ['html-output'], complete: true },
  { name: 'encode', package: 'html-entities', protects: ['html-output'], complete: true },
  // Command
  { name: 'quote', package: 'shell-quote', protects: ['command-exec'], complete: true },
  // Path
  { name: 'basename', package: 'path', protects: ['file-read', 'file-write'], complete: false, notes: 'Only removes directory components' },
  { name: 'normalize', package: 'path', protects: ['file-read', 'file-write'], complete: false, notes: 'Resolves .. but does not prevent traversal' },
];
