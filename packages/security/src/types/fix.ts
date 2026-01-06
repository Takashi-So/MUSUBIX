/**
 * @fileoverview Fix suggestion and verification type definitions
 * @module @nahisaho/musubix-security/types/fix
 * @trace REQ-SEC-FIX-001, REQ-SEC-FIX-002, REQ-SEC-FIX-003
 */

import type { SourceLocation, Severity } from './vulnerability.js';

/**
 * Fix strategy type
 * @trace REQ-SEC-FIX-001
 */
export type FixStrategy =
  | 'parameterized-query' // SQL/NoSQL injection
  | 'html-escape' // XSS
  | 'command-escape' // Command injection
  | 'path-validation' // Path traversal
  | 'url-validation' // Open redirect, SSRF
  | 'input-validation' // Generic input validation
  | 'authentication' // Auth fixes
  | 'authorization' // Access control
  | 'encryption' // Sensitive data
  | 'sanitization' // Generic sanitization
  | 'configuration' // Config changes
  | 'dependency-update'; // Vulnerable dependencies

/**
 * Code edit to apply
 * @trace DES-SEC-FIX-001
 */
export interface CodeEdit {
  /** Source code location to edit */
  location: SourceLocation;
  /** Original code to replace */
  originalCode: string;
  /** New code to insert */
  newCode: string;
  /** Description of the change */
  description: string;
}

/**
 * Import statement to add
 */
export interface ImportEdit {
  /** Module to import from */
  module: string;
  /** Named imports */
  namedImports?: string[];
  /** Default import name */
  defaultImport?: string;
  /** Namespace import name */
  namespaceImport?: string;
  /** Insert at line (0 for top of file) */
  insertLine: number;
}

/**
 * Fix suggestion for a vulnerability
 * @trace REQ-SEC-FIX-001
 */
export interface Fix {
  /** Unique fix ID (e.g., "FIX-2026-001") */
  id: string;
  /** Reference to the vulnerability being fixed */
  vulnerabilityId: string;
  /** Reference to the taint path if applicable */
  taintPathId?: string;
  /** Fix strategy used */
  strategy: FixStrategy;
  /** Human-readable title */
  title: string;
  /** Detailed description of the fix */
  description: string;
  /** Code edits to apply */
  edits: CodeEdit[];
  /** Import statements to add */
  imports: ImportEdit[];
  /** Confidence in fix correctness (0.0 - 1.0) */
  confidence: number;
  /** Whether this fix may change behavior */
  breakingChange: boolean;
  /** Required new dependencies */
  newDependencies?: {
    name: string;
    version: string;
    dev?: boolean;
  }[];
  /** Explanation of why this fix works */
  rationale: string;
  /** Alternative fix approaches */
  alternatives?: string[];
  /** Generated timestamp */
  generatedAt: Date;
  /** LLM model used if AI-generated */
  generatedBy?: string;
}

/**
 * Fix generation options
 */
export interface FixGenerationOptions {
  /** Preferred fix strategies */
  preferredStrategies?: FixStrategy[];
  /** Use AI-assisted fix generation */
  useAI?: boolean;
  /** AI model to use */
  aiModel?: string;
  /** Generate multiple alternatives */
  generateAlternatives?: boolean;
  /** Maximum alternatives per vulnerability */
  maxAlternatives?: number;
  /** Preserve code style */
  preserveStyle?: boolean;
  /** Target language/framework */
  targetFramework?: string;
}

/**
 * Verification status
 * @trace REQ-SEC-FIX-002
 */
export type VerificationStatus =
  | 'verified' // Formally verified as correct
  | 'unverified' // Not verified yet
  | 'failed' // Verification failed
  | 'timeout' // Verification timed out
  | 'unsupported'; // Cannot be verified

/**
 * Formal verification result
 * @trace REQ-SEC-FIX-002
 */
export interface VerificationResult {
  /** Fix ID being verified */
  fixId: string;
  /** Verification status */
  status: VerificationStatus;
  /** Whether the fix eliminates the vulnerability */
  eliminatesVulnerability: boolean;
  /** Whether the fix preserves program semantics */
  preservesSemantics: boolean;
  /** Whether any regressions were detected */
  noRegressions: boolean;
  /** Verification method used */
  method: 'z3-smt' | 'hoare-logic' | 'type-checking' | 'static-analysis';
  /** Detailed verification output */
  details?: string;
  /** Verification duration in milliseconds */
  duration: number;
  /** Verification timestamp */
  timestamp: Date;
  /** Error message if verification failed */
  error?: string;
}

/**
 * Fix application status
 * @trace REQ-SEC-FIX-003
 */
export type ApplyStatus =
  | 'success' // Fix applied successfully
  | 'partial' // Some edits applied
  | 'failed' // Application failed
  | 'conflict' // Code has changed
  | 'rejected'; // User rejected

/**
 * Result of applying a fix
 * @trace REQ-SEC-FIX-003
 */
export interface ApplyResult {
  /** Fix ID that was applied */
  fixId: string;
  /** Application status */
  status: ApplyStatus;
  /** Files modified */
  modifiedFiles: string[];
  /** Edits that were applied */
  appliedEdits: CodeEdit[];
  /** Edits that failed to apply */
  failedEdits?: {
    edit: CodeEdit;
    reason: string;
  }[];
  /** Backup file paths */
  backupPaths?: string[];
  /** Whether backup was created */
  backupCreated: boolean;
  /** Error message if failed */
  error?: string;
  /** Application timestamp */
  timestamp: Date;
}

/**
 * Fix batch for multiple vulnerabilities
 */
export interface FixBatch {
  /** Batch ID */
  id: string;
  /** Fixes in this batch */
  fixes: Fix[];
  /** Combined verification result */
  verification?: VerificationResult;
  /** Whether batch can be applied atomically */
  atomic: boolean;
  /** Files affected by this batch */
  affectedFiles: string[];
  /** Estimated impact level */
  impactLevel: Severity;
  /** Creation timestamp */
  createdAt: Date;
}

/**
 * Fix template for common patterns
 */
export interface FixTemplate {
  /** Template ID */
  id: string;
  /** Template name */
  name: string;
  /** Vulnerability type this template addresses */
  vulnerabilityType: string;
  /** Fix strategy */
  strategy: FixStrategy;
  /** Template code with placeholders */
  template: string;
  /** Placeholder definitions */
  placeholders: {
    name: string;
    description: string;
    required: boolean;
    defaultValue?: string;
  }[];
  /** Required imports */
  imports: ImportEdit[];
  /** When to use this template */
  applicableWhen: string;
  /** Example usage */
  example?: {
    before: string;
    after: string;
  };
}
