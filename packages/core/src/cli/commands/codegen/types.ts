/**
 * Codegen Command Types
 *
 * Shared type definitions for code generation and analysis
 *
 * @packageDocumentation
 * @module cli/commands/codegen/types
 *
 * @see REQ-CLI-003 - Codegen CLI
 * @see REQ-CG-001 - Code Generation
 */

/**
 * Codegen command options
 */
export interface CodegenOptions {
  output?: string;
  language?: 'typescript' | 'javascript' | 'python';
  template?: string;
  verbose?: boolean;
}

/**
 * Generated code
 */
export interface GeneratedCode {
  filename: string;
  language: string;
  content: string;
  metadata: {
    requirements: string[];
    designElements: string[];
    patterns: string[];
  };
}

/**
 * Generation result
 */
export interface GenerationResult {
  success: boolean;
  files: GeneratedCode[];
  summary: {
    totalFiles: number;
    totalLines: number;
    languages: string[];
  };
  message: string;
}

/**
 * Analysis issue
 */
export interface AnalysisIssue {
  file: string;
  line?: number;
  column?: number;
  severity: 'error' | 'warning' | 'info';
  rule: string;
  message: string;
}

/**
 * Analysis result
 */
export interface AnalysisResult {
  success: boolean;
  issues: AnalysisIssue[];
  metrics: {
    files: number;
    lines: number;
    complexity: number;
    maintainabilityIndex: number;
  };
  summary: {
    errors: number;
    warnings: number;
    info: number;
  };
  message: string;
}

/**
 * Security vulnerability
 */
export interface SecurityVulnerability {
  severity: 'critical' | 'high' | 'medium' | 'low';
  type: string;
  file: string;
  line?: number;
  description: string;
  recommendation: string;
  cwe?: string;
}

/**
 * Security result
 */
export interface SecurityResult {
  success: boolean;
  vulnerabilities: SecurityVulnerability[];
  summary: {
    critical: number;
    high: number;
    medium: number;
    low: number;
  };
  score: number;
  message: string;
}

/**
 * Generated skeleton for 4-file generation
 * @see REQ-BUGFIX-003-01 - 4 file generation
 * @see TSK-BUGFIX-003 - codegen full implementation
 */
export interface GeneratedSkeleton {
  interface: GeneratedCode;
  implementation: GeneratedCode;
  test: GeneratedCode;
  index: GeneratedCode;
}

/**
 * Options for full skeleton generation
 */
export interface FullSkeletonOptions {
  language: 'typescript' | 'javascript' | 'python';
  patterns: string[];
  requirements: string[];
  designId?: string;
  includeTest?: boolean;
}

/**
 * Extended generation options for full skeleton
 */
export interface ExtendedGenerateOptions {
  fullSkeleton?: boolean;
  withTests?: boolean;
}

/**
 * C4 Component definition
 */
export interface C4Component {
  id: string;
  name: string;
  type: string;
  description: string;
  pattern?: string;
}

/**
 * Design Pattern definition
 */
export interface DesignPattern {
  name: string;
  category: string;
  intent: string;
}
