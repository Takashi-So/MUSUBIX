/**
 * Design Command Types
 *
 * Type definitions for design generation and validation
 *
 * @packageDocumentation
 * @module cli/commands/design/types
 */

/**
 * Design command options
 */
export interface DesignOptions {
  output?: string;
  format?: 'mermaid' | 'plantuml' | 'markdown' | 'json';
  verbose?: boolean;
  patterns?: string[];
  level?: 'context' | 'container' | 'component' | 'code';
}

/**
 * C4 Model types
 */
export type C4Level = 'context' | 'container' | 'component' | 'code';

/**
 * C4 Element
 */
export interface C4Element {
  id: string;
  name: string;
  description: string;
  type: 'person' | 'software_system' | 'container' | 'component';
  technology?: string;
  tags?: string[];
}

/**
 * C4 Relationship
 */
export interface C4Relationship {
  source: string;
  target: string;
  description: string;
  technology?: string;
}

/**
 * C4 Model
 */
export interface C4Model {
  level: C4Level;
  title: string;
  elements: C4Element[];
  relationships: C4Relationship[];
}

/**
 * Design pattern
 */
export interface DesignPattern {
  name: string;
  category: 'creational' | 'structural' | 'behavioral';
  intent: string;
  applicability: string[];
  consequences: { positive: string[]; negative: string[] };
}

/**
 * Generate result
 */
export interface GenerateResult {
  success: boolean;
  design: C4Model;
  patterns: DesignPattern[];
  traceability: Array<{ requirement: string; designElement: string }>;
  message: string;
}

/**
 * Validation result
 */
export interface DesignValidationResult {
  success: boolean;
  valid: boolean;
  solidViolations: Array<{
    principle: 'S' | 'O' | 'L' | 'I' | 'D';
    element: string;
    message: string;
    severity: 'error' | 'warning';
  }>;
  traceabilityGaps: Array<{
    requirement: string;
    message: string;
  }>;
  message: string;
}

/**
 * ADR structure
 */
export interface ADRDocument {
  id: string;
  title: string;
  date: string;
  status: 'proposed' | 'accepted' | 'deprecated' | 'superseded';
  context: string;
  decision: string;
  consequences: string[];
  relatedRequirements: string[];
}

/**
 * Pattern detection result
 */
export interface PatternDetectionResult {
  success: boolean;
  patterns: Array<{
    name: string;
    category: string;
    confidence: number;
    location: string;
    suggestion?: string;
  }>;
  recommendations: string[];
  message: string;
}

/**
 * Design review result
 */
export interface DesignReviewResult {
  passed: boolean;
  score: number;
  totalChecks: number;
  passedChecks: number;
  findings: DesignReviewFinding[];
  recommendations: string[];
  constitutionCompliance: {
    articleVII: boolean;
    articleV: boolean;
    articleIX: boolean;
  };
  solidAnalysis: {
    s: { passed: boolean; message: string };
    o: { passed: boolean; message: string };
    l: { passed: boolean; message: string };
    i: { passed: boolean; message: string };
    d: { passed: boolean; message: string };
  };
}

/**
 * Design review finding
 */
export interface DesignReviewFinding {
  severity: 'error' | 'warning' | 'info';
  category: 'solid' | 'pattern' | 'traceability' | 'completeness' | 'consistency';
  element?: string;
  message: string;
  suggestion?: string;
}
