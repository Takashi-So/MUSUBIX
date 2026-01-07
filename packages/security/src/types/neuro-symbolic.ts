/**
 * @fileoverview Neuro-Symbolic intelligence type definitions
 * @module @nahisaho/musubix-security/types/neuro-symbolic
 * @trace DES-SEC2-INT-001, REQ-SEC2-INT-001, REQ-SEC2-INT-002, REQ-SEC2-INT-003
 */

import type { Vulnerability, Severity } from './vulnerability.js';
import type { TaintPath } from './taint.js';

/**
 * Evidence type for symbolic reasoning
 */
export type EvidenceType = 
  | 'pattern-match'     // Pattern matched in knowledge graph
  | 'rule-inference'    // Inferred from security rules
  | 'knowledge-graph'   // Retrieved from YATA
  | 'static-analysis'   // AST analysis result
  | 'data-flow';        // Data flow analysis result

/**
 * Symbolic reasoning evidence
 * @trace REQ-SEC2-INT-002
 */
export interface Evidence {
  /** Evidence type */
  type: EvidenceType;
  
  /** Source of evidence (pattern name, rule ID, etc.) */
  source: string;
  
  /** Detailed description */
  description: string;
  
  /** Confidence weight (0.0-1.0) */
  weight: number;
  
  /** Related CWEs */
  relatedCWEs?: string[];
}

/**
 * Neural (LLM) analysis result
 * @trace REQ-SEC2-INT-001
 */
export interface NeuralResult {
  /** Confidence score (0.0-1.0) */
  confidence: number;
  
  /** Generated explanation */
  explanation: string;
  
  /** Suggested severity */
  suggestedSeverity: Severity;
  
  /** Suggested fixes */
  suggestedFixes: string[];
  
  /** Model used */
  model: string;
  
  /** Token usage */
  tokenUsage?: {
    prompt: number;
    completion: number;
    total: number;
  };
  
  /** Response time in milliseconds */
  latency: number;
}

/**
 * Symbolic validation result
 * @trace REQ-SEC2-INT-002
 */
export interface SymbolicResult {
  /** Whether the finding is valid according to symbolic rules */
  valid: boolean;
  
  /** Evidence supporting the decision */
  evidence: Evidence[];
  
  /** Matched patterns */
  matchedPatterns: string[];
  
  /** Applied rules */
  appliedRules: string[];
  
  /** Knowledge graph query results */
  knowledgeGraphMatches?: KnowledgeGraphMatch[];
}

/**
 * Knowledge graph match
 */
export interface KnowledgeGraphMatch {
  /** Entity URI */
  entityUri: string;
  
  /** Entity type */
  entityType: string;
  
  /** Match score (0.0-1.0) */
  score: number;
  
  /** Related entities */
  relatedEntities: string[];
}

/**
 * Final decision from Neuro-Symbolic integration
 */
export type FinalDecision = 
  | 'confirmed'      // High confidence vulnerability
  | 'rejected'       // False positive
  | 'needs-review';  // Requires human review

/**
 * Neuro-Symbolic integration result
 * @trace REQ-SEC2-INT-002
 */
export interface NeuroSymbolicResult {
  /** Neural (LLM) confidence */
  neuralConfidence: number;
  
  /** Symbolic validation result */
  symbolicValid: boolean;
  
  /** Final decision based on integration rules */
  finalDecision: FinalDecision;
  
  /** Neural analysis explanation */
  neuralExplanation: string;
  
  /** Symbolic reasoning evidence */
  symbolicEvidence: Evidence[];
  
  /** Combined confidence score */
  combinedConfidence: number;
  
  /** Decision rationale */
  rationale: string;
}

/**
 * Integration options
 */
export interface IntegrationOptions {
  /** Neural confidence threshold (default: 0.8) */
  neuralThreshold?: number;
  
  /** Require symbolic validation */
  requireSymbolicValidation?: boolean;
  
  /** LLM provider to use */
  llmProvider?: 'openai' | 'anthropic' | 'azure';
  
  /** Maximum LLM tokens */
  maxTokens?: number;
  
  /** Knowledge graph query depth */
  kgQueryDepth?: number;
}

/**
 * Neuro-Symbolic core interface
 * @trace DES-SEC2-INT-001
 */
export interface INeuroSymbolicCore {
  /**
   * Integrate neural and symbolic analysis for a vulnerability
   * @trace REQ-SEC2-INT-003
   */
  integrate(
    vulnerability: Vulnerability,
    options?: IntegrationOptions
  ): Promise<NeuroSymbolicResult>;
  
  /**
   * Validate a finding using symbolic reasoning only
   */
  validateSymbolic(
    vulnerability: Vulnerability
  ): Promise<SymbolicResult>;
  
  /**
   * Analyze a finding using neural (LLM) only
   */
  analyzeNeural(
    vulnerability: Vulnerability,
    context?: string
  ): Promise<NeuralResult>;
  
  /**
   * Calculate combined confidence score
   */
  calculateScore(
    neuralResult: NeuralResult,
    symbolicResult: SymbolicResult
  ): number;
}

/**
 * LLM analyzer interface
 * @trace DES-SEC2-INT-002
 */
export interface ILLMAnalyzer {
  /**
   * Analyze vulnerability context
   */
  analyzeContext(
    codeSnippet: string,
    vulnerability: Vulnerability
  ): Promise<NeuralResult>;
  
  /**
   * Generate human-readable explanation
   */
  generateExplanation(
    vulnerability: Vulnerability,
    dataFlow?: TaintPath
  ): Promise<string>;
  
  /**
   * Suggest fix for vulnerability
   */
  suggestFix(
    vulnerability: Vulnerability
  ): Promise<string[]>;
}

/**
 * Knowledge query interface
 * @trace DES-SEC2-INT-003
 */
export interface IKnowledgeQuery {
  /**
   * Query for matching security patterns
   */
  queryPattern(
    codePattern: string,
    cwes?: string[]
  ): Promise<KnowledgeGraphMatch[]>;
  
  /**
   * Match against known vulnerability rules
   */
  matchRule(
    vulnerability: Vulnerability
  ): Promise<string[]>;
  
  /**
   * Infer potential vulnerabilities from code pattern
   */
  inferVulnerability(
    codeSnippet: string
  ): Promise<string[]>;
}
