/**
 * @fileoverview Zero-day detection type definitions
 * @module @nahisaho/musubix-security/types/zero-day
 * @trace DES-SEC2-SAST-003, REQ-SEC2-SAST-003
 */

import type { SourceLocation } from './vulnerability.js';

/**
 * Deviation type for zero-day candidates
 */
export type DeviationType = 
  | 'pattern-mismatch'   // Deviation from known safe patterns
  | 'anomaly'            // Statistical anomaly detection
  | 'unsafe-practice';   // Usage of unsafe practices

/**
 * LLM analysis recommendation
 */
export type LLMRecommendation = 
  | 'review'       // Needs security review
  | 'investigate'  // Needs deeper investigation
  | 'safe';        // Likely safe

/**
 * LLM analysis result for zero-day detection
 * @trace REQ-SEC2-SAST-003
 */
export interface LLMAnalysisResult {
  /** Vulnerability likelihood (0.0-1.0) */
  vulnerabilityLikelihood: number;
  
  /** Reasoning for the assessment */
  reasoning: string;
  
  /** Recommended action */
  recommendedAction: LLMRecommendation;
  
  /** Potential CWEs (educated guess) */
  potentialCWEs: string[];
  
  /** Similar known vulnerabilities */
  similarVulnerabilities?: string[];
}

/**
 * Risk factor contributing to zero-day score
 */
export interface RiskFactor {
  /** Factor name */
  name: string;
  
  /** Weight in scoring (0.0-1.0) */
  weight: number;
  
  /** Description of the factor */
  description: string;
  
  /** Score for this factor (0-100) */
  score: number;
}

/**
 * Risk assessment for zero-day candidate
 */
export interface RiskAssessment {
  /** Overall risk score (0-100) */
  score: number;
  
  /** Individual risk factors */
  factors: RiskFactor[];
  
  /** Recommendation based on score */
  recommendation: LLMRecommendation;
  
  /** Confidence in assessment (0.0-1.0) */
  confidence: number;
}

/**
 * Zero-day vulnerability candidate
 * @trace REQ-SEC2-SAST-003
 */
export interface ZeroDayCandidate {
  /** Unique identifier */
  id: string;
  
  /** Source code location */
  location: SourceLocation;
  
  /** Code snippet containing potential vulnerability */
  codeSnippet: string;
  
  /** Type of deviation detected */
  deviationType: DeviationType;
  
  /** Detection confidence (0.0-1.0) */
  confidence: number;
  
  /** LLM assessment (if performed) */
  llmAssessment?: LLMAnalysisResult;
  
  /** Severity is always 'potential' for zero-days */
  severity: 'potential';
  
  /** Explanation of why this was flagged */
  explanation: string;
  
  /** AST pattern that triggered detection */
  triggerPattern?: string;
  
  /** Risk assessment */
  riskAssessment?: RiskAssessment;
  
  /** Detection timestamp */
  detectedAt: Date;
  
  /** Related known patterns (for comparison) */
  relatedPatterns?: string[];
}

/**
 * Zero-day detection options
 */
export interface ZeroDayDetectionOptions {
  /** Enable LLM analysis for candidates */
  enableLLMAnalysis?: boolean;
  
  /** Minimum confidence threshold (0.0-1.0) */
  minConfidence?: number;
  
  /** Maximum candidates to report */
  maxCandidates?: number;
  
  /** Risk score threshold (0-100) */
  riskThreshold?: number;
  
  /** Include pattern comparison */
  includePatternComparison?: boolean;
}

/**
 * Zero-day detection result
 */
export interface ZeroDayResult {
  /** Detected candidates */
  candidates: ZeroDayCandidate[];
  
  /** Files analyzed */
  filesAnalyzed: number;
  
  /** Patterns compared */
  patternsCompared: number;
  
  /** LLM analyses performed */
  llmAnalysesPerformed: number;
  
  /** Analysis duration in milliseconds */
  duration: number;
  
  /** Summary statistics */
  summary: {
    totalCandidates: number;
    highRisk: number;
    mediumRisk: number;
    lowRisk: number;
  };
}

/**
 * Zero-day detector interface
 * @trace DES-SEC2-SAST-003
 */
export interface IZeroDayDetector {
  /**
   * Detect potential zero-day vulnerabilities
   */
  detect(
    files: string[],
    options?: ZeroDayDetectionOptions
  ): Promise<ZeroDayResult>;
  
  /**
   * Analyze a specific code snippet for zero-day patterns
   */
  analyzeSnippet(
    code: string,
    context?: string
  ): Promise<ZeroDayCandidate | null>;
  
  /**
   * Assess risk of a candidate
   */
  assessRisk(candidate: ZeroDayCandidate): Promise<RiskAssessment>;
  
  /**
   * Get LLM analysis for a candidate
   */
  getLLMAnalysis(candidate: ZeroDayCandidate): Promise<LLMAnalysisResult>;
}
