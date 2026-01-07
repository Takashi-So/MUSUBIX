/**
 * @fileoverview Result aggregation type definitions
 * @module @nahisaho/musubix-security/types/result
 * @trace DES-SEC2-ORCH-003, REQ-SEC2-REPORT-001
 */

import type { Vulnerability, Severity } from './vulnerability.js';
import type { TaintPath } from './taint.js';
import type { Secret } from './secret.js';
import type { AuditResult } from './dependency.js';

/**
 * Detection source type
 */
export type DetectionSource = 
  | 'sast'              // Static analysis
  | 'taint'             // Taint analysis
  | 'secret'            // Secret detection
  | 'dependency'        // Dependency audit
  | 'container'         // Container scan
  | 'iac'               // IaC check
  | 'ai'                // AI/ML vulnerability
  | 'neuro-symbolic';   // Neuro-Symbolic integration

/**
 * Aggregated vulnerability with source tracking
 */
export interface AggregatedVulnerability extends Vulnerability {
  /** Detection sources (may be multiple) */
  sources: DetectionSource[];
  
  /** Original vulnerability IDs before aggregation */
  originalIds: string[];
  
  /** Whether this is a duplicate detection */
  isDuplicate: boolean;
  
  /** Priority score (calculated from severity, confidence, etc.) */
  priorityScore: number;
  
  /** Risk score (0-100) */
  riskScore: number;
  
  /** Related findings (similar vulnerabilities) */
  relatedFindings?: string[];
}

/**
 * Analysis result from any analyzer
 */
export interface AnalysisResult {
  /** Result type identifier */
  type: DetectionSource;
  
  /** Vulnerabilities found */
  vulnerabilities: Vulnerability[];
  
  /** Taint paths (if taint analysis) */
  taintPaths?: TaintPath[];
  
  /** Secrets (if secret detection) */
  secrets?: Secret[];
  
  /** Audit result (if dependency audit) */
  auditResult?: AuditResult;
  
  /** Analysis duration in milliseconds */
  duration: number;
  
  /** Timestamp */
  timestamp: Date;
}

/**
 * Aggregated result combining all analyzers
 * @trace DES-SEC2-ORCH-003
 */
export interface AggregatedResult {
  /** Aggregated vulnerabilities (deduplicated and prioritized) */
  vulnerabilities: AggregatedVulnerability[];
  
  /** Total risk score (0-100) */
  riskScore: number;
  
  /** Summary by severity */
  bySeverity: Record<Severity, number>;
  
  /** Summary by source */
  bySource: Record<DetectionSource, number>;
  
  /** Duplicates removed */
  duplicatesRemoved: number;
  
  /** Analysis sources included */
  sources: DetectionSource[];
  
  /** Aggregation timestamp */
  aggregatedAt: Date;
  
  /** Aggregation duration */
  aggregationDuration: number;
}

/**
 * Deduplication rule
 */
export interface DeduplicationRule {
  /** Rule ID */
  id: string;
  
  /** Fields to compare */
  compareFields: (keyof Vulnerability)[];
  
  /** Similarity threshold (0.0-1.0) */
  similarityThreshold: number;
  
  /** Merge strategy when duplicates found */
  mergeStrategy: 'keep-first' | 'keep-highest-confidence' | 'merge';
}

/**
 * Prioritization criteria
 */
export interface PrioritizationCriteria {
  /** Severity weight */
  severityWeight: number;
  
  /** Confidence weight */
  confidenceWeight: number;
  
  /** Exploitability weight */
  exploitabilityWeight: number;
  
  /** Impact weight */
  impactWeight: number;
  
  /** Custom scoring function */
  customScorer?: (vuln: Vulnerability) => number;
}

/**
 * Default prioritization criteria
 */
export const DEFAULT_PRIORITIZATION: PrioritizationCriteria = {
  severityWeight: 0.4,
  confidenceWeight: 0.3,
  exploitabilityWeight: 0.2,
  impactWeight: 0.1,
};

/**
 * Severity weights for scoring
 */
export const SEVERITY_SCORES: Record<Severity, number> = {
  critical: 100,
  high: 80,
  medium: 50,
  low: 20,
  info: 5,
};

/**
 * Result aggregator interface
 * @trace DES-SEC2-ORCH-003
 */
export interface IResultAggregator {
  /**
   * Aggregate results from multiple analyzers
   */
  aggregate(results: AnalysisResult[]): AggregatedResult;
  
  /**
   * Deduplicate vulnerabilities
   */
  deduplicate(
    vulnerabilities: Vulnerability[],
    rules?: DeduplicationRule[]
  ): Vulnerability[];
  
  /**
   * Prioritize vulnerabilities
   */
  prioritize(
    vulnerabilities: Vulnerability[],
    criteria?: PrioritizationCriteria
  ): Vulnerability[];
  
  /**
   * Calculate overall risk score
   */
  calculateRiskScore(vulnerabilities: Vulnerability[]): number;
  
  /**
   * Merge similar vulnerabilities
   */
  mergeSimilar(
    vuln1: Vulnerability,
    vuln2: Vulnerability
  ): Vulnerability;
}
