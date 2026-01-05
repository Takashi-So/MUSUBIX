/**
 * Symbolic Reasoning Type Definitions
 *
 * Types for Semantic Code Filter, Hallucination Detection,
 * Constitution Enforcement, and Confidence-Based Routing.
 *
 * Re-exports common types from core and defines symbolic-specific types.
 *
 * @packageDocumentation
 * @module symbolic
 *
 * @see REQ-SYMB-001 - Symbolic Reasoning Enhancement
 * @see DES-SYMB-001 - Symbolic Components Design
 */

// Re-export common types used in symbolic module
export type { ID, Timestamp, Confidence, Priority, Violation, Location } from '../types/common.js';

// ============================================================================
// Explanation Types (REQ-NFR-003)
// ============================================================================

/**
 * Reference to an artifact (code, document, config)
 */
export interface ArtifactRef {
  type: 'code' | 'requirement' | 'design' | 'config' | 'test';
  id: string;
  location?: {
    file?: string;
    line?: number;
    column?: number;
  };
}

/**
 * Evidence supporting a decision
 */
export interface Evidence {
  type:
    | 'symbolic_check'
    | 'neural_inference'
    | 'rule_match'
    | 'counterexample'
    | 'proof'
    | 'requirement'
    | 'verification'
    | 'code'
    | 'security'
    | 'timing'
    | 'artifact'
    | 'traceability'
    | 'constitution';
  source?: string;
  content?: string;
  description?: string;
  artifacts?: ArtifactRef[];
  confidence?: number;
}

/**
 * Explanation for any decision (REQ-NFR-003)
 */
export interface Explanation {
  summary: string;
  reasoning: string[];
  evidence: Evidence[];
  relatedRequirements?: string[];
  confidence?: number;
  generatedAt?: string;
  metadata?: Record<string, unknown>;
}

// ============================================================================
// Semantic Code Filter Types (REQ-SF-001〜003)
// ============================================================================

/**
 * Symbol information in project context
 */
export interface SymbolInfo {
  name: string;
  type: 'class' | 'function' | 'interface' | 'type' | 'variable' | 'constant' | 'enum';
  path: string;
  signature?: string;
  exported?: boolean;
}

/**
 * EARS Requirement reference
 */
export interface EarsRequirement {
  id: string;
  text: string;
  type: 'ubiquitous' | 'event-driven' | 'state-driven' | 'unwanted' | 'optional';
}

/**
 * Project context for filtering
 */
export interface ProjectContext {
  projectPath: string;
  symbols?: SymbolInfo[];
  dependencies?: string[];
  requirements?: EarsRequirement[];
}

/**
 * Code candidate for filtering
 */
export interface CodeCandidate {
  code: string;
  language: string;
  targetFile?: string;
  metadata?: {
    generatedAt?: string;
    model?: string;
    [key: string]: unknown;
  };
}

/**
 * Filter input
 */
export interface FilterInput {
  candidates: CodeCandidate[];
  projectContext: ProjectContext;
  requirements?: EarsRequirement[];
}

/**
 * Hallucination detection item
 */
export interface HallucinationItem {
  type: 'import' | 'function_call' | 'type_reference' | 'module';
  identifier: string;
  location: { line: number; column?: number };
  reason: string;
  suggestions?: string[];
}

/**
 * Hallucination detection result
 */
export interface HallucinationResult {
  hasHallucinations: boolean;
  items: HallucinationItem[];
  explanation: Explanation;
}

/**
 * Constitution article identifier
 */
export type ConstitutionArticle = 'I' | 'II' | 'III' | 'IV' | 'V' | 'VI' | 'VII' | 'VIII' | 'IX';

/**
 * Constitution rule definition
 */
export interface ConstitutionRule {
  article: ConstitutionArticle;
  name: string;
  description: string;
  validator: (input: ConstitutionCheckInput) => Promise<ConstitutionCheckResult>;
}

/**
 * Context for constitution checking
 */
export interface ConstitutionCheckContext {
  hasLibraryStructure: boolean;
  hasCLI: boolean;
  hasTests: boolean;
  earsRequirements: string[];
  traceabilityLinks: Array<{ requirementId: string; designId?: string; taskId?: string }>;
  hasSteeringReference: boolean;
  documentedPatterns: string[];
  hasADR: boolean;
  hasQualityGates: boolean;
}

/**
 * Constitution check input
 */
export interface ConstitutionCheckInput {
  code: string;
  context: ConstitutionCheckContext;
  requirements: EarsRequirement[];
}

/**
 * Constitution violation
 */
export interface ConstitutionViolation {
  article: ConstitutionArticle;
  severity: 'critical' | 'error' | 'warning' | 'info';
  message: string;
  suggestion?: string;
}

/**
 * Constitution check result
 */
export interface ConstitutionCheckResult {
  passed: boolean;
  violations: ConstitutionViolation[];
  explanation: Explanation;
}

/**
 * Constitution report
 */
export interface ConstitutionReport {
  overallPassed: boolean;
  articleResults: Array<{
    article: ConstitutionArticle;
    passed: boolean;
    violations: ConstitutionViolation[];
  }>;
  explanation: Explanation;
}

/**
 * Filter output
 */
export interface FilterOutput {
  accepted: boolean;
  filteredCandidates: CodeCandidate[];
  violations: ConstitutionViolation[];
  hallucinationReport?: HallucinationResult;
  constitutionReport?: ConstitutionReport;
  explanation: Explanation;
}

// ============================================================================
// Confidence-Based Routing Types (REQ-ROUTE-001〜003)
// ============================================================================

/**
 * Confidence breakdown by aspect
 */
export interface ConfidenceBreakdown {
  syntactic: number;
  semantic: number;
  factual: number;
  consistency: number;
}

/**
 * Risk factor
 */
export interface RiskFactor {
  type: 'low_confidence' | 'hallucination_risk' | 'complexity' | 'novel_pattern' | 'security_concern';
  description: string;
  impact: number;
}

/**
 * Confidence estimation result
 */
export interface ConfidenceEstimation {
  score: number;
  breakdown: ConfidenceBreakdown;
  riskFactors: RiskFactor[];
  explanation: Explanation;
}

/**
 * Routing decision
 */
export type RoutingDecision = 'accept' | 'verify' | 'regenerate';

/**
 * Verification requirement
 */
export interface VerificationRequirement {
  type: 'syntax_check' | 'semantic_review' | 'api_verification' | 'pattern_review' | 'test_coverage';
  description: string;
  priority: 'high' | 'medium' | 'low';
}

/**
 * Routing result
 */
export interface RoutingResult {
  decision: RoutingDecision;
  confidence: number;
  verificationRequirements: VerificationRequirement[];
  explanation: Explanation;
}

// ============================================================================
// Error Handling Types (REQ-NFR-004)
// ============================================================================

/**
 * Error handling strategy
 */
export type ErrorHandlingStrategy =
  | 'fail_fast'
  | 'retry_with_backoff'
  | 'graceful_degradation';

/**
 * Fallback action
 */
export type FallbackAction =
  | 'none'
  | 'skip_hallucination_check'
  | 'apply_default_rules'
  | 'use_default_confidence'
  | 'use_cached_response';

/**
 * Audit log entry
 */
export interface AuditLogEntry {
  id: string;
  timestamp: string;
  component: string;
  operation: string;
  result: 'pass' | 'fail' | 'partial';
  details: Record<string, unknown>;
}
