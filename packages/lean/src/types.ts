/**
 * @fileoverview Core type definitions for musubix-lean package
 * @module @nahisaho/musubix-lean/types
 * @traceability REQ-LEAN-001
 */

// ============================================================================
// EARS Types
// ============================================================================

/**
 * EARS requirement patterns
 * @traceability REQ-LEAN-CONV-001
 */
export type EarsPattern =
  | 'ubiquitous'
  | 'event-driven'
  | 'state-driven'
  | 'unwanted'
  | 'optional';

/**
 * Parsed components of an EARS requirement
 */
export interface EarsParsedComponents {
  readonly pattern: EarsPattern;
  readonly trigger?: string; // WHEN clause
  readonly state?: string; // WHILE clause
  readonly condition?: string; // IF clause
  readonly subject: string; // THE system
  readonly action: string; // SHALL/SHALL NOT clause
  readonly negated: boolean; // true for SHALL NOT
}

/**
 * EARS requirement structure
 * @traceability REQ-LEAN-CONV-001
 */
export interface EarsRequirement {
  readonly id: string;
  readonly pattern: EarsPattern;
  readonly text: string;
  readonly parsed?: EarsParsedComponents;
  readonly priority?: string;
}

// ============================================================================
// Lean Types
// ============================================================================

/**
 * Lean version information
 */
export interface LeanVersion {
  readonly major: number;
  readonly minor: number;
  readonly patch: number;
  readonly full: string;
}

/**
 * Lean 4 environment information
 * @traceability REQ-LEAN-CORE-001
 */
export interface LeanEnvironmentInfo {
  readonly installed: boolean;
  readonly version: LeanVersion | null;
  readonly path: string | null;
  readonly lakeVersion: string | null;
  readonly mathlibAvailable: boolean;
  // Aliases for compatibility
  readonly leanInstalled?: boolean;
}

/**
 * Lean hypothesis (assumption)
 */
export interface LeanHypothesis {
  readonly name: string;
  readonly type: string;
  readonly leanCode?: string;
}

/**
 * Lean expression
 */
export interface LeanExpression {
  readonly type: string;
  readonly leanCode: string;
}

/**
 * Lean theorem structure
 * @traceability REQ-LEAN-CONV-001
 */
export interface LeanTheorem {
  readonly id: string;
  readonly name: string;
  readonly statement: string;
  readonly requirementId: string;
  readonly hypotheses: LeanHypothesis[];
  readonly conclusion?: LeanExpression;
  readonly description?: string;
  readonly sourceText?: string;
  readonly leanCode: string;
  readonly proof?: LeanProof;
}

/**
 * Lean proof structure
 */
export interface LeanProof {
  readonly id: string;
  readonly theoremId: string;
  readonly tactics: string[];
  readonly leanCode: string;
  readonly isComplete: boolean;
  readonly generatedAt: string;
}

/**
 * Lean proof sketch with sorry markers
 * @traceability REQ-LEAN-PROOF-003
 */
export interface LeanProofSketch {
  readonly theoremName: string;
  readonly partialProof: string;
  readonly sorryLocations: SorryLocation[];
  readonly hints: string[];
  readonly completionRate: number;
}

/**
 * Location of a sorry marker in proof
 */
export interface SorryLocation {
  readonly line: number;
  readonly expectedType: string;
  readonly hint: string;
}

/**
 * Proof state during construction
 */
export interface ProofState {
  readonly goals: ProofGoal[];
  readonly hypotheses: LeanHypothesis[];
  readonly currentGoal: number;
}

/**
 * A single proof goal
 */
export interface ProofGoal {
  readonly id: number;
  readonly type: string;
  readonly leanCode: string;
}

// ============================================================================
// TypeScript Specification Types
// ============================================================================

/**
 * TypeScript parameter
 */
export interface TypeScriptParameter {
  readonly name: string;
  readonly type: string;
  readonly optional: boolean;
}

/**
 * TypeScript function structure
 * @traceability REQ-LEAN-TS-001
 */
export interface TypeScriptFunction {
  readonly name: string;
  readonly filePath?: string;
  readonly parameters: TypeScriptParameter[];
  readonly returnType: string;
  readonly preconditions: Precondition[];
  readonly postconditions: Postcondition[];
  readonly invariants: Invariant[];
  readonly sourceCode?: string;
}

/**
 * Precondition annotation
 * @traceability REQ-LEAN-TS-002
 */
export interface Precondition {
  readonly expression: string;
  readonly condition?: string;
  readonly description: string;
  readonly source?: 'jsdoc' | 'type-guard' | 'validation';
}

/**
 * Postcondition annotation
 * @traceability REQ-LEAN-TS-003
 */
export interface Postcondition {
  readonly expression: string;
  readonly condition?: string;
  readonly description: string;
  readonly source?: 'jsdoc' | 'return-type' | 'result-type';
}

/**
 * Class invariant
 * @traceability REQ-LEAN-TS-004
 */
export interface Invariant {
  readonly expression: string;
  readonly condition?: string;
  readonly description: string;
}

/**
 * TypeScript specification for conversion
 */
export interface TypeScriptSpec {
  readonly filePath?: string;
  readonly code?: string;
  readonly functions?: TypeScriptFunction[];
}

/**
 * Lean function specification
 * @traceability REQ-LEAN-TS-001
 */
export interface LeanFunctionSpec {
  readonly functionName: string;
  readonly typeSignature: string;
  readonly preconditionHypotheses: LeanHypothesis[];
  readonly postconditionGoal: LeanExpression;
  readonly leanCode: string;
}

// ============================================================================
// Proof Generation Types
// ============================================================================

/**
 * Proof strategy configuration
 * @traceability REQ-LEAN-PROOF-001
 */
export interface ProofStrategy {
  readonly name: string;
  readonly tactics: string[];
  readonly applicability?: (theorem: LeanTheorem) => boolean;
}

/**
 * Proof generation options
 */
export interface ProofOptions {
  readonly timeout?: number;
  readonly maxTactics?: number;
  readonly strategies?: ProofStrategy[];
  readonly useReProver?: boolean;
}

/**
 * Result of proof attempt
 * @traceability REQ-LEAN-PROOF-001
 */
export interface ProofResult {
  readonly success: boolean;
  readonly proof: LeanProof | null;
  readonly proofState: ProofState | null;
  readonly tacticsAttempted: string[];
  readonly duration: number;
  readonly error?: string;
}

/**
 * Result of tactic application
 */
export interface TacticResult {
  readonly success: boolean;
  readonly newState: ProofState | null;
  readonly error?: string;
}

// ============================================================================
// ReProver Types
// ============================================================================

/**
 * ReProver configuration
 * @traceability REQ-LEAN-REPROVER-001
 */
export interface ReProverConfig {
  readonly endpoint: string;
  readonly timeout: number;
  readonly maxDepth: number;
  readonly apiKey?: string;
}

/**
 * Search node in proof tree
 */
export interface SearchNode {
  readonly tactic: string;
  readonly state: ProofState;
  readonly score: number;
  readonly children: SearchNode[];
}

/**
 * ReProver search result
 * @traceability REQ-LEAN-REPROVER-002
 */
export interface ReProverSearchResult {
  readonly found: boolean;
  readonly proof: string | null;
  readonly searchPath: SearchNode[];
  readonly suggestions: string[];
}

/**
 * Proof feedback for failed attempts
 * @traceability REQ-LEAN-REPROVER-003
 */
export interface ProofFeedback {
  readonly stuckState: ProofState;
  readonly attemptedTactics: string[];
  readonly similarTheorems: string[];
  readonly guidance: string[];
}

// ============================================================================
// Verification Types
// ============================================================================

/**
 * Verification result for a single theorem
 */
export interface VerificationResult {
  readonly theoremId: string;
  readonly status: 'proved' | 'incomplete' | 'error';
  readonly proof?: LeanProof;
  readonly errors: string[];
  readonly warnings: string[];
  readonly duration: number;
  readonly feedback?: ProofFeedback;
}

/**
 * Report statistics
 */
export interface ReportStatistics {
  readonly totalTheorems: number;
  readonly provedCount: number;
  readonly failedCount: number;
  readonly incompleteCount: number;
  readonly averageProofTime: number;
  readonly totalTime: number;
}

/**
 * Verification report format
 */
export type ReportFormat = 'json' | 'markdown' | 'html' | 'csv';

/**
 * Verification report
 * @traceability REQ-LEAN-FEEDBACK-001
 */
export interface VerificationReport {
  readonly id: string;
  readonly timestamp: string;
  readonly results: VerificationResult[];
  readonly statistics: ReportStatistics;
  readonly executionDetails: {
    totalDuration: number;
    leanVersion: string;
    systemInfo: Record<string, string>;
  };
}

/**
 * Counterexample for failed verification
 * @traceability REQ-LEAN-FEEDBACK-003
 */
export interface Counterexample {
  readonly values: Record<string, unknown>;
  readonly violatedCondition: string;
  readonly typescriptReproduction: string;
}

/**
 * Diagnostic information
 */
export interface Diagnostic {
  readonly severity: 'error' | 'warning' | 'info';
  readonly message: string;
  readonly line?: number;
  readonly column?: number;
  readonly suggestion?: string;
}

// ============================================================================
// Traceability Types
// ============================================================================

/**
 * Traceability artifact types
 */
export type ArtifactType = 'requirement' | 'theorem' | 'proof' | 'code' | 'test';

/**
 * Traceability artifact
 */
export interface TraceabilityArtifact {
  readonly id: string;
  readonly type: ArtifactType;
  readonly content?: string;
  readonly name?: string;
  readonly version?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Traceability link type
 */
export type LinkType =
  | 'derives'
  | 'satisfies'
  | 'verifies'
  | 'tests'
  | 'requirement_to_theorem'
  | 'theorem_to_proof'
  | 'theorem_to_code'
  | 'requirement_to_code'
  | 'proof_to_verification';

/**
 * Link between artifacts
 * @traceability REQ-LEAN-INTEG-002
 */
export interface TraceabilityLink {
  readonly id: string;
  readonly source: string;
  readonly target: string;
  readonly type: LinkType;
  readonly confidence: number;
  readonly createdAt?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Traceability matrix
 * @traceability REQ-LEAN-INTEG-002
 */
export interface TraceabilityMatrix {
  readonly links: TraceabilityLink[];
  readonly coverage: number;
  readonly lastUpdated: Date;
}

// ============================================================================
// Hybrid Verification Types
// ============================================================================

/**
 * Verification target classification
 * @traceability REQ-LEAN-INTEG-001
 */
export type VerificationTarget = 'z3' | 'lean' | 'both';

/**
 * Classification result
 */
export interface ClassificationResult {
  readonly target: VerificationTarget;
  readonly reason: string;
  readonly confidence: number;
}

/**
 * Property to verify
 */
export interface Property {
  readonly id: string;
  readonly expression: string;
  readonly type: 'precondition' | 'postcondition' | 'invariant' | 'theorem';
}

/**
 * Combined verification result
 */
export interface HybridVerificationResult {
  readonly functionId: string;
  readonly runtimeResult?: {
    passed: boolean;
    testCount: number;
    failedTests: string[];
    coverage: number;
    duration: number;
  };
  readonly formalResult?: {
    proved: boolean;
    proof?: string;
    errors: string[];
    duration: number;
  };
  readonly combinedStatus: 'verified' | 'failed' | 'partial' | 'pending' | 'unknown';
  readonly coverage: {
    runtimeCoverage: number;
    formalCoverage: number;
    combinedCoverage: number;
    uncoveredPaths?: string[];
  };
}

// ============================================================================
// Configuration Types
// ============================================================================

/**
 * Lean package configuration
 */
export interface LeanConfig {
  /** Lean 4 executable path (auto-detected if not specified) */
  leanPath?: string;

  /** Project path */
  projectPath?: string;

  /** Minimum required Lean version */
  minVersion?: string;

  /** Default proof timeout in milliseconds */
  timeout?: number;

  /** Enable Lake */
  lakeEnabled?: boolean;

  /** Include Mathlib dependency */
  mathlibEnabled?: boolean;

  /** ReProver configuration */
  reprover?: ReProverConfig;

  /** Output directory for generated Lean files */
  outputDir?: string;

  /** Verbose logging */
  verbose?: boolean;

  /** Verification strategy */
  strategy?: 'lean-only' | 'hybrid' | 'z3-fallback';
}

/**
 * Default configuration values
 */
export const DEFAULT_LEAN_CONFIG: LeanConfig = {
  minVersion: '4.0.0',
  timeout: 30000,
  outputDir: '.musubix/lean',
  mathlibEnabled: false,
  lakeEnabled: true,
  strategy: 'hybrid',
};

// ============================================================================
// Execution Types
// ============================================================================

/**
 * Lean runner options
 * @traceability REQ-LEAN-CORE-004
 */
export interface LeanRunnerOptions {
  readonly timeout: number;
  readonly cwd?: string;
  readonly env?: Record<string, string>;
}
