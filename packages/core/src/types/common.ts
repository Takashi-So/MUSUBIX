/**
 * Common Type Definitions for MUSUBIX
 * 
 * @packageDocumentation
 * @module types
 * 
 * @see REQ-INT-001 - Neuro-Symbolic Integration
 * @see DES-MUSUBIX-001 Section 4 - Integration Layer Design
 */

// ============================================================================
// Base Types
// ============================================================================

/**
 * Unique identifier type
 */
export type ID = string;

/**
 * ISO 8601 timestamp
 */
export type Timestamp = string;

/**
 * Semantic version string (e.g., "1.0.0")
 */
export type SemanticVersion = string;

/**
 * Priority levels
 */
export type Priority = 'P0' | 'P1' | 'P2';

/**
 * Confidence score (0.0 - 1.0)
 */
export type Confidence = number;

// ============================================================================
// Result Types
// ============================================================================

/**
 * Generic result wrapper for operations
 */
export interface Result<T, E = Error> {
  success: boolean;
  data?: T;
  error?: E;
  metadata?: ResultMetadata;
}

/**
 * Metadata for operation results
 */
export interface ResultMetadata {
  timestamp: Timestamp;
  duration: number;
  traceId?: ID;
}

// ============================================================================
// Neuro-Symbolic Integration Types
// ============================================================================

/**
 * Neural inference result from LLM
 * @see REQ-INT-001
 */
export interface NeuralInferenceResult {
  /** Generated output */
  output: string;
  /** Confidence score (0.0 - 1.0) */
  confidence: Confidence;
  /** Model identifier */
  model: string;
  /** Token count */
  tokens: number;
  /** Raw response metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Symbolic reasoning result from YATA
 * @see REQ-INT-001
 */
export interface SymbolicReasoningResult {
  /** Generated output */
  output: string;
  /** Whether output is logically valid */
  valid: boolean;
  /** Detected violations */
  violations: Violation[];
  /** Detected patterns */
  patterns: DetectedPattern[];
  /** Reasoning chain */
  chain?: ReasoningStep[];
}

/**
 * Merged integration result
 * @see REQ-INT-001
 */
export interface IntegrationResult {
  /** Neural inference result */
  neuralResult: NeuralInferenceResult;
  /** Symbolic reasoning result */
  symbolicResult: SymbolicReasoningResult;
  /** Final merged result */
  finalResult: MergedResult;
  /** Overall confidence */
  confidence: Confidence;
  /** Complete reasoning chain */
  reasoning: ReasoningChain;
}

/**
 * Merged result after integration
 */
export interface MergedResult {
  /** Final output */
  output: string;
  /** Source of decision */
  source: 'neural' | 'symbolic' | 'merged';
  /** How results were combined */
  mergeStrategy: MergeStrategy;
}

/**
 * Merge strategy used
 */
export type MergeStrategy = 
  | 'neural-only'
  | 'symbolic-only'
  | 'neural-validated'
  | 'weighted-merge'
  | 'contradiction-resolved';

// ============================================================================
// Violation and Pattern Types
// ============================================================================

/**
 * Violation detected during validation
 * @see REQ-INT-003
 */
export interface Violation {
  /** Violation identifier */
  id: ID;
  /** Violation type */
  type: ViolationType;
  /** Severity level */
  severity: 'error' | 'warning' | 'info';
  /** Human-readable message */
  message: string;
  /** Location in artifact */
  location?: Location;
  /** Suggested fix */
  suggestion?: string;
}

/**
 * Violation types
 */
export type ViolationType =
  | 'syntax-error'
  | 'semantic-error'
  | 'pattern-violation'
  | 'constraint-violation'
  | 'contradiction'
  | 'incomplete';

/**
 * Detected design pattern
 * @see REQ-DES-001
 */
export interface DetectedPattern {
  /** Pattern name */
  name: string;
  /** Pattern category */
  category: PatternCategory;
  /** Detection confidence */
  confidence: Confidence;
  /** Pattern applicability score */
  applicability: number;
  /** Rationale for detection */
  rationale: string;
}

/**
 * Pattern categories
 */
export type PatternCategory =
  | 'creational'
  | 'structural'
  | 'behavioral'
  | 'architectural'
  | 'concurrency'
  | 'integration';

// ============================================================================
// Reasoning Types
// ============================================================================

/**
 * Complete reasoning chain
 * @see REQ-EXP-001
 */
export interface ReasoningChain {
  /** Chain identifier */
  id: ID;
  /** Reasoning steps */
  steps: ReasoningStep[];
  /** Final conclusion */
  conclusion: string;
  /** Overall confidence */
  confidence: Confidence;
  /** Timestamp */
  timestamp: Timestamp;
}

/**
 * Single reasoning step
 */
export interface ReasoningStep {
  /** Step number */
  step: number;
  /** Step type */
  type: ReasoningStepType;
  /** Input to this step */
  input: string;
  /** Output from this step */
  output: string;
  /** Source of reasoning */
  source: 'neural' | 'symbolic';
  /** Confidence for this step */
  confidence: Confidence;
  /** Evidence supporting this step */
  evidence?: string[];
}

/**
 * Reasoning step types
 */
export type ReasoningStepType =
  | 'analysis'
  | 'inference'
  | 'validation'
  | 'synthesis'
  | 'resolution';

// ============================================================================
// Location Types
// ============================================================================

/**
 * Location in source artifact
 */
export interface Location {
  /** File path */
  file?: string;
  /** Line number (1-indexed) */
  line?: number;
  /** Column number (1-indexed) */
  column?: number;
  /** End line */
  endLine?: number;
  /** End column */
  endColumn?: number;
}

// ============================================================================
// Traceability Types
// ============================================================================

/**
 * Traceability link between artifacts
 * @see REQ-TRA-001
 */
export interface TraceabilityLink {
  /** Link identifier */
  id: ID;
  /** Source artifact ID */
  sourceId: ID;
  /** Source artifact type */
  sourceType: ArtifactType;
  /** Target artifact ID */
  targetId: ID;
  /** Target artifact type */
  targetType: ArtifactType;
  /** Link type */
  linkType: LinkType;
  /** When link was created */
  createdAt: Timestamp;
}

/**
 * Artifact types for traceability
 */
export type ArtifactType =
  | 'requirement'
  | 'design'
  | 'code'
  | 'test'
  | 'documentation';

/**
 * Link types
 */
export type LinkType =
  | 'implements'
  | 'satisfies'
  | 'tests'
  | 'derives-from'
  | 'depends-on';

// ============================================================================
// Configuration Types
// ============================================================================

/**
 * MUSUBIX configuration
 */
export interface MuSubixConfig {
  /** Configuration version */
  version: SemanticVersion;
  /** Project name */
  project: string;
  /** Steering directory path */
  steeringDir: string;
  /** Storage directory path */
  storageDir: string;
  /** LLM configuration */
  llm?: LLMConfig;
  /** YATA configuration */
  yata?: YataConfig;
  /** Integration configuration */
  integration?: IntegrationConfig;
}

/**
 * LLM configuration
 */
export interface LLMConfig {
  /** Provider name */
  provider: 'anthropic' | 'openai' | 'google' | 'local';
  /** Model name */
  model: string;
  /** API endpoint */
  endpoint?: string;
  /** Maximum tokens */
  maxTokens?: number;
  /** Temperature */
  temperature?: number;
}

/**
 * YATA configuration
 */
export interface YataConfig {
  /** MCP transport */
  transport: 'stdio' | 'sse';
  /** Server command or URL */
  server: string;
  /** Connection timeout (ms) */
  timeout?: number;
}

/**
 * Integration configuration
 */
export interface IntegrationConfig {
  /** Confidence threshold for neural output */
  neuralThreshold: Confidence;
  /** Confidence threshold for symbolic output */
  symbolicThreshold: Confidence;
  /** Default merge strategy */
  defaultStrategy: MergeStrategy;
  /** Enable graceful degradation */
  gracefulDegradation: boolean;
}

// ============================================================================
// Export Index
// ============================================================================

export * from './ears.js';
export * from './errors.js';
