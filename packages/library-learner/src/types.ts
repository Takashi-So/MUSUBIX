/**
 * Type definitions for musubix-library-learner
 *
 * REQ-LL-001: 階層的抽象化
 * REQ-LL-002: ライブラリ成長
 * REQ-LL-003: 型指向探索
 * REQ-LL-004: E-graph最適化
 */

// =============================================================================
// Core Types
// =============================================================================

/** Unique identifier for patterns */
export type PatternId = string;

/** Unique identifier for E-graph classes */
export type EClassId = number;

/** Code corpus for pattern mining */
export interface CodeCorpus {
  /** Unique identifier for the corpus */
  id: string;
  /** Source files in the corpus */
  files: SourceFile[];
  /** Metadata about the corpus */
  metadata?: Record<string, unknown>;
}

/** Source file in a corpus */
export interface SourceFile {
  /** File path */
  path: string;
  /** File content */
  content: string;
  /** Programming language */
  language: 'typescript' | 'javascript' | 'python' | string;
}

// =============================================================================
// Pattern Types
// =============================================================================

/** Candidate pattern detected during mining */
export interface PatternCandidate {
  /** Unique identifier */
  id: PatternId;
  /** Pattern AST or representation */
  ast: ASTNode;
  /** Occurrences in the corpus */
  occurrences: PatternOccurrence[];
  /** Computed score */
  score: number;
}

/** Occurrence of a pattern in source code */
export interface PatternOccurrence {
  /** Source file path */
  file: string;
  /** Start line (1-indexed) */
  startLine: number;
  /** End line (1-indexed) */
  endLine: number;
  /** Matched bindings */
  bindings: Map<string, ASTNode>;
}

/** Concrete pattern (Level 1 abstraction) */
export interface ConcretePattern {
  /** Unique identifier */
  id: PatternId;
  /** Pattern AST */
  ast: ASTNode;
  /** Number of occurrences */
  occurrenceCount: number;
  /** Source locations */
  locations: PatternOccurrence[];
}

/** Parameterized template (Level 2 abstraction) */
export interface ParameterizedTemplate {
  /** Unique identifier */
  id: PatternId;
  /** Template with holes */
  template: TemplateNode;
  /** Parameter names and types */
  parameters: TemplateParameter[];
  /** Concrete patterns this abstracts */
  concretePatterns: PatternId[];
}

/** Parameter in a template */
export interface TemplateParameter {
  /** Parameter name */
  name: string;
  /** Parameter type */
  type: TypeSignature;
  /** Default value (if any) */
  defaultValue?: unknown;
}

/** Abstract concept (Level 3 abstraction) */
export interface AbstractConcept {
  /** Unique identifier */
  id: PatternId;
  /** Concept name */
  name: string;
  /** Description */
  description: string;
  /** Templates this concept encompasses */
  templates: PatternId[];
  /** Semantic category */
  category: string;
}

/** Learned pattern stored in library */
export interface LearnedPattern {
  /** Unique identifier */
  id: PatternId;
  /** Pattern name */
  name: string;
  /** Abstraction level */
  level: 1 | 2 | 3;
  /** Pattern content (varies by level) */
  content: ConcretePattern | ParameterizedTemplate | AbstractConcept;
  /** Usage count */
  usageCount: number;
  /** Confidence score (0-1) */
  confidence: number;
  /** Creation timestamp */
  createdAt: Date;
  /** Last used timestamp */
  lastUsedAt: Date;
  /** Tags for categorization */
  tags: string[];
}

// =============================================================================
// AST Types
// =============================================================================

/** Generic AST node */
export interface ASTNode {
  /** Node type */
  type: string;
  /** Child nodes */
  children?: ASTNode[];
  /** Node value (for literals) */
  value?: unknown;
  /** Additional properties */
  [key: string]: unknown;
}

/** Template node with holes */
export interface TemplateNode extends ASTNode {
  /** Whether this is a hole */
  isHole?: boolean;
  /** Hole name (if isHole) */
  holeName?: string;
  /** Hole type constraint (if isHole) */
  holeType?: TypeSignature;
}

// =============================================================================
// Type System
// =============================================================================

/** Type signature for type-directed search */
export interface TypeSignature {
  /** Type kind */
  kind: 'primitive' | 'function' | 'generic' | 'union' | 'intersection' | 'object' | 'array';
  /** Type name (for primitives) */
  name?: string;
  /** Parameter types (for functions) */
  paramTypes?: TypeSignature[];
  /** Return type (for functions) */
  returnType?: TypeSignature;
  /** Type parameters (for generics) */
  typeParams?: string[];
  /** Union/intersection members */
  members?: TypeSignature[];
  /** Object properties */
  properties?: Record<string, TypeSignature>;
  /** Array element type */
  elementType?: TypeSignature;
}

/** Type context for analysis */
export interface TypeContext {
  /** Available variables and their types */
  variables: Map<string, TypeSignature>;
  /** Available functions and their types */
  functions: Map<string, TypeSignature>;
  /** Type aliases */
  aliases: Map<string, TypeSignature>;
}

// =============================================================================
// E-Graph Types
// =============================================================================

/** E-graph node */
export interface ENode {
  /** Operator name */
  op: string;
  /** Child E-class IDs */
  children: EClassId[];
}

/** E-class (equivalence class) */
export interface EClass {
  /** Class ID */
  id: EClassId;
  /** Nodes in this class */
  nodes: ENode[];
  /** Parent classes (for union-find) */
  parents: Set<EClassId>;
}

/** Pattern for e-graph matching */
export interface EPattern {
  /** Pattern operator (or variable name if isVar) */
  op: string;
  /** Whether this is a pattern variable */
  isVar?: boolean;
  /** Child patterns */
  children?: EPattern[];
}

/** Match result from e-graph pattern matching */
export interface EMatch {
  /** E-class ID that matched */
  eclass: EClassId;
  /** Variable bindings */
  bindings: Map<string, EClassId>;
}

/** Equality rule for e-graph rewriting */
export interface EqualityRule {
  /** Rule name */
  name: string;
  /** Left-hand side pattern */
  lhs: EPattern;
  /** Right-hand side pattern */
  rhs: EPattern;
  /** Optional condition */
  condition?: (match: EMatch) => boolean;
}

/** Cost function for extraction */
export type CostFunction = (node: ENode, childCosts: number[]) => number;

/** Optimal expression extracted from e-graph */
export interface OptimalExpression {
  /** Root E-class ID */
  root: EClassId;
  /** Extracted AST */
  ast: ASTNode;
  /** Total cost */
  cost: number;
}

// =============================================================================
// Query and Search Types
// =============================================================================

/** Query for searching patterns */
export interface PatternQuery {
  /** Text search */
  text?: string;
  /** Filter by abstraction level */
  level?: 1 | 2 | 3;
  /** Filter by tags */
  tags?: string[];
  /** Filter by minimum confidence */
  minConfidence?: number;
  /** Filter by minimum usage count */
  minUsageCount?: number;
  /** Maximum results */
  limit?: number;
}

/** Specification for synthesis */
export interface Specification {
  /** Input-output examples */
  examples?: Array<{ input: unknown; output: unknown }>;
  /** Type signature */
  type?: TypeSignature;
  /** Natural language description */
  description?: string;
  /** Constraints */
  constraints?: string[];
}

/** Options for synthesis */
export interface SynthesizeOptions {
  /** Maximum search depth */
  maxDepth?: number;
  /** Timeout in milliseconds */
  timeout?: number;
  /** Whether to use type-directed search */
  useTypeDirected?: boolean;
  /** Whether to use E-graph optimization */
  useEGraph?: boolean;
}

/** Result of synthesis */
export interface SynthesisResult {
  /** Whether synthesis succeeded */
  success: boolean;
  /** Synthesized program (if success) */
  program?: ASTNode;
  /** Alternative candidates */
  candidates?: ASTNode[];
  /** Time taken in milliseconds */
  duration: number;
  /** Number of search nodes explored */
  searchNodes: number;
  /** Patterns used */
  patternsUsed: PatternId[];
}

// =============================================================================
// Learning Types
// =============================================================================

/** Result of learning from corpus */
export interface LearnResult {
  /** Number of patterns extracted */
  patternsExtracted: number;
  /** Number of patterns added to library */
  patternsAdded: number;
  /** Number of patterns consolidated */
  patternsConsolidated: number;
  /** Time taken in milliseconds */
  duration: number;
}

/** Statistics about the library */
export interface LibraryStats {
  /** Total number of patterns */
  totalPatterns: number;
  /** Patterns by level */
  patternsByLevel: Record<1 | 2 | 3, number>;
  /** Average confidence */
  averageConfidence: number;
  /** Average usage count */
  averageUsageCount: number;
  /** Most used patterns */
  mostUsed: PatternId[];
  /** Least used patterns */
  leastUsed: PatternId[];
}

/** Report from consolidation */
export interface ConsolidationReport {
  /** Number of clusters found */
  clustersFound: number;
  /** Number of patterns merged */
  patternsMerged: number;
  /** New patterns created */
  newPatterns: PatternId[];
  /** Time taken in milliseconds */
  duration: number;
}

/** Report from pruning */
export interface PruneReport {
  /** Number of patterns pruned */
  patternsPruned: number;
  /** IDs of pruned patterns */
  prunedIds: PatternId[];
  /** Time taken in milliseconds */
  duration: number;
}

/** Cluster of similar patterns */
export interface SimilarityCluster {
  /** Representative pattern ID */
  representative: PatternId;
  /** Member pattern IDs */
  members: PatternId[];
  /** Similarity score */
  similarity: number;
}

// =============================================================================
// Configuration Types
// =============================================================================

/** Configuration for LibraryLearner */
export interface LibraryLearnerConfig {
  /** Number of abstraction levels (default: 3) */
  abstractionLevels?: number;
  /** Minimum occurrences to extract pattern (default: 2) */
  minOccurrences?: number;
  /** Decay rate for unused patterns (default: 0.95) */
  decayRate?: number;
  /** Threshold for pruning (default: 0.1) */
  pruneThreshold?: number;
  /** Whether to use E-graph optimization (default: true) */
  useEGraph?: boolean;
  /** Storage path for library */
  storagePath?: string;
}

/** Configuration for PatternMiner */
export interface PatternMinerConfig {
  /** Minimum occurrences to consider as pattern */
  minOccurrences?: number;
  /** Maximum pattern depth */
  maxDepth?: number;
  /** Minimum pattern size (nodes) */
  minSize?: number;
  /** Maximum pattern size (nodes) */
  maxSize?: number;
}

/** Configuration for E-graph */
export interface EGraphConfig {
  /** Maximum iterations for saturation */
  maxIterations?: number;
  /** Timeout for saturation in milliseconds */
  timeout?: number;
  /** Whether to enable explanations */
  enableExplanations?: boolean;
}
