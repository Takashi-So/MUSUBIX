/**
 * @fileoverview Ontology MCP type definitions
 * @traceability REQ-ONTO-001
 */

/**
 * RDF Triple
 */
export interface Triple {
  subject: string;
  predicate: string;
  object: string;
  graph?: string;
}

/**
 * Ontology definition
 */
export interface Ontology {
  id: string;
  namespace: string;
  prefixes: Record<string, string>;
  triples: Triple[];
  createdAt: string;
  updatedAt: string;
}

/**
 * Ontology store configuration
 */
export interface OntologyStoreConfig {
  storagePath: string;
  enableInference: boolean;
  maxTriples: number;
}

/**
 * SPARQL query result
 */
export interface QueryResult {
  type: 'select' | 'ask' | 'construct';
  bindings?: Record<string, string>[];
  boolean?: boolean;
  triples?: Triple[];
}

/**
 * Inference result with proof tree
 */
export interface InferenceResult {
  inferred: Triple[];
  proofTree: ProofNode[];
}

/**
 * Proof tree node
 */
export interface ProofNode {
  conclusion: Triple;
  rule: string;
  premises: ProofNode[];
}

/**
 * Consistency check result
 */
export interface ConsistencyResult {
  consistent: boolean;
  violations: ConsistencyViolation[];
}

/**
 * Consistency violation
 */
export interface ConsistencyViolation {
  type: string;
  message: string;
  triples: Triple[];
}

/**
 * Query error with position
 */
export interface QueryError {
  message: string;
  line: number;
  column: number;
  suggestion?: string;
}
