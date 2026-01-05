/**
 * @fileoverview Pattern MCP type definitions
 * @traceability REQ-PATTERN-001
 */

/**
 * AST node representation for pattern extraction
 */
export interface ASTNode {
  type: string;
  children: ASTNode[];
  value?: string;
  startPosition: Position;
  endPosition: Position;
}

export interface Position {
  row: number;
  column: number;
}

/**
 * Extracted pattern structure
 */
export interface Pattern {
  id: string;
  name: string;
  language: string;
  ast: ASTNode;
  holes: PatternHole[];
  frequency: number;
  createdAt: string;
  updatedAt: string;
}

/**
 * Hole in abstract pattern (placeholder for variable parts)
 */
export interface PatternHole {
  id: string;
  type: string;
  constraints?: string[];
}

/**
 * Pattern library configuration
 */
export interface PatternLibraryConfig {
  storagePath: string;
  maxPatterns: number;
  enablePrivacyFilter: boolean;
}

/**
 * Pattern extraction options
 */
export interface ExtractionOptions {
  language: string;
  minFrequency: number;
  maxDepth: number;
}

/**
 * Similarity calculation result
 */
export interface SimilarityResult {
  patternA: string;
  patternB: string;
  score: number;
  method: 'cosine' | 'jaccard' | 'structural';
}

/**
 * Similarity matrix for batch calculations
 */
export interface SimilarityMatrix {
  patternIds: string[];
  scores: number[][];
}

/**
 * Pattern cluster
 */
export interface PatternCluster {
  id: string;
  centroid: Pattern;
  members: string[];
  cohesion: number;
}

/**
 * Privacy filter result
 */
export interface PrivacyFilterResult {
  filtered: boolean;
  reason?: string;
  sanitizedPattern?: Pattern;
}
