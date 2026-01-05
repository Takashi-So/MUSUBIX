/**
 * @fileoverview Wake-Sleep Learning Types for YATA Local
 * @module @nahisaho/yata-local/wake-sleep
 * @version 0.1.0
 * @license MIT
 * 
 * Trace: REQ-WSL-001, REQ-WSL-002, REQ-WSL-003
 */

/**
 * Pattern candidate extracted during wake phase
 */
export interface LocalPatternCandidate {
  /** Temporary ID for tracking */
  tempId: string;
  /** Pattern type */
  type: LocalPatternType;
  /** Pattern name/identifier */
  name: string;
  /** Original source code or content */
  content: string;
  /** Source file path */
  sourcePath: string;
  /** Line range in source */
  lineRange: {
    start: number;
    end: number;
  };
  /** Language of the source */
  language: 'typescript' | 'javascript' | 'python' | 'other';
  /** AST signature for matching */
  signature: string;
  /** Initial confidence (0.0 - 1.0) */
  confidence: number;
  /** Extraction timestamp */
  extractedAt: Date;
  /** Additional metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Pattern types for classification
 */
export type LocalPatternType =
  | 'function_signature'
  | 'class_structure'
  | 'interface_definition'
  | 'type_definition'
  | 'import_pattern'
  | 'export_pattern'
  | 'error_handling'
  | 'async_pattern'
  | 'factory_pattern'
  | 'repository_pattern'
  | 'service_pattern'
  | 'value_object'
  | 'entity'
  | 'aggregate'
  | 'event_handler'
  | 'middleware'
  | 'decorator'
  | 'hook'
  | 'test_pattern'
  | 'other';

/**
 * Cluster of similar patterns
 */
export interface LocalPatternCluster {
  /** Cluster ID */
  clusterId: string;
  /** Patterns in this cluster */
  patterns: LocalPatternCandidate[];
  /** Representative pattern */
  representative: LocalPatternCandidate;
  /** Average similarity within cluster */
  avgSimilarity: number;
  /** Cluster centroid (abstract representation) */
  centroid: string;
  /** Total occurrences across patterns */
  totalOccurrences: number;
}

/**
 * Consolidated pattern ready for storage
 */
export interface LocalConsolidatedPattern {
  /** Pattern ID */
  id: string;
  /** Pattern name */
  name: string;
  /** Pattern type */
  type: LocalPatternType;
  /** Abstract template */
  template: string;
  /** Compressed representation */
  compressed: string;
  /** Confidence score */
  confidence: number;
  /** Number of source examples */
  sourceCount: number;
  /** Usage count */
  usageCount: number;
  /** Created timestamp */
  createdAt: Date;
  /** Last used timestamp */
  lastUsedAt: Date | null;
  /** Source files this pattern was extracted from */
  sources: string[];
}

/**
 * Wake phase observation options
 */
export interface WakeObserveOptions {
  /** File extensions to include */
  extensions?: string[];
  /** Directories to exclude */
  excludeDirs?: string[];
  /** Minimum confidence threshold */
  minConfidence?: number;
  /** Maximum number of candidates */
  maxCandidates?: number;
  /** Include private members */
  includePrivate?: boolean;
}

/**
 * Wake phase observation result
 */
export interface WakeObserveResult {
  /** Extracted pattern candidates */
  candidates: LocalPatternCandidate[];
  /** Statistics */
  stats: {
    filesScanned: number;
    candidatesFound: number;
    skippedFiles: number;
    processingTimeMs: number;
  };
  /** Any errors encountered */
  errors: Array<{
    file: string;
    error: string;
  }>;
}

/**
 * Sleep phase clustering options
 */
export interface SleepClusterOptions {
  /** Similarity threshold (0.0 - 1.0) */
  similarityThreshold?: number;
  /** Minimum cluster size */
  minClusterSize?: number;
  /** Maximum clusters to form */
  maxClusters?: number;
}

/**
 * Sleep phase clustering result
 */
export interface SleepClusterResult {
  /** Formed clusters */
  clusters: LocalPatternCluster[];
  /** Patterns that didn't cluster */
  unclustered: LocalPatternCandidate[];
  /** Statistics */
  stats: {
    totalPatterns: number;
    clusteredPatterns: number;
    unclusteredPatterns: number;
    clustersFormed: number;
    avgClusterSize: number;
    processingTimeMs: number;
  };
}

/**
 * Pattern compression options
 */
export interface CompressOptions {
  /** Compression level (1-10) */
  level?: number;
  /** Preserve variable names */
  preserveNames?: boolean;
  /** Include type annotations */
  includeTypes?: boolean;
}

/**
 * Learning cycle result
 */
export interface LocalLearningCycleResult {
  /** Cycle ID */
  cycleId: string;
  /** Phase that completed */
  phase: 'wake' | 'sleep' | 'complete';
  /** Wake phase results (if applicable) */
  wakeResult?: WakeObserveResult;
  /** Sleep phase results (if applicable) */
  sleepResult?: SleepClusterResult;
  /** New patterns added to store */
  newPatterns: number;
  /** Patterns updated */
  updatedPatterns: number;
  /** Patterns decayed */
  decayedPatterns: number;
  /** Cycle start time */
  startedAt: Date;
  /** Cycle end time */
  completedAt: Date;
  /** Cycle duration in ms */
  durationMs: number;
}

/**
 * Learning cycle status
 */
export type LearningCycleStatus = 'pending' | 'running' | 'completed' | 'failed';

/**
 * Learning cycle metadata for storage
 */
export interface LocalLearningCycleMetadata {
  /** Cycle ID */
  id: string;
  /** Cycle status */
  status: LearningCycleStatus;
  /** Wake results JSON */
  wakeResultJson: string | null;
  /** Sleep results JSON */
  sleepResultJson: string | null;
  /** New patterns count */
  newPatterns: number;
  /** Updated patterns count */
  updatedPatterns: number;
  /** Decayed patterns count */
  decayedPatterns: number;
  /** Started timestamp */
  startedAt: string;
  /** Completed timestamp */
  completedAt: string | null;
  /** Duration in milliseconds */
  durationMs: number | null;
  /** Error message if failed */
  errorMessage: string | null;
}

/**
 * Similarity calculation method
 */
export type SimilarityMethod = 'jaccard' | 'cosine' | 'levenshtein' | 'ast';

/**
 * Wake-sleep cycle configuration
 */
export interface WakeSleepConfig {
  /** Auto-run interval in milliseconds (0 = disabled) */
  autoRunInterval: number;
  /** Wake phase options */
  wakeOptions: WakeObserveOptions;
  /** Sleep phase options */
  sleepOptions: SleepClusterOptions;
  /** Compression options */
  compressOptions: CompressOptions;
  /** Similarity method */
  similarityMethod: SimilarityMethod;
  /** Confidence decay rate per day (0.0 - 1.0) */
  decayRate: number;
  /** Minimum confidence before removal */
  minConfidenceThreshold: number;
}

/**
 * Default configuration
 */
export const DEFAULT_WAKE_SLEEP_CONFIG: WakeSleepConfig = {
  autoRunInterval: 0,
  wakeOptions: {
    extensions: ['.ts', '.tsx', '.js', '.jsx'],
    excludeDirs: ['node_modules', 'dist', 'build', '.git'],
    minConfidence: 0.3,
    maxCandidates: 1000,
    includePrivate: false,
  },
  sleepOptions: {
    similarityThreshold: 0.8,
    minClusterSize: 2,
    maxClusters: 100,
  },
  compressOptions: {
    level: 5,
    preserveNames: false,
    includeTypes: true,
  },
  similarityMethod: 'jaccard',
  decayRate: 0.01,
  minConfidenceThreshold: 0.1,
};
