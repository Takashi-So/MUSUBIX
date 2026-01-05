/**
 * @fileoverview Wake-Sleep type definitions
 * @traceability REQ-WAKE-001
 */

/**
 * Wake phase task for learning
 */
export interface WakeTask {
  id: string;
  type: 'code' | 'requirements' | 'design';
  content: string;
  context?: {
    filePath?: string;
    language?: string;
    project?: string;
  };
  metadata?: Record<string, unknown>;
  timestamp?: string;
}

/**
 * Wake phase result
 */
export interface WakeResult {
  taskId: string;
  success: boolean;
  extractedPatterns: string[];
  confidence: number;
  processingTime: number;
  metadata?: Record<string, unknown>;
  error?: string;
}

/**
 * Sleep phase consolidation input
 */
export interface ConsolidationInput {
  patterns: PatternCandidate[];
  existingLibrary: string[];
}

/**
 * Pattern candidate for consolidation
 */
export interface PatternCandidate {
  id?: string;
  name: string;
  code?: string;
  structure: unknown;
  occurrences: number;
  confidence: number;
  source: 'code' | 'requirements' | 'design';
  frequency?: number;
  contexts?: string[];
}

/**
 * Sleep phase result
 */
export interface SleepResult {
  consolidatedPatterns: string[];
  abstractedPatterns: AbstractedPattern[];
  prunedPatterns: string[];
  mdlScore: number;
}

/**
 * Abstracted pattern after sleep phase
 */
export interface AbstractedPattern {
  id: string;
  originalPatterns: string[];
  abstractedCode: string;
  compressionRatio: number;
}

/**
 * Wake-sleep cycle configuration
 */
export interface CycleConfig {
  /** Number of wake tasks before sleep */
  wakeTaskThreshold: number;
  /** Maximum cycle duration in ms */
  maxCycleDuration: number;
  /** Minimum pattern frequency for consolidation */
  minPatternFrequency: number;
  /** MDL threshold for abstraction */
  mdlThreshold: number;
}

/**
 * Cycle status
 */
export interface CycleStatus {
  currentPhase: 'wake' | 'sleep' | 'idle';
  taskCount: number;
  patternCount: number;
  cycleNumber: number;
  lastCycleTime: string | null;
}

/**
 * Resource limits configuration
 */
export interface ResourceLimits {
  /** Maximum memory usage in MB */
  maxMemoryMB: number;
  /** Maximum CPU time per operation in ms */
  maxCpuTimeMs: number;
  /** Maximum patterns in library */
  maxPatterns: number;
  /** Maximum concurrent operations */
  maxConcurrency: number;
}

/**
 * Resource usage metrics
 */
export interface ResourceMetrics {
  memoryUsedMB: number;
  cpuTimeMs: number;
  patternCount: number;
  activeOperations: number;
}

/**
 * Quality metrics for learning
 */
export interface QualityMetrics {
  accuracy: number;
  precision: number;
  recall: number;
  f1Score: number;
  mdlScore: number;
}
