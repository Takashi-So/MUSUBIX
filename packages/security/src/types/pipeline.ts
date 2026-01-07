/**
 * @fileoverview Pipeline and orchestration type definitions
 * @module @nahisaho/musubix-security/types/pipeline
 * @trace DES-SEC2-ORCH-002, REQ-SEC2-PERF-001
 */

import type { ScanResult } from './vulnerability.js';
import type { TaintResult } from './taint.js';
import type { SecretScanResult } from './secret.js';
import type { AuditResult } from './dependency.js';

/**
 * Pipeline stage identifier
 */
export type StageId = string;

/**
 * Pipeline stage status
 */
export type StageStatus = 
  | 'pending'
  | 'running'
  | 'completed'
  | 'failed'
  | 'cancelled'
  | 'skipped';

/**
 * Analyzer type
 */
export type AnalyzerType = 
  | 'vulnerability-scanner'
  | 'taint-tracker'
  | 'secret-detector'
  | 'dependency-auditor'
  | 'image-scanner'
  | 'iac-checker'
  | 'prompt-injection-detector'
  | 'compliance-validator'
  | 'zero-day-detector'
  | 'interprocedural-analyzer';

/**
 * Pipeline stage configuration
 * @trace DES-SEC2-ORCH-002
 */
export interface PipelineStage {
  /** Stage identifier */
  id: StageId;
  
  /** Stage name for display */
  name: string;
  
  /** Analyzer type to run */
  analyzer: AnalyzerType;
  
  /** Analyzer-specific options */
  options: Record<string, unknown>;
  
  /** Stage dependencies (must complete before this stage) */
  dependsOn?: StageId[];
  
  /** Timeout in milliseconds */
  timeout?: number;
  
  /** Whether to continue pipeline on failure */
  continueOnFailure?: boolean;
}

/**
 * Pipeline configuration
 */
export interface PipelineConfig {
  /** Pipeline stages */
  stages: PipelineStage[];
  
  /** Maximum parallel stages */
  maxParallel?: number;
  
  /** Global timeout for entire pipeline */
  timeout?: number;
  
  /** Target path(s) to scan */
  targets: string[];
  
  /** Enable caching */
  cache?: boolean;
}

/**
 * Pipeline progress callback
 */
export type ProgressCallback = (progress: PipelineProgress) => void;

/**
 * Pipeline progress information
 */
export interface PipelineProgress {
  /** Pipeline ID */
  pipelineId: string;
  
  /** Overall progress percentage (0-100) */
  percentage: number;
  
  /** Currently running stages */
  runningStages: StageId[];
  
  /** Completed stages */
  completedStages: StageId[];
  
  /** Failed stages */
  failedStages: StageId[];
  
  /** Estimated time remaining (milliseconds) */
  estimatedRemaining?: number;
}

/**
 * Pipeline stage result
 */
export interface StageResult {
  /** Stage ID */
  stageId: StageId;
  
  /** Stage status */
  status: StageStatus;
  
  /** Stage duration in milliseconds */
  duration: number;
  
  /** Result data (varies by analyzer type) */
  data?: ScanResult | TaintResult | SecretScanResult | AuditResult | unknown;
  
  /** Error if failed */
  error?: Error;
  
  /** Start time */
  startedAt: Date;
  
  /** End time */
  endedAt?: Date;
}

/**
 * Pipeline result
 * @trace DES-SEC2-ORCH-002
 */
export interface PipelineResult {
  /** Pipeline ID */
  pipelineId: string;
  
  /** Pipeline status */
  status: 'completed' | 'failed' | 'cancelled' | 'timeout';
  
  /** Stage results */
  stageResults: StageResult[];
  
  /** Total duration in milliseconds */
  duration: number;
  
  /** Start time */
  startedAt: Date;
  
  /** End time */
  endedAt: Date;
  
  /** Summary statistics */
  summary: {
    totalStages: number;
    completedStages: number;
    failedStages: number;
    skippedStages: number;
  };
}

/**
 * Pipeline manager interface
 * @trace DES-SEC2-ORCH-002
 */
export interface IPipelineManager {
  /** Create and configure a pipeline */
  createPipeline(config: PipelineConfig): Pipeline;
  
  /** Execute pipeline stages in parallel where possible */
  executeParallel(pipelines: Pipeline[]): Promise<PipelineResult[]>;
  
  /** Execute pipeline stages sequentially */
  executeSequential(pipeline: Pipeline): Promise<PipelineResult>;
  
  /** Cancel running pipeline */
  cancel(pipelineId: string): void;
  
  /** Get pipeline status */
  getStatus(pipelineId: string): PipelineProgress | undefined;
}

/**
 * Pipeline instance
 */
export interface Pipeline {
  /** Pipeline ID */
  id: string;
  
  /** Pipeline configuration */
  config: PipelineConfig;
  
  /** Progress callback */
  onProgress?: ProgressCallback;
  
  /** Execute the pipeline */
  execute(): Promise<PipelineResult>;
  
  /** Cancel the pipeline */
  cancel(): void;
}

/**
 * Analyzer factory function
 * Returns an analyzer instance with at least one of the analysis methods
 */
export type AnalyzerFactory = () => AnalyzerInstance;

/**
 * Analyzer instance with optional analysis methods
 */
export interface AnalyzerInstance {
  /** Scan method (vulnerability-scanner, image-scanner) */
  scan?: (path: string, options?: unknown) => Promise<unknown>;
  
  /** Analyze method (taint-tracker, iac-checker, interprocedural-analyzer) */
  analyze?: (path: string, options?: unknown) => Promise<unknown>;
  
  /** Detect method (secret-detector, prompt-injection-detector, zero-day-detector) */
  detect?: (path: string, options?: unknown) => Promise<unknown>;
  
  /** Audit method (dependency-auditor) */
  audit?: (path: string, options?: unknown) => Promise<unknown>;
  
  /** Validate method (compliance-validator) */
  validate?: (path: string, options?: unknown) => Promise<unknown>;
}
