/**
 * @fileoverview Pipeline Manager - orchestrates security analysis pipelines
 * @module @nahisaho/musubix-security/core/pipeline-manager
 * @trace DES-SEC2-ORCH-002, REQ-SEC2-PERF-001
 */

import { randomUUID } from 'node:crypto';
import type {
  Pipeline,
  PipelineConfig,
  PipelineResult,
  PipelineProgress,
  PipelineStage,
  StageResult,
  StageStatus,
  IPipelineManager,
  ProgressCallback,
  AnalyzerType,
  AnalyzerInstance,
  ScanOptions,
} from '../types/index.js';
import { VulnerabilityScanner } from '../analysis/index.js';
import { TaintAnalyzer } from '../analysis/index.js';
import { SecretDetector } from '../analysis/index.js';
import { DependencyAuditor } from '../analysis/index.js';

/**
 * Pipeline execution context
 */
interface PipelineContext {
  id: string;
  config: PipelineConfig;
  status: 'pending' | 'running' | 'completed' | 'failed' | 'cancelled';
  stageStatuses: Map<string, StageStatus>;
  stageResults: Map<string, StageResult>;
  startTime?: Date;
  endTime?: Date;
  cancelled: boolean;
  onProgress?: ProgressCallback;
}

/**
 * Analyzer factory for creating analyzer instances
 */
type AnalyzerFactory = () => AnalyzerInstance;

/**
 * Pipeline Manager implementation
 * @trace DES-SEC2-ORCH-002
 */
export class PipelineManager implements IPipelineManager {
  private runningPipelines: Map<string, PipelineContext> = new Map();
  private analyzerFactories: Map<AnalyzerType, AnalyzerFactory>;

  constructor() {
    // Initialize analyzer factories with explicit typing
    // Wrap existing analyzers to conform to AnalyzerInstance interface
    const factories: Array<[AnalyzerType, AnalyzerFactory]> = [
      ['vulnerability-scanner', (): AnalyzerInstance => {
        const scanner = new VulnerabilityScanner();
        return {
          scan: async (path: string, options?: unknown) => scanner.scanDirectory(path, options as ScanOptions | undefined),
        };
      }],
      ['taint-tracker', (): AnalyzerInstance => {
        const analyzer = new TaintAnalyzer();
        return {
          analyze: async (path: string, _options?: unknown) => analyzer.analyzeFile(path),
        };
      }],
      ['secret-detector', (): AnalyzerInstance => {
        const detector = new SecretDetector();
        return {
          detect: async (path: string, _options?: unknown) => detector.scan(path),
        };
      }],
      ['dependency-auditor', (): AnalyzerInstance => {
        const auditor = new DependencyAuditor();
        return {
          audit: async (path: string, _options?: unknown) => auditor.audit(path),
        };
      }],
      // Placeholders for new analyzers (to be implemented in Phase 2)
      ['image-scanner', (): AnalyzerInstance => ({ scan: async () => ({ vulnerabilities: [] }) })],
      ['iac-checker', (): AnalyzerInstance => ({ analyze: async () => ({ issues: [] }) })],
      ['prompt-injection-detector', (): AnalyzerInstance => ({ detect: async () => ({ findings: [] }) })],
      ['compliance-validator', (): AnalyzerInstance => ({ validate: async () => ({ compliant: true }) })],
      ['zero-day-detector', (): AnalyzerInstance => ({ detect: async () => ({ candidates: [] }) })],
      ['interprocedural-analyzer', (): AnalyzerInstance => ({ analyze: async () => ({ callGraph: { nodes: [], edges: [], roots: [], leaves: [] } }) })],
    ];
    this.analyzerFactories = new Map(factories);
  }

  /**
   * Register a custom analyzer factory
   */
  registerAnalyzer(type: AnalyzerType, factory: AnalyzerFactory): void {
    this.analyzerFactories.set(type, factory);
  }

  /**
   * Create a new pipeline from configuration
   * @trace DES-SEC2-ORCH-002
   */
  createPipeline(config: PipelineConfig): Pipeline {
    const id = randomUUID();
    
    const context: PipelineContext = {
      id,
      config,
      status: 'pending',
      stageStatuses: new Map(config.stages.map(s => [s.id, 'pending'])),
      stageResults: new Map(),
      cancelled: false,
    };
    
    this.runningPipelines.set(id, context);
    
    const pipeline: Pipeline = {
      id,
      config,
      execute: () => this.executePipeline(context),
      cancel: () => this.cancel(id),
    };
    
    return pipeline;
  }

  /**
   * Execute multiple pipelines in parallel
   * @trace REQ-SEC2-PERF-001
   */
  async executeParallel(pipelines: Pipeline[]): Promise<PipelineResult[]> {
    const promises = pipelines.map(p => {
      const context = this.runningPipelines.get(p.id);
      if (!context) {
        throw new Error(`Pipeline ${p.id} not found`);
      }
      return this.executePipeline(context);
    });
    
    return Promise.all(promises);
  }

  /**
   * Execute a single pipeline sequentially
   */
  async executeSequential(pipeline: Pipeline): Promise<PipelineResult> {
    const context = this.runningPipelines.get(pipeline.id);
    if (!context) {
      throw new Error(`Pipeline ${pipeline.id} not found`);
    }
    return this.executePipeline(context);
  }

  /**
   * Cancel a running pipeline
   */
  cancel(pipelineId: string): void {
    const context = this.runningPipelines.get(pipelineId);
    if (context) {
      context.cancelled = true;
      context.status = 'cancelled';
      
      // Mark pending stages as cancelled
      for (const [stageId, status] of context.stageStatuses) {
        if (status === 'pending' || status === 'running') {
          context.stageStatuses.set(stageId, 'cancelled');
        }
      }
    }
  }

  /**
   * Get current pipeline status
   */
  getStatus(pipelineId: string): PipelineProgress | undefined {
    const context = this.runningPipelines.get(pipelineId);
    if (!context) return undefined;
    
    return this.calculateProgress(context);
  }

  /**
   * Execute a pipeline with dependency resolution
   */
  private async executePipeline(context: PipelineContext): Promise<PipelineResult> {
    context.startTime = new Date();
    context.status = 'running';
    
    try {
      // Build dependency graph
      const stageOrder = this.resolveDependencies(context.config.stages);
      
      // Execute stages respecting dependencies
      const maxParallel = context.config.maxParallel ?? 4;
      await this.executeStagesWithDependencies(context, stageOrder, maxParallel);
      
      // Determine final status
      const hasFailures = Array.from(context.stageStatuses.values())
        .some(s => s === 'failed');
      
      context.status = context.cancelled ? 'cancelled' : 
                       hasFailures ? 'failed' : 'completed';
      
    } catch (error) {
      // Rethrow circular dependency errors
      if (error instanceof Error && error.message.includes('Circular dependency')) {
        throw error;
      }
      context.status = 'failed';
    }
    
    context.endTime = new Date();
    
    // Build result
    const result = this.buildResult(context);
    
    // Cleanup
    this.runningPipelines.delete(context.id);
    
    return result;
  }

  /**
   * Resolve stage dependencies and return execution order
   */
  private resolveDependencies(stages: PipelineStage[]): PipelineStage[][] {
    const levels: PipelineStage[][] = [];
    const resolved = new Set<string>();
    
    while (resolved.size < stages.length) {
      const level: PipelineStage[] = [];
      
      for (const stage of stages) {
        if (resolved.has(stage.id)) continue;
        
        const deps = stage.dependsOn ?? [];
        const allDepsResolved = deps.every(d => resolved.has(d));
        
        if (allDepsResolved) {
          level.push(stage);
        }
      }
      
      if (level.length === 0 && resolved.size < stages.length) {
        // Circular dependency detected
        throw new Error('Circular dependency detected in pipeline stages');
      }
      
      for (const stage of level) {
        resolved.add(stage.id);
      }
      
      levels.push(level);
    }
    
    return levels;
  }

  /**
   * Execute stages respecting dependencies with parallel execution
   */
  private async executeStagesWithDependencies(
    context: PipelineContext,
    stageOrder: PipelineStage[][],
    maxParallel: number
  ): Promise<void> {
    for (const level of stageOrder) {
      if (context.cancelled) break;
      
      // Execute stages in this level in parallel (up to maxParallel)
      const chunks = this.chunkArray(level, maxParallel);
      
      for (const chunk of chunks) {
        if (context.cancelled) break;
        
        await Promise.all(
          chunk.map(stage => this.executeStage(context, stage))
        );
        
        this.notifyProgress(context);
      }
    }
  }

  /**
   * Execute a single stage
   */
  private async executeStage(
    context: PipelineContext,
    stage: PipelineStage
  ): Promise<void> {
    if (context.cancelled) {
      context.stageStatuses.set(stage.id, 'cancelled');
      return;
    }
    
    context.stageStatuses.set(stage.id, 'running');
    const startTime = new Date();
    
    try {
      const factory = this.analyzerFactories.get(stage.analyzer);
      if (!factory) {
        throw new Error(`Unknown analyzer type: ${stage.analyzer}`);
      }
      
      const analyzer = factory();
      let result: unknown;
      
      // Execute with timeout if specified
      const timeout = stage.timeout ?? context.config.timeout ?? 300000; // 5 min default
      
      const executePromise = this.runAnalyzer(
        analyzer,
        stage.analyzer,
        context.config.targets,
        stage.options
      );
      
      result = await Promise.race([
        executePromise,
        this.createTimeout(timeout, stage.id),
      ]);
      
      const endTime = new Date();
      
      const stageResult: StageResult = {
        stageId: stage.id,
        status: 'completed',
        duration: endTime.getTime() - startTime.getTime(),
        data: result,
        startedAt: startTime,
        endedAt: endTime,
      };
      
      context.stageResults.set(stage.id, stageResult);
      context.stageStatuses.set(stage.id, 'completed');
      
    } catch (error) {
      const endTime = new Date();
      
      const stageResult: StageResult = {
        stageId: stage.id,
        status: 'failed',
        duration: endTime.getTime() - startTime.getTime(),
        error: error instanceof Error ? error : new Error(String(error)),
        startedAt: startTime,
        endedAt: endTime,
      };
      
      context.stageResults.set(stage.id, stageResult);
      context.stageStatuses.set(stage.id, 'failed');
      
      // Check if we should continue on failure
      if (!stage.continueOnFailure) {
        // Mark dependent stages as skipped
        this.skipDependentStages(context, stage.id);
      }
    }
  }

  /**
   * Run analyzer based on type
   */
  private async runAnalyzer(
    analyzer: ReturnType<AnalyzerFactory>,
    type: AnalyzerType,
    targets: string[],
    options: Record<string, unknown>
  ): Promise<unknown> {
    const target = targets[0] ?? '.'; // Use first target or current directory
    
    switch (type) {
      case 'vulnerability-scanner':
        return analyzer.scan?.(target, options);
      case 'taint-tracker':
        return analyzer.analyze?.(target, options);
      case 'secret-detector':
        return analyzer.detect?.(target, options);
      case 'dependency-auditor':
        return analyzer.audit?.(target, options);
      default:
        // Generic execution for other analyzers
        if (analyzer.scan) return analyzer.scan(target, options);
        if (analyzer.analyze) return analyzer.analyze(target, options);
        if (analyzer.detect) return analyzer.detect(target, options);
        throw new Error(`Analyzer ${type} does not have a known execution method`);
    }
  }

  /**
   * Create timeout promise
   */
  private createTimeout(ms: number, stageId: string): Promise<never> {
    return new Promise((_, reject) => {
      setTimeout(() => {
        reject(new Error(`Stage ${stageId} timed out after ${ms}ms`));
      }, ms);
    });
  }

  /**
   * Skip stages that depend on a failed stage
   */
  private skipDependentStages(context: PipelineContext, failedStageId: string): void {
    for (const stage of context.config.stages) {
      if (stage.dependsOn?.includes(failedStageId)) {
        if (context.stageStatuses.get(stage.id) === 'pending') {
          context.stageStatuses.set(stage.id, 'skipped');
          // Recursively skip dependent stages
          this.skipDependentStages(context, stage.id);
        }
      }
    }
  }

  /**
   * Calculate current progress
   */
  private calculateProgress(context: PipelineContext): PipelineProgress {
    const total = context.config.stages.length;
    const completed = Array.from(context.stageStatuses.values())
      .filter(s => s === 'completed' || s === 'failed' || s === 'skipped' || s === 'cancelled')
      .length;
    
    const runningStages = Array.from(context.stageStatuses.entries())
      .filter(([_, status]) => status === 'running')
      .map(([id]) => id);
    
    const completedStages = Array.from(context.stageStatuses.entries())
      .filter(([_, status]) => status === 'completed')
      .map(([id]) => id);
    
    const failedStages = Array.from(context.stageStatuses.entries())
      .filter(([_, status]) => status === 'failed')
      .map(([id]) => id);
    
    return {
      pipelineId: context.id,
      percentage: Math.round((completed / total) * 100),
      runningStages,
      completedStages,
      failedStages,
    };
  }

  /**
   * Notify progress callback
   */
  private notifyProgress(context: PipelineContext): void {
    if (context.onProgress) {
      context.onProgress(this.calculateProgress(context));
    }
  }

  /**
   * Build final pipeline result
   */
  private buildResult(context: PipelineContext): PipelineResult {
    const stageResults = Array.from(context.stageResults.values());
    
    const statusCounts = {
      completed: 0,
      failed: 0,
      skipped: 0,
      cancelled: 0,
    };
    
    for (const status of context.stageStatuses.values()) {
      if (status === 'completed') statusCounts.completed++;
      else if (status === 'failed') statusCounts.failed++;
      else if (status === 'skipped') statusCounts.skipped++;
      else if (status === 'cancelled') statusCounts.cancelled++;
    }
    
    const endTime = context.endTime ?? new Date();
    const startTime = context.startTime ?? endTime;
    
    return {
      pipelineId: context.id,
      status: context.cancelled ? 'cancelled' :
              statusCounts.failed > 0 ? 'failed' : 'completed',
      stageResults,
      duration: endTime.getTime() - startTime.getTime(),
      startedAt: startTime,
      endedAt: endTime,
      summary: {
        totalStages: context.config.stages.length,
        completedStages: statusCounts.completed,
        failedStages: statusCounts.failed,
        skippedStages: statusCounts.skipped + statusCounts.cancelled,
      },
    };
  }

  /**
   * Split array into chunks
   */
  private chunkArray<T>(array: T[], size: number): T[][] {
    const chunks: T[][] = [];
    for (let i = 0; i < array.length; i += size) {
      chunks.push(array.slice(i, i + size));
    }
    return chunks;
  }
}

/**
 * Create a default pipeline manager instance
 */
export function createPipelineManager(): PipelineManager {
  return new PipelineManager();
}

/**
 * Create a standard security scan pipeline
 * @trace REQ-SEC2-CLI-001
 */
export function createStandardPipeline(
  targets: string[],
  options: {
    vulnerabilities?: boolean;
    taint?: boolean;
    secrets?: boolean;
    dependencies?: boolean;
  } = {}
): PipelineConfig {
  const stages: PipelineStage[] = [];
  
  if (options.vulnerabilities !== false) {
    stages.push({
      id: 'vuln-scan',
      name: 'Vulnerability Scan',
      analyzer: 'vulnerability-scanner',
      options: {},
    });
  }
  
  if (options.taint !== false) {
    stages.push({
      id: 'taint-analysis',
      name: 'Taint Analysis',
      analyzer: 'taint-tracker',
      options: {},
    });
  }
  
  if (options.secrets !== false) {
    stages.push({
      id: 'secret-detection',
      name: 'Secret Detection',
      analyzer: 'secret-detector',
      options: {},
    });
  }
  
  if (options.dependencies !== false) {
    stages.push({
      id: 'dep-audit',
      name: 'Dependency Audit',
      analyzer: 'dependency-auditor',
      options: {},
    });
  }
  
  return {
    stages,
    targets,
    maxParallel: 4,
    cache: true,
  };
}
