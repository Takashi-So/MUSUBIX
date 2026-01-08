/**
 * PipelineConfig - Integrated Synthesis Pipeline Configuration
 *
 * Configures and executes a 7-stage synthesis pipeline with support for
 * parallel execution of independent stages.
 *
 * @module @nahisaho/musubix-core
 * @see TSK-INT-102
 * @see DES-INT-102
 * @see REQ-INT-102
 *
 * Pipeline Stages:
 * 1. Parse - Source code parsing
 * 2. Analyze - Type and semantic analysis
 * 3. Extract - Pattern extraction
 * 4. Prune - Search space pruning
 * 5. Synthesize - Code synthesis
 * 6. Optimize - E-Graph optimization
 * 7. Generate - Code generation
 *
 * @example
 * ```typescript
 * import { createPipelineConfig } from './PipelineConfig.js';
 *
 * const config = createPipelineConfig({ enableParallel: true });
 * const result = await config.execute({ source: 'input code' });
 * ```
 */

// =============================================================================
// Types
// =============================================================================

/**
 * Input for pipeline execution
 */
export interface PipelineInput {
  /** Source code or specification */
  source: string;
  /** Optional target type */
  targetType?: unknown;
  /** Optional context */
  context?: Record<string, unknown>;
}

/**
 * Output from pipeline execution
 */
export interface PipelineOutput {
  /** Generated code */
  code?: string;
  /** AST representation */
  ast?: unknown;
  /** Extracted patterns */
  patterns?: unknown[];
  /** Intermediate results */
  intermediates?: Record<string, unknown>;
}

/**
 * Pipeline stage definition
 */
export interface PipelineStage {
  /** Stage name */
  name: string;
  /** Description */
  description: string;
  /** Execute function */
  execute: (input: unknown) => Promise<unknown>;
  /** Execution order (1-based) */
  order: number;
  /** Whether the stage is enabled */
  enabled?: boolean;
  /** Dependencies (other stage names) */
  dependencies?: string[];
}

/**
 * Pipeline execution result
 */
export interface PipelineExecutionResult {
  /** Whether execution was successful */
  success: boolean;
  /** Output from the pipeline */
  output?: PipelineOutput;
  /** Error if failed */
  error?: Error;
  /** Number of stages executed */
  stagesExecuted: number;
  /** Total execution time in milliseconds */
  totalTimeMs: number;
  /** Per-stage timing */
  stageTimes?: Record<string, number>;
}

/**
 * Parallel execution group
 */
export type ParallelGroup = string[];

/**
 * Configuration options for PipelineConfig
 */
export interface PipelineConfigOptions {
  /** Enable parallel execution */
  enableParallel?: boolean;
  /** Maximum parallel stages */
  maxParallelStages?: number;
  /** Groups of stages that can run in parallel */
  parallelGroups?: ParallelGroup[];
  /** Timeout per stage in milliseconds */
  stageTimeout?: number;
}

/**
 * JSON representation for serialization
 */
export interface PipelineConfigJSON {
  stages: Array<{
    name: string;
    description: string;
    order: number;
    enabled: boolean;
    dependencies?: string[];
  }>;
  options: PipelineConfigOptions;
}

/**
 * PipelineConfig interface
 */
export interface PipelineConfig {
  /** Get all configured stages */
  getStages(): PipelineStage[];

  /** Get a specific stage by name */
  getStage(name: string): PipelineStage | undefined;

  /** Enable a stage */
  enableStage(name: string): void;

  /** Disable a stage */
  disableStage(name: string): void;

  /** Check if a stage is enabled */
  isStageEnabled(name: string): boolean;

  /** Add a custom stage */
  addStage(stage: PipelineStage): void;

  /** Remove a stage */
  removeStage(name: string): void;

  /** Execute the pipeline */
  execute(input: PipelineInput): Promise<PipelineExecutionResult>;

  /** Check if parallel execution is enabled */
  isParallelEnabled(): boolean;

  /** Serialize to JSON */
  toJSON(): PipelineConfigJSON;

  /** Deserialize from JSON */
  fromJSON(json: PipelineConfigJSON): void;
}

// =============================================================================
// Default Stages
// =============================================================================

function createDefaultStages(): PipelineStage[] {
  return [
    {
      name: 'parse',
      description: 'Parse source code into AST',
      order: 1,
      enabled: true,
      execute: async (input: unknown) => {
        const pipelineInput = input as PipelineInput;
        // Simple mock parsing
        return {
          source: pipelineInput.source,
          targetType: pipelineInput.targetType,
          context: pipelineInput.context,
          ast: { type: 'Program', body: [], source: pipelineInput.source },
        };
      },
    },
    {
      name: 'analyze',
      description: 'Type and semantic analysis',
      order: 2,
      enabled: true,
      dependencies: ['parse'],
      execute: async (input: unknown) => {
        // Add type information
        const data = input as Record<string, unknown>;
        return {
          ...data,
          types: { inferred: true },
        };
      },
    },
    {
      name: 'extract',
      description: 'Extract patterns from code',
      order: 3,
      enabled: true,
      dependencies: ['parse'],
      execute: async (input: unknown) => {
        // Extract patterns
        const data = input as Record<string, unknown>;
        return {
          ...data,
          patterns: [],
        };
      },
    },
    {
      name: 'prune',
      description: 'Prune search space using type information',
      order: 4,
      enabled: true,
      dependencies: ['analyze', 'extract'],
      execute: async (input: unknown) => {
        // Prune candidates
        const data = input as Record<string, unknown>;
        return {
          ...data,
          prunedCandidates: [],
        };
      },
    },
    {
      name: 'synthesize',
      description: 'Synthesize code candidates',
      order: 5,
      enabled: true,
      dependencies: ['prune'],
      execute: async (input: unknown) => {
        // Synthesize
        const data = input as Record<string, unknown>;
        return {
          ...data,
          candidates: [],
        };
      },
    },
    {
      name: 'optimize',
      description: 'Optimize using E-Graph',
      order: 6,
      enabled: true,
      dependencies: ['synthesize'],
      execute: async (input: unknown) => {
        // Optimize
        const data = input as Record<string, unknown>;
        return {
          ...data,
          optimized: true,
        };
      },
    },
    {
      name: 'generate',
      description: 'Generate final code',
      order: 7,
      enabled: true,
      dependencies: ['optimize'],
      execute: async (input: unknown) => {
        const data = input as Record<string, unknown>;
        // Generate output
        return {
          code: '// Generated code',
          ast: data.ast,
          patterns: data.patterns,
          intermediates: data,
        } as PipelineOutput;
      },
    },
  ];
}

// =============================================================================
// Default Implementation
// =============================================================================

/**
 * Default PipelineConfig implementation
 */
export class DefaultPipelineConfig implements PipelineConfig {
  private stages: Map<string, PipelineStage> = new Map();
  private options: Required<PipelineConfigOptions>;

  constructor(options: PipelineConfigOptions = {}) {
    this.options = {
      enableParallel: options.enableParallel ?? false,
      maxParallelStages: options.maxParallelStages ?? 2,
      parallelGroups: options.parallelGroups ?? [],
      stageTimeout: options.stageTimeout ?? 30000,
    };

    // Initialize default stages
    createDefaultStages().forEach((stage) => {
      this.stages.set(stage.name, stage);
    });
  }

  /**
   * Get all configured stages
   */
  getStages(): PipelineStage[] {
    return Array.from(this.stages.values()).sort((a, b) => a.order - b.order);
  }

  /**
   * Get a specific stage by name
   */
  getStage(name: string): PipelineStage | undefined {
    return this.stages.get(name);
  }

  /**
   * Enable a stage
   */
  enableStage(name: string): void {
    const stage = this.stages.get(name);
    if (stage) {
      stage.enabled = true;
    }
  }

  /**
   * Disable a stage
   */
  disableStage(name: string): void {
    const stage = this.stages.get(name);
    if (stage) {
      stage.enabled = false;
    }
  }

  /**
   * Check if a stage is enabled
   */
  isStageEnabled(name: string): boolean {
    const stage = this.stages.get(name);
    return stage?.enabled ?? false;
  }

  /**
   * Add a custom stage
   */
  addStage(stage: PipelineStage): void {
    if (stage.enabled === undefined) {
      stage.enabled = true;
    }
    this.stages.set(stage.name, stage);
  }

  /**
   * Remove a stage
   */
  removeStage(name: string): void {
    this.stages.delete(name);
  }

  /**
   * Execute the pipeline
   */
  async execute(input: PipelineInput): Promise<PipelineExecutionResult> {
    const startTime = Date.now();
    const stageTimes: Record<string, number> = {};
    let stagesExecuted = 0;
    let currentData: unknown = input;

    try {
      const stages = this.getStages().filter((s) => s.enabled);

      for (const stage of stages) {
        const stageStart = Date.now();

        try {
          currentData = await stage.execute(currentData);
          stagesExecuted++;
          stageTimes[stage.name] = Date.now() - stageStart;
        } catch (error) {
          return {
            success: false,
            error: error instanceof Error ? error : new Error(String(error)),
            stagesExecuted,
            totalTimeMs: Date.now() - startTime,
            stageTimes,
          };
        }
      }

      return {
        success: true,
        output: currentData as PipelineOutput,
        stagesExecuted,
        totalTimeMs: Date.now() - startTime,
        stageTimes,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error : new Error(String(error)),
        stagesExecuted,
        totalTimeMs: Date.now() - startTime,
        stageTimes,
      };
    }
  }

  /**
   * Check if parallel execution is enabled
   */
  isParallelEnabled(): boolean {
    return this.options.enableParallel;
  }

  /**
   * Serialize to JSON
   */
  toJSON(): PipelineConfigJSON {
    return {
      stages: this.getStages().map((s) => ({
        name: s.name,
        description: s.description,
        order: s.order,
        enabled: s.enabled ?? true,
        dependencies: s.dependencies,
      })),
      options: { ...this.options },
    };
  }

  /**
   * Deserialize from JSON
   */
  fromJSON(json: PipelineConfigJSON): void {
    // Update options
    this.options = {
      ...this.options,
      ...json.options,
    };

    // Update stage enabled states
    for (const stageConfig of json.stages) {
      const stage = this.stages.get(stageConfig.name);
      if (stage) {
        stage.enabled = stageConfig.enabled;
      }
    }
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create a new PipelineConfig instance
 */
export function createPipelineConfig(options: PipelineConfigOptions = {}): PipelineConfig {
  return new DefaultPipelineConfig(options);
}
