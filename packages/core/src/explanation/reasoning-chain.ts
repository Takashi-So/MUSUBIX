/**
 * Reasoning Chain Recorder
 * 
 * Records AI reasoning chains for explainability
 * 
 * @packageDocumentation
 * @module explanation/reasoning-chain
 * 
 * @see REQ-EXP-001 - Reasoning Chain Recording
 * @see Article VIII - Transparency Standards
 */

/**
 * Reasoning step type
 */
export type ReasoningStepType =
  | 'input'
  | 'analysis'
  | 'inference'
  | 'decision'
  | 'action'
  | 'validation'
  | 'output'
  | 'error'
  | 'fallback';

/**
 * Confidence level
 */
export type ConfidenceLevel = 'high' | 'medium' | 'low' | 'uncertain';

/**
 * Reasoning step
 */
export interface ReasoningStep {
  /** Step ID */
  id: string;
  /** Step type */
  type: ReasoningStepType;
  /** Step description */
  description: string;
  /** Input data */
  input?: unknown;
  /** Output data */
  output?: unknown;
  /** Confidence level */
  confidence: ConfidenceLevel;
  /** Confidence score (0-1) */
  confidenceScore: number;
  /** Timestamp */
  timestamp: Date;
  /** Duration (ms) */
  duration?: number;
  /** Parent step ID */
  parentId?: string;
  /** Evidence/sources */
  evidence?: Evidence[];
  /** Alternatives considered */
  alternatives?: Alternative[];
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Evidence for a reasoning step
 */
export interface Evidence {
  /** Evidence ID */
  id: string;
  /** Evidence type */
  type: 'knowledge' | 'rule' | 'pattern' | 'data' | 'user-input' | 'external';
  /** Source */
  source: string;
  /** Content */
  content: string;
  /** Relevance score (0-1) */
  relevance: number;
  /** Verification status */
  verified: boolean;
}

/**
 * Alternative considered
 */
export interface Alternative {
  /** Alternative ID */
  id: string;
  /** Description */
  description: string;
  /** Why rejected */
  rejectionReason: string;
  /** Score compared to chosen */
  score: number;
}

/**
 * Reasoning chain
 */
export interface ReasoningChain {
  /** Chain ID */
  id: string;
  /** Session ID */
  sessionId: string;
  /** Task/query that initiated the chain */
  task: string;
  /** Steps in the chain */
  steps: ReasoningStep[];
  /** Start time */
  startTime: Date;
  /** End time */
  endTime?: Date;
  /** Final outcome */
  outcome?: ChainOutcome;
  /** Overall confidence */
  overallConfidence: number;
  /** Chain status */
  status: 'in-progress' | 'completed' | 'failed' | 'cancelled';
  /** Error if failed */
  error?: string;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Chain outcome
 */
export interface ChainOutcome {
  /** Success */
  success: boolean;
  /** Result */
  result?: unknown;
  /** Summary */
  summary: string;
  /** Key decisions made */
  keyDecisions: string[];
  /** Uncertainties */
  uncertainties: string[];
}

/**
 * Reasoning chain query
 */
export interface ChainQuery {
  /** Session IDs */
  sessionIds?: string[];
  /** Time range */
  timeRange?: {
    start: Date;
    end: Date;
  };
  /** Status filter */
  status?: ReasoningChain['status'][];
  /** Minimum confidence */
  minConfidence?: number;
  /** Task pattern */
  taskPattern?: string;
  /** Limit */
  limit?: number;
}

/**
 * Chain statistics
 */
export interface ChainStatistics {
  /** Total chains */
  totalChains: number;
  /** Completed chains */
  completedChains: number;
  /** Failed chains */
  failedChains: number;
  /** Average steps per chain */
  avgStepsPerChain: number;
  /** Average confidence */
  avgConfidence: number;
  /** Average duration (ms) */
  avgDuration: number;
  /** Step type distribution */
  stepTypeDistribution: Record<ReasoningStepType, number>;
  /** Confidence distribution */
  confidenceDistribution: Record<ConfidenceLevel, number>;
}

/**
 * Reasoning chain recorder config
 */
export interface ReasoningChainRecorderConfig {
  /** Maximum steps per chain */
  maxStepsPerChain: number;
  /** Maximum chains to keep in memory */
  maxChainsInMemory: number;
  /** Auto-persist chains */
  autoPersist: boolean;
  /** Persist threshold (chains in memory before persist) */
  persistThreshold: number;
  /** Record detailed evidence */
  recordEvidence: boolean;
  /** Record alternatives */
  recordAlternatives: boolean;
  /** Minimum confidence to record */
  minConfidenceToRecord: number;
}

/**
 * Default configuration
 */
export const DEFAULT_RECORDER_CONFIG: ReasoningChainRecorderConfig = {
  maxStepsPerChain: 100,
  maxChainsInMemory: 1000,
  autoPersist: true,
  persistThreshold: 100,
  recordEvidence: true,
  recordAlternatives: true,
  minConfidenceToRecord: 0,
};

/**
 * Reasoning Chain Recorder
 */
export class ReasoningChainRecorder {
  private config: ReasoningChainRecorderConfig;
  private chains: Map<string, ReasoningChain>;
  private activeChain: ReasoningChain | null = null;
  private stepCounter = 0;
  private persistedChains: ReasoningChain[] = [];

  constructor(config?: Partial<ReasoningChainRecorderConfig>) {
    this.config = { ...DEFAULT_RECORDER_CONFIG, ...config };
    this.chains = new Map();
  }

  /**
   * Start a new reasoning chain
   */
  startChain(task: string, sessionId?: string): string {
    const chainId = this.generateId('chain');
    const chain: ReasoningChain = {
      id: chainId,
      sessionId: sessionId ?? this.generateId('session'),
      task,
      steps: [],
      startTime: new Date(),
      overallConfidence: 1,
      status: 'in-progress',
    };

    this.chains.set(chainId, chain);
    this.activeChain = chain;

    // Check memory limit
    this.checkMemoryLimit();

    return chainId;
  }

  /**
   * Add a step to the current chain
   */
  addStep(
    type: ReasoningStepType,
    description: string,
    options?: {
      input?: unknown;
      output?: unknown;
      confidence?: number;
      parentId?: string;
      evidence?: Evidence[];
      alternatives?: Alternative[];
      metadata?: Record<string, unknown>;
    }
  ): string {
    if (!this.activeChain) {
      throw new Error('No active reasoning chain. Call startChain() first.');
    }

    if (this.activeChain.steps.length >= this.config.maxStepsPerChain) {
      throw new Error(`Maximum steps (${this.config.maxStepsPerChain}) reached for this chain.`);
    }

    const stepId = this.generateId('step');
    const confidenceScore = options?.confidence ?? 1;
    const step: ReasoningStep = {
      id: stepId,
      type,
      description,
      input: options?.input,
      output: options?.output,
      confidence: this.scoreToLevel(confidenceScore),
      confidenceScore,
      timestamp: new Date(),
      parentId: options?.parentId,
      evidence: this.config.recordEvidence ? options?.evidence : undefined,
      alternatives: this.config.recordAlternatives ? options?.alternatives : undefined,
      metadata: options?.metadata,
    };

    // Calculate duration from previous step
    if (this.activeChain.steps.length > 0) {
      const prevStep = this.activeChain.steps[this.activeChain.steps.length - 1];
      prevStep.duration = step.timestamp.getTime() - prevStep.timestamp.getTime();
    }

    // Filter by minimum confidence
    if (confidenceScore >= this.config.minConfidenceToRecord) {
      this.activeChain.steps.push(step);
    }

    // Update overall confidence
    this.updateOverallConfidence();

    return stepId;
  }

  /**
   * Record input step
   */
  recordInput(description: string, input: unknown, confidence = 1): string {
    return this.addStep('input', description, { input, confidence });
  }

  /**
   * Record analysis step
   */
  recordAnalysis(
    description: string,
    input: unknown,
    output: unknown,
    confidence = 1,
    evidence?: Evidence[]
  ): string {
    return this.addStep('analysis', description, { input, output, confidence, evidence });
  }

  /**
   * Record inference step
   */
  recordInference(
    description: string,
    premises: unknown[],
    conclusion: unknown,
    confidence = 1,
    alternatives?: Alternative[]
  ): string {
    return this.addStep('inference', description, {
      input: premises,
      output: conclusion,
      confidence,
      alternatives,
    });
  }

  /**
   * Record decision step
   */
  recordDecision(
    description: string,
    options: unknown[],
    chosen: unknown,
    confidence = 1,
    alternatives?: Alternative[]
  ): string {
    return this.addStep('decision', description, {
      input: options,
      output: chosen,
      confidence,
      alternatives,
    });
  }

  /**
   * Record action step
   */
  recordAction(description: string, action: unknown, result: unknown, confidence = 1): string {
    return this.addStep('action', description, { input: action, output: result, confidence });
  }

  /**
   * Record validation step
   */
  recordValidation(
    description: string,
    data: unknown,
    isValid: boolean,
    confidence = 1,
    evidence?: Evidence[]
  ): string {
    return this.addStep('validation', description, {
      input: data,
      output: isValid,
      confidence,
      evidence,
    });
  }

  /**
   * Record output step
   */
  recordOutput(description: string, output: unknown, confidence = 1): string {
    return this.addStep('output', description, { output, confidence });
  }

  /**
   * Record error step
   */
  recordError(description: string, error: unknown, confidence = 1): string {
    return this.addStep('error', description, { input: error, confidence });
  }

  /**
   * Record fallback step
   */
  recordFallback(description: string, reason: string, fallbackAction: unknown, confidence = 1): string {
    return this.addStep('fallback', description, {
      input: reason,
      output: fallbackAction,
      confidence,
    });
  }

  /**
   * Complete the current chain
   */
  completeChain(outcome: ChainOutcome): ReasoningChain {
    if (!this.activeChain) {
      throw new Error('No active reasoning chain to complete.');
    }

    this.activeChain.endTime = new Date();
    this.activeChain.outcome = outcome;
    this.activeChain.status = outcome.success ? 'completed' : 'failed';

    // Calculate final step duration
    if (this.activeChain.steps.length > 0) {
      const lastStep = this.activeChain.steps[this.activeChain.steps.length - 1];
      lastStep.duration = this.activeChain.endTime.getTime() - lastStep.timestamp.getTime();
    }

    const completedChain = this.activeChain;
    this.activeChain = null;

    // Auto-persist if configured
    if (this.config.autoPersist && this.chains.size >= this.config.persistThreshold) {
      this.persistChains();
    }

    return completedChain;
  }

  /**
   * Cancel the current chain
   */
  cancelChain(reason?: string): void {
    if (this.activeChain) {
      this.activeChain.endTime = new Date();
      this.activeChain.status = 'cancelled';
      this.activeChain.error = reason;
      this.activeChain = null;
    }
  }

  /**
   * Fail the current chain
   */
  failChain(error: string): ReasoningChain | null {
    if (!this.activeChain) {
      return null;
    }

    this.activeChain.endTime = new Date();
    this.activeChain.status = 'failed';
    this.activeChain.error = error;

    const failedChain = this.activeChain;
    this.activeChain = null;

    return failedChain;
  }

  /**
   * Get current active chain
   */
  getActiveChain(): ReasoningChain | null {
    return this.activeChain;
  }

  /**
   * Get chain by ID
   */
  getChain(chainId: string): ReasoningChain | undefined {
    return this.chains.get(chainId);
  }

  /**
   * Query chains
   */
  queryChains(query: ChainQuery): ReasoningChain[] {
    let results = [...this.chains.values(), ...this.persistedChains];

    // Filter by session IDs
    if (query.sessionIds?.length) {
      results = results.filter((c) => query.sessionIds!.includes(c.sessionId));
    }

    // Filter by time range
    if (query.timeRange) {
      results = results.filter(
        (c) =>
          c.startTime >= query.timeRange!.start &&
          c.startTime <= query.timeRange!.end
      );
    }

    // Filter by status
    if (query.status?.length) {
      results = results.filter((c) => query.status!.includes(c.status));
    }

    // Filter by confidence
    if (query.minConfidence !== undefined) {
      results = results.filter((c) => c.overallConfidence >= query.minConfidence!);
    }

    // Filter by task pattern
    if (query.taskPattern) {
      const pattern = new RegExp(query.taskPattern, 'i');
      results = results.filter((c) => pattern.test(c.task));
    }

    // Sort by start time (newest first)
    results.sort((a, b) => b.startTime.getTime() - a.startTime.getTime());

    // Apply limit
    if (query.limit) {
      results = results.slice(0, query.limit);
    }

    return results;
  }

  /**
   * Get statistics
   */
  getStatistics(): ChainStatistics {
    const allChains = [...this.chains.values(), ...this.persistedChains];
    
    const stepTypeDistribution: Record<ReasoningStepType, number> = {
      input: 0,
      analysis: 0,
      inference: 0,
      decision: 0,
      action: 0,
      validation: 0,
      output: 0,
      error: 0,
      fallback: 0,
    };

    const confidenceDistribution: Record<ConfidenceLevel, number> = {
      high: 0,
      medium: 0,
      low: 0,
      uncertain: 0,
    };

    let totalSteps = 0;
    let totalConfidence = 0;
    let totalDuration = 0;
    let completedCount = 0;
    let failedCount = 0;

    for (const chain of allChains) {
      totalSteps += chain.steps.length;
      totalConfidence += chain.overallConfidence;

      if (chain.endTime) {
        totalDuration += chain.endTime.getTime() - chain.startTime.getTime();
      }

      if (chain.status === 'completed') completedCount++;
      if (chain.status === 'failed') failedCount++;

      for (const step of chain.steps) {
        stepTypeDistribution[step.type]++;
        confidenceDistribution[step.confidence]++;
      }
    }

    const chainCount = allChains.length;

    return {
      totalChains: chainCount,
      completedChains: completedCount,
      failedChains: failedCount,
      avgStepsPerChain: chainCount > 0 ? Math.round((totalSteps / chainCount) * 100) / 100 : 0,
      avgConfidence: chainCount > 0 ? Math.round((totalConfidence / chainCount) * 100) / 100 : 0,
      avgDuration: chainCount > 0 ? Math.round(totalDuration / chainCount) : 0,
      stepTypeDistribution,
      confidenceDistribution,
    };
  }

  /**
   * Export chain to JSON
   */
  exportChain(chainId: string): string | null {
    const chain = this.getChain(chainId);
    if (!chain) return null;
    return JSON.stringify(chain, null, 2);
  }

  /**
   * Import chain from JSON
   */
  importChain(json: string): ReasoningChain {
    const chain = JSON.parse(json) as ReasoningChain;
    chain.startTime = new Date(chain.startTime);
    if (chain.endTime) chain.endTime = new Date(chain.endTime);
    for (const step of chain.steps) {
      step.timestamp = new Date(step.timestamp);
    }
    this.chains.set(chain.id, chain);
    return chain;
  }

  /**
   * Clear all chains
   */
  clear(): void {
    this.chains.clear();
    this.persistedChains = [];
    this.activeChain = null;
  }

  /**
   * Generate unique ID
   */
  private generateId(prefix: string): string {
    this.stepCounter++;
    return `${prefix}-${Date.now()}-${this.stepCounter}`;
  }

  /**
   * Convert confidence score to level
   */
  private scoreToLevel(score: number): ConfidenceLevel {
    if (score >= 0.8) return 'high';
    if (score >= 0.5) return 'medium';
    if (score >= 0.2) return 'low';
    return 'uncertain';
  }

  /**
   * Update overall confidence of active chain
   */
  private updateOverallConfidence(): void {
    if (!this.activeChain || this.activeChain.steps.length === 0) return;

    const scores = this.activeChain.steps.map((s) => s.confidenceScore);
    // Use geometric mean for combined confidence
    const product = scores.reduce((a, b) => a * b, 1);
    this.activeChain.overallConfidence = Math.pow(product, 1 / scores.length);
  }

  /**
   * Check and enforce memory limit
   */
  private checkMemoryLimit(): void {
    if (this.chains.size > this.config.maxChainsInMemory) {
      // Persist oldest chains
      const chainsToMove = this.chains.size - this.config.maxChainsInMemory + 10;
      const sortedChains = [...this.chains.entries()]
        .sort((a, b) => a[1].startTime.getTime() - b[1].startTime.getTime());

      for (let i = 0; i < chainsToMove && i < sortedChains.length; i++) {
        const [id, chain] = sortedChains[i];
        if (chain !== this.activeChain) {
          this.persistedChains.push(chain);
          this.chains.delete(id);
        }
      }
    }
  }

  /**
   * Persist chains to storage
   */
  private persistChains(): void {
    const completedChains = [...this.chains.values()].filter(
      (c) => c.status !== 'in-progress' && c !== this.activeChain
    );

    for (const chain of completedChains) {
      this.persistedChains.push(chain);
      this.chains.delete(chain.id);
    }
  }
}

/**
 * Create reasoning chain recorder instance
 */
export function createReasoningChainRecorder(
  config?: Partial<ReasoningChainRecorderConfig>
): ReasoningChainRecorder {
  return new ReasoningChainRecorder(config);
}
