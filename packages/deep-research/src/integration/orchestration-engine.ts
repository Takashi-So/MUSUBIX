// Orchestration Engine
// TSK-DR-024
// REQ: REQ-DR-INT-004
// DES: DES-DR-v3.4.0 Section 5.3

import type { ResearchContext } from '../types/index.js';

/**
 * Task complexity threshold
 */
export const COMPLEXITY_THRESHOLD = {
  LOW: 3,
  MEDIUM: 6,
  HIGH: 9,
} as const;

/**
 * Complexity analysis result
 */
export interface ComplexityAnalysis {
  score: number;
  factors: ComplexityFactor[];
  shouldDelegate: boolean;
  recommendedSubagents: number;
}

/**
 * Complexity factor
 */
export interface ComplexityFactor {
  name: string;
  weight: number;
  description: string;
}

/**
 * Subagent task
 */
export interface SubagentTask {
  id: string;
  description: string;
  context: ResearchContext;
  priority: number;
}

/**
 * Orchestration result
 */
export interface OrchestrationResult {
  tasks: SubagentTask[];
  parallelizable: boolean;
  estimatedTime: number;
}

/**
 * Orchestration Engine
 * 
 * Integrates with @nahisaho/musubix-agent-orchestrator for complex task management.
 * 
 * Features:
 * - Task complexity analysis
 * - Subagent task decomposition
 * - Parallel execution coordination
 * - Result aggregation
 * 
 * REQ: REQ-DR-INT-004 - Agent Orchestrator integration
 * DES: DES-DR-v3.4.0 Section 5.3 - Agent Orchestrator integration pattern
 */
export class OrchestrationEngine {
  private readonly complexityThreshold: number;
  
  constructor(complexityThreshold: number = COMPLEXITY_THRESHOLD.MEDIUM) {
    this.complexityThreshold = complexityThreshold;
  }
  
  /**
   * Analyze task complexity
   */
  async analyzeComplexity(context: ResearchContext): Promise<ComplexityAnalysis> {
    console.log(`📊 Analyzing task complexity...`);
    
    const factors: ComplexityFactor[] = [];
    let totalScore = 0;
    
    // Factor 1: Query complexity (length, keywords)
    const queryComplexity = this.assessQueryComplexity(context.query);
    factors.push({
      name: 'Query Complexity',
      weight: queryComplexity,
      description: 'Based on query length and keyword count',
    });
    totalScore += queryComplexity;
    
    // Factor 2: Knowledge base size
    const knowledgeComplexity = this.assessKnowledgeComplexity(context.knowledgeBase.length);
    factors.push({
      name: 'Knowledge Complexity',
      weight: knowledgeComplexity,
      description: 'Based on accumulated knowledge size',
    });
    totalScore += knowledgeComplexity;
    
    // Factor 3: Iteration depth
    const iterationComplexity = this.assessIterationComplexity(context.iteration, context.maxIterations);
    factors.push({
      name: 'Iteration Complexity',
      weight: iterationComplexity,
      description: 'Based on iteration depth',
    });
    totalScore += iterationComplexity;
    
    const avgScore = totalScore / factors.length;
    const shouldDelegate = avgScore >= this.complexityThreshold;
    const recommendedSubagents = shouldDelegate ? this.calculateSubagentCount(avgScore) : 0;
    
    console.log(`✅ Complexity score: ${avgScore.toFixed(2)} (threshold: ${this.complexityThreshold})`);
    
    return {
      score: avgScore,
      factors,
      shouldDelegate,
      recommendedSubagents,
    };
  }
  
  /**
   * Decompose research into subagent tasks
   */
  async decomposeResearch(context: ResearchContext): Promise<OrchestrationResult> {
    console.log(`🔀 Decomposing research into subagent tasks...`);
    
    const complexity = await this.analyzeComplexity(context);
    
    if (!complexity.shouldDelegate) {
      console.log(`📝 Task complexity below threshold, no delegation needed`);
      return {
        tasks: [],
        parallelizable: false,
        estimatedTime: 0,
      };
    }
    
    // Check if orchestrator package is available
    const orchestrator = await this.loadOrchestrator();
    
    if (!orchestrator) {
      console.warn('⚠️  Agent orchestrator not available, skipping delegation');
      return {
        tasks: [],
        parallelizable: false,
        estimatedTime: 0,
      };
    }
    
    // Decompose using orchestrator
    const tasks = await orchestrator.decompose({
      query: context.query,
      knowledgeBase: context.knowledgeBase,
      iteration: context.iteration,
      subagentCount: complexity.recommendedSubagents,
    });
    
    console.log(`✅ Decomposed into ${tasks.length} subagent tasks`);
    
    return {
      tasks,
      parallelizable: tasks.length > 1,
      estimatedTime: this.estimateTime(tasks.length),
    };
  }
  
  /**
   * Assess query complexity (1-10 scale)
   */
  private assessQueryComplexity(query: string): number {
    const words = query.split(/\s+/).length;
    const keywords = query.match(/\b(how|what|why|when|where|which|explain|analyze|compare)\b/gi)?.length || 0;
    
    // Base score on word count
    let score = Math.min(words / 5, 5);
    
    // Add bonus for complex keywords
    score += Math.min(keywords, 3);
    
    return Math.min(score, 10);
  }
  
  /**
   * Assess knowledge complexity (1-10 scale)
   */
  private assessKnowledgeComplexity(knowledgeCount: number): number {
    // More knowledge = higher complexity
    return Math.min(knowledgeCount / 5, 10);
  }
  
  /**
   * Assess iteration complexity (1-10 scale)
   */
  private assessIterationComplexity(current: number, max: number): number {
    // Later iterations = higher complexity
    const ratio = current / max;
    return ratio * 10;
  }
  
  /**
   * Calculate recommended subagent count
   */
  private calculateSubagentCount(complexityScore: number): number {
    if (complexityScore < COMPLEXITY_THRESHOLD.MEDIUM) return 1;
    if (complexityScore < COMPLEXITY_THRESHOLD.HIGH) return 2;
    return 3;
  }
  
  /**
   * Estimate time for subagent execution
   */
  private estimateTime(taskCount: number): number {
    // Assume 30 seconds per task with parallel execution
    return Math.ceil((taskCount * 30000) / 2);
  }
  
  /**
   * Load agent-orchestrator package dynamically
   */
  private async loadOrchestrator(): Promise<any> {
    try {
      const module = await import('@nahisaho/musubix-agent-orchestrator' as any);
      
      // Get SubagentDispatcher
      const { SubagentDispatcher } = module;
      
      if (!SubagentDispatcher) {
        console.warn('⚠️  SubagentDispatcher not found in module');
        return null;
      }
      
      // SubagentDispatcher is available but not used in mock implementation
      // In real implementation, would use: new SubagentDispatcher()
      
      return {
        decompose: async (config: any) => {
          // Mock decomposition for now
          // In real implementation, would call dispatcher.dispatch()
          const tasks: SubagentTask[] = [];
          
          for (let i = 0; i < config.subagentCount; i++) {
            tasks.push({
              id: `subagent-${i + 1}`,
              description: `Research subtask ${i + 1} for: ${config.query}`,
              context: {
                query: config.query,
                knowledgeBase: config.knowledgeBase,
                iteration: config.iteration,
                maxIterations: 10,
              },
              priority: i + 1,
            });
          }
          
          return tasks;
        },
      };
    } catch (error) {
      console.warn('⚠️  @nahisaho/musubix-agent-orchestrator not available');
      return null;
    }
  }
  
  /**
   * Check if orchestrator is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      const orchestrator = await this.loadOrchestrator();
      return orchestrator !== null;
    } catch (error) {
      return false;
    }
  }
}

/**
 * Create an orchestration engine instance
 */
export function createOrchestrationEngine(
  complexityThreshold?: number
): OrchestrationEngine {
  return new OrchestrationEngine(complexityThreshold);
}
