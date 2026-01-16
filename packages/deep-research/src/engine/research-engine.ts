// Research Engine - Template Method Pattern
// TSK-DR-001
// REQ: REQ-DR-CORE-001
// ADR: ADR-v3.4.0-001

import { KnowledgeBase } from '../knowledge/knowledge-base.js';
import { TokenTracker } from '../utils/token-tracker.js';
import { TrajectoryLogger } from '../utils/trajectory-logger.js';
import { ReportGenerator } from '../reporters/report-generator.js';
import type {
  ResearchConfig,
  ResearchReport,
  ReflectiveQuestion,
  SearchResult,
  WebContent,
  KnowledgeItem,
} from '../types/index.js';
import { InvalidConfigurationError } from '../types/errors.js';

/**
 * Research Engine - Main orchestrator using Template Method Pattern
 * 
 * REQ: REQ-DR-CORE-001 - Iterative search-read-reason cycle
 * ADR: ADR-v3.4.0-001 - Template Method Pattern architecture
 * 
 * Flow:
 * 1. initialize()
 * 2. while (!shouldStop())
 *    a. generateQuestions()
 *    b. search()
 *    c. read()
 *    d. reason()
 *    e. evaluate()
 * 3. generateReport()
 */
export class ResearchEngine {
  protected knowledge: KnowledgeBase;
  protected tokenTracker: TokenTracker;
  protected logger: TrajectoryLogger;
  protected reportGenerator: ReportGenerator;
  
  protected config: ResearchConfig;
  protected iteration: number = 0;
  protected startTime: number = 0;
  protected definitiveAnswer: string | null = null;
  
  constructor(config: ResearchConfig) {
    this.validateConfig(config);
    this.config = {
      maxIterations: 10,
      tokenBudget: 15000,
      outputFormat: 'markdown',
      ...config,
    };
    
    this.knowledge = new KnowledgeBase();
    this.tokenTracker = new TokenTracker(this.config.tokenBudget!);
    this.logger = new TrajectoryLogger();
    this.reportGenerator = new ReportGenerator();
  }
  
  /**
   * Main research method - Template Method
   * 
   * REQ: REQ-DR-CORE-001 - Iterative cycle
   */
  async research(): Promise<ResearchReport> {
    this.initialize();
    
    while (!this.shouldStop()) {
      console.log(`\n🔍 === Iteration ${this.iteration + 1}/${this.config.maxIterations} ===`);
      
      try {
        // Generate reflective questions
        const questions = await this.generateQuestions();
        
        // Search for information
        const searchResults = await this.search(questions);
        this.logger.logIteration({
          iteration: this.iteration,
          action: {
            type: 'search',
            query: questions[0]?.question || this.config.query,
            resultsCount: searchResults.length,
          },
          tokensUsed: 0,
          knowledgeGained: 0,
          timestamp: Date.now(),
        });
        
        // Read web contents
        const contents = await this.read(searchResults);
        
        // Reason and extract knowledge
        const knowledgeItems = await this.reason(contents);
        this.knowledge.addAll(knowledgeItems);
        
        this.logger.logIteration({
          iteration: this.iteration,
          action: {
            type: 'reason',
            tokensUsed: 0, // Updated by LMReasoning
            knowledgeGained: knowledgeItems.length,
          },
          tokensUsed: 0,
          knowledgeGained: knowledgeItems.length,
          timestamp: Date.now(),
        });
        
        // Evaluate if answer is definitive
        if (await this.isAnswerDefinitive()) {
          console.log('✅ Definitive answer found');
          break;
        }
        
        this.iteration++;
      } catch (error) {
        console.error(`❌ Error in iteration ${this.iteration}:`, error);
        // Continue to next iteration on non-fatal errors
        this.iteration++;
      }
    }
    
    return this.generateFinalReport();
  }
  
  /**
   * Initialize research session
   */
  protected initialize(): void {
    this.iteration = 0;
    this.startTime = Date.now();
    this.definitiveAnswer = null;
    
    console.log(`🚀 Starting research: "${this.config.query}"`);
    console.log(`   Max iterations: ${this.config.maxIterations}`);
    console.log(`   Token budget: ${this.config.tokenBudget}`);
  }
  
  /**
   * Check if research should stop
   * 
   * Stopping conditions:
   * 1. Max iterations reached
   * 2. Token budget exceeded
   * 3. Definitive answer found
   */
  protected shouldStop(): boolean {
    // Max iterations
    if (this.iteration >= this.config.maxIterations!) {
      console.log('⏹️  Max iterations reached');
      return true;
    }
    
    // Token budget exceeded
    if (this.tokenTracker.isExceeded()) {
      console.log('⏹️  Token budget exceeded');
      return true;
    }
    
    // Definitive answer found
    if (this.definitiveAnswer !== null) {
      return true;
    }
    
    return false;
  }
  
  /**
   * Hook: Generate reflective questions
   * Override in subclass or use LMReasoning
   */
  protected async generateQuestions(): Promise<ReflectiveQuestion[]> {
    // Default implementation: return initial query as question
    return [
      {
        question: this.config.query,
        reason: 'Initial research question',
        priority: 5,
      },
    ];
  }
  
  /**
   * Hook: Search for information
   * Override in subclass or use SearchProviderFactory
   */
  protected async search(_questions: ReflectiveQuestion[]): Promise<SearchResult[]> {
    // Default implementation: return empty results
    // Will be implemented in TSK-DR-006 (SearchProviderFactory)
    console.log('⚠️  search() not implemented yet, returning empty results');
    return [];
  }
  
  /**
   * Hook: Read web contents
   * Override in subclass or use JinaProvider
   */
  protected async read(_results: SearchResult[]): Promise<WebContent[]> {
    // Default implementation: return empty contents
    // Will be implemented in TSK-DR-007 (JinaProvider)
    console.log('⚠️  read() not implemented yet, returning empty contents');
    return [];
  }
  
  /**
   * Hook: Reason and extract knowledge
   * Override in subclass or use LMReasoning
   */
  protected async reason(contents: WebContent[]): Promise<KnowledgeItem[]> {
    // Default implementation: extract basic knowledge
    const knowledgeItems: KnowledgeItem[] = [];
    
    for (const content of contents) {
      for (const fact of content.extractedFacts) {
        knowledgeItems.push({
          type: 'fact',
          content: fact,
          sources: [content.url],
          relevance: 0.7,
          iteration: this.iteration,
          timestamp: Date.now(),
        });
      }
    }
    
    return knowledgeItems;
  }
  
  /**
   * Check if answer is definitive
   * Override in subclass or use LMReasoning
   */
  protected async isAnswerDefinitive(): Promise<boolean> {
    // Default implementation: check knowledge count
    // Will be enhanced with LM reasoning in TSK-DR-010
    const knowledgeCount = this.knowledge.size();
    
    // Consider answer definitive if we have 10+ knowledge items
    if (knowledgeCount >= 10) {
      this.definitiveAnswer = this.knowledge.getSummary(5);
      return true;
    }
    
    return false;
  }
  
  /**
   * Generate final research report
   */
  protected async generateFinalReport(): Promise<ResearchReport> {
    const durationMs = Date.now() - this.startTime;
    const totalTokens = this.tokenTracker.getUsed();
    
    console.log(`\n📊 Research completed in ${(durationMs / 1000).toFixed(2)}s`);
    console.log(`   Iterations: ${this.iteration}`);
    console.log(`   Tokens used: ${totalTokens}/${this.config.tokenBudget}`);
    console.log(`   Knowledge items: ${this.knowledge.size()}`);
    
    const report = await this.reportGenerator.generate(
      this.config.query,
      this.knowledge,
      this.logger.getLogs(),
      {
        totalTokens,
        durationMs,
        iterations: this.iteration,
      }
    );
    
    return report;
  }
  
  /**
   * Validate configuration
   */
  private validateConfig(config: ResearchConfig): void {
    if (!config.query || config.query.trim().length === 0) {
      throw new InvalidConfigurationError('Query is required');
    }
    
    if (config.maxIterations !== undefined && config.maxIterations <= 0) {
      throw new InvalidConfigurationError('maxIterations must be positive');
    }
    
    if (config.tokenBudget !== undefined && config.tokenBudget <= 0) {
      throw new InvalidConfigurationError('tokenBudget must be positive');
    }
  }
  
  /**
   * Get current knowledge base (for testing)
   */
  getKnowledge(): KnowledgeBase {
    return this.knowledge;
  }
  
  /**
   * Get token tracker (for testing)
   */
  getTokenTracker(): TokenTracker {
    return this.tokenTracker;
  }
  
  /**
   * Get trajectory logger (for testing)
   */
  getLogger(): TrajectoryLogger {
    return this.logger;
  }
}
