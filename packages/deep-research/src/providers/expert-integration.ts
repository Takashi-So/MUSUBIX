// Expert Delegation Integration
// TSK-DR-012
// REQ: REQ-DR-CORE-004
// ADR: ADR-v3.4.0-003

import type { LMProvider, LMGenerationOptions } from '../reasoning/lm-reasoning.js';

/**
 * Expert Delegation Integration
 * 
 * Wrapper for @nahisaho/musubix-expert-delegation package.
 * Delegates complex reasoning tasks to specialized AI experts.
 * 
 * Features:
 * - 7 specialized experts (Software Architect, Security Analyst, etc.)
 * - Automatic expert selection based on task type
 * - Confidence-based routing
 * - Fallback to general expert
 * 
 * REQ: REQ-DR-CORE-004 - Advanced reasoning
 * ADR: ADR-v3.4.0-003 - Expert delegation for complex tasks
 */
export class ExpertIntegration implements LMProvider {
  name = 'Expert Delegation';
  
  private readonly timeout: number;
  private readonly expertSelector: (prompt: string) => string;
  
  /**
   * Available expert types
   */
  static readonly EXPERTS = {
    SOFTWARE_ARCHITECT: 'software-architect',
    SECURITY_ANALYST: 'security-analyst',
    PERFORMANCE_ENGINEER: 'performance-engineer',
    CODE_REVIEWER: 'code-reviewer',
    TECHNICAL_WRITER: 'technical-writer',
    DATABASE_SPECIALIST: 'database-specialist',
    DEVOPS_ENGINEER: 'devops-engineer',
  } as const;
  
  constructor(
    timeout: number = 30000,
    expertSelector?: (prompt: string) => string
  ) {
    this.timeout = timeout;
    this.expertSelector = expertSelector || this.defaultExpertSelector.bind(this);
  }
  
  /**
   * Generate text using expert delegation
   */
  async generate(prompt: string, options?: LMGenerationOptions): Promise<string> {
    console.log(`🎯 Consulting experts...`);
    
    try {
      // Select appropriate expert
      const expertType = this.expertSelector(prompt);
      console.log(`👨‍💼 Selected expert: ${expertType}`);
      
      // Check if expert-delegation package is available
      const expertDelegation = await this.loadExpertDelegation();
      
      if (!expertDelegation) {
        throw new Error('Expert delegation package not available');
      }
      
      // Consult expert
      const result = await expertDelegation.consult({
        expertType,
        query: prompt,
        systemPrompt: options?.systemPrompt,
        maxTokens: options?.maxTokens || 1000,
        temperature: options?.temperature || 0.7,
        timeout: this.timeout,
      });
      
      console.log(`✅ Expert consultation complete (confidence: ${result.confidence})`);
      
      return result.response;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`❌ Expert consultation failed:`, err.message);
      throw err;
    }
  }
  
  /**
   * Check if expert delegation is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      const expertDelegation = await this.loadExpertDelegation();
      return expertDelegation !== null;
    } catch (error) {
      console.warn('⚠️  Expert delegation availability check failed:', error);
      return false;
    }
  }
  
  /**
   * Default expert selector (keyword-based)
   */
  private defaultExpertSelector(prompt: string): string {
    const lower = prompt.toLowerCase();
    
    // Security-related
    if (lower.includes('security') || lower.includes('vulnerability') || lower.includes('authentication')) {
      return ExpertIntegration.EXPERTS.SECURITY_ANALYST;
    }
    
    // Performance-related (check before database to catch "optimize database")
    if (lower.includes('performance') || lower.includes('optimization') || lower.includes('optimize') || lower.includes('scalability')) {
      return ExpertIntegration.EXPERTS.PERFORMANCE_ENGINEER;
    }
    
    // Database-related
    if (lower.includes('database') || lower.includes('query') || lower.includes('sql')) {
      return ExpertIntegration.EXPERTS.DATABASE_SPECIALIST;
    }
    
    // DevOps-related
    if (lower.includes('deployment') || lower.includes('ci/cd') || lower.includes('infrastructure')) {
      return ExpertIntegration.EXPERTS.DEVOPS_ENGINEER;
    }
    
    // Code review
    if (lower.includes('review') || lower.includes('refactor') || lower.includes('best practice')) {
      return ExpertIntegration.EXPERTS.CODE_REVIEWER;
    }
    
    // Documentation
    if (lower.includes('documentation') || lower.includes('explain') || lower.includes('describe')) {
      return ExpertIntegration.EXPERTS.TECHNICAL_WRITER;
    }
    
    // Default to software architect
    return ExpertIntegration.EXPERTS.SOFTWARE_ARCHITECT;
  }
  
  /**
   * Load expert-delegation package dynamically
   */
  private async loadExpertDelegation(): Promise<any> {
    try {
      // Try to import the package (dynamic import, may not be installed)
      const module = await import('@nahisaho/musubix-expert-delegation' as any);
      return module.default || module;
    } catch (error) {
      // Package not installed or not available
      console.warn('⚠️  @nahisaho/musubix-expert-delegation not available');
      return null;
    }
  }
}

/**
 * Create an expert integration instance
 */
export function createExpertIntegration(
  timeout?: number,
  expertSelector?: (prompt: string) => string
): ExpertIntegration {
  return new ExpertIntegration(timeout, expertSelector);
}
