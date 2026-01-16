// LM-based Reasoning
// TSK-DR-010
// REQ: REQ-DR-CORE-004, REQ-DR-CORE-009
// ADR: ADR-v3.4.0-003

import type {
  KnowledgeItem,
  ReflectiveQuestion,
  ResearchContext,
} from '../types/index.js';

/**
 * LM Provider Interface
 * 
 * Abstract interface for language model providers.
 * Concrete implementations: VSCodeLMProvider, ExpertIntegration
 */
export interface LMProvider {
  /** Provider name */
  name: string;
  
  /**
   * Generate text completion
   * 
   * @param prompt - Input prompt
   * @param options - Generation options
   * @returns Generated text
   */
  generate(prompt: string, options?: LMGenerationOptions): Promise<string>;
  
  /**
   * Check if provider is available
   */
  isAvailable(): Promise<boolean>;
}

/**
 * LM Generation Options
 */
export interface LMGenerationOptions {
  /** Maximum tokens to generate */
  maxTokens?: number;
  /** Temperature (0-1, higher = more random) */
  temperature?: number;
  /** Stop sequences */
  stop?: string[];
  /** System prompt */
  systemPrompt?: string;
}

/**
 * LM-based Reasoning
 * 
 * Uses language models for reasoning tasks:
 * - Generate reflective questions
 * - Evaluate answer definitiveness
 * - Convert knowledge to EARS format
 * 
 * REQ: REQ-DR-CORE-004 - Reasoning with LM
 * REQ: REQ-DR-CORE-009 - Reflective questioning
 * ADR: ADR-v3.4.0-003 - Use LM API
 */
export class LMReasoning {
  private readonly provider: LMProvider;
  private readonly maxQuestions: number;
  
  constructor(provider: LMProvider, maxQuestions: number = 5) {
    this.provider = provider;
    this.maxQuestions = maxQuestions;
  }
  
  /**
   * Generate reflective questions based on current knowledge
   * 
   * REQ: REQ-DR-CORE-009
   */
  async generateQuestions(context: ResearchContext): Promise<ReflectiveQuestion[]> {
    console.log(`🤔 Generating questions (iteration ${context.iteration})...`);
    
    const prompt = this.buildQuestionPrompt(context);
    
    const response = await this.provider.generate(prompt, {
      maxTokens: 500,
      temperature: 0.7,
      systemPrompt: 'You are a research assistant helping to identify knowledge gaps.',
    });
    
    const questions = this.parseQuestions(response);
    
    console.log(`✅ Generated ${questions.length} questions`);
    
    return questions;
  }
  
  /**
   * Evaluate if current answer is definitive
   * 
   * REQ: REQ-DR-CORE-004
   */
  async evaluateAnswer(
    originalQuery: string,
    knowledgeItems: KnowledgeItem[]
  ): Promise<{ isDefinitive: boolean; confidence: number; reasoning: string }> {
    console.log(`📊 Evaluating answer definitiveness...`);
    
    const prompt = this.buildEvaluationPrompt(originalQuery, knowledgeItems);
    
    const response = await this.provider.generate(prompt, {
      maxTokens: 300,
      temperature: 0.3,
      systemPrompt: 'You are an expert at evaluating research completeness.',
    });
    
    const evaluation = this.parseEvaluation(response);
    
    console.log(`✅ Answer is ${evaluation.isDefinitive ? 'definitive' : 'incomplete'} (confidence: ${evaluation.confidence})`);
    
    return evaluation;
  }
  
  /**
   * Convert knowledge items to EARS format requirements
   * 
   * REQ: REQ-DR-CORE-004
   */
  async convertToEARS(knowledgeItems: KnowledgeItem[]): Promise<string[]> {
    console.log(`📝 Converting ${knowledgeItems.length} knowledge items to EARS...`);
    
    const earsRequirements: string[] = [];
    
    // Process in batches to avoid overwhelming the LM
    const batchSize = 5;
    for (let i = 0; i < knowledgeItems.length; i += batchSize) {
      const batch = knowledgeItems.slice(i, i + batchSize);
      const prompt = this.buildEARSPrompt(batch);
      
      const response = await this.provider.generate(prompt, {
        maxTokens: 800,
        temperature: 0.5,
        systemPrompt: 'You are an expert in EARS (Easy Approach to Requirements Syntax) format.',
      });
      
      const ears = this.parseEARS(response);
      earsRequirements.push(...ears);
    }
    
    console.log(`✅ Generated ${earsRequirements.length} EARS requirements`);
    
    return earsRequirements;
  }
  
  /**
   * Build prompt for question generation
   */
  private buildQuestionPrompt(context: ResearchContext): string {
    const knowledgeSummary = context.knowledgeBase
      .slice(0, 10)
      .map((item: KnowledgeItem, i: number) => `${i + 1}. ${item.content}`)
      .join('\n');
    
    return `Research Query: ${context.query}
Iteration: ${context.iteration}/${context.maxIterations}

Current Knowledge:
${knowledgeSummary}

Based on the above knowledge, generate ${this.maxQuestions} reflective questions to deepen understanding.
Each question should:
1. Identify a knowledge gap
2. Be specific and actionable
3. Build on existing knowledge

Format: JSON array of objects with "question", "reason", and "priority" (1-5).

Example:
[
  {
    "question": "What are the performance implications?",
    "reason": "Performance not yet analyzed",
    "priority": 4
  }
]

Output:`;
  }
  
  /**
   * Build prompt for answer evaluation
   */
  private buildEvaluationPrompt(query: string, knowledgeItems: KnowledgeItem[]): string {
    const knowledge = knowledgeItems
      .slice(0, 15)
      .map((item, i) => `${i + 1}. [${item.type}] ${item.content}`)
      .join('\n');
    
    return `Original Query: ${query}

Gathered Knowledge:
${knowledge}

Evaluate if this knowledge sufficiently answers the query.

Respond in JSON format:
{
  "isDefinitive": true/false,
  "confidence": 0.0-1.0,
  "reasoning": "explanation"
}

Output:`;
  }
  
  /**
   * Build prompt for EARS conversion
   */
  private buildEARSPrompt(knowledgeItems: KnowledgeItem[]): string {
    const items = knowledgeItems
      .map((item, i) => `${i + 1}. [${item.type}] ${item.content}`)
      .join('\n');
    
    return `Convert the following knowledge items to EARS format requirements.

EARS Patterns:
- Ubiquitous: "THE [system] SHALL [requirement]"
- Event-driven: "WHEN [event], THE [system] SHALL [response]"
- State-driven: "WHILE [state], THE [system] SHALL [response]"
- Unwanted: "THE [system] SHALL NOT [behavior]"
- Optional: "IF [condition], THEN THE [system] SHALL [response]"

Knowledge Items:
${items}

Output each EARS requirement on a new line:`;
  }
  
  /**
   * Parse questions from LM response
   */
  private parseQuestions(response: string): ReflectiveQuestion[] {
    try {
      // Try to extract JSON from response
      const jsonMatch = response.match(/\[[\s\S]*\]/);
      if (!jsonMatch) {
        console.warn('⚠️  No JSON array found in response');
        return [];
      }
      
      const parsed = JSON.parse(jsonMatch[0]);
      
      if (!Array.isArray(parsed)) {
        console.warn('⚠️  Response is not an array');
        return [];
      }
      
      return parsed
        .filter(q => q.question && q.reason && typeof q.priority === 'number')
        .slice(0, this.maxQuestions)
        .map(q => ({
          question: q.question,
          reason: q.reason,
          priority: Math.max(1, Math.min(5, q.priority)),
        }));
    } catch (error) {
      console.error('❌ Failed to parse questions:', error);
      return [];
    }
  }
  
  /**
   * Parse evaluation from LM response
   */
  private parseEvaluation(response: string): {
    isDefinitive: boolean;
    confidence: number;
    reasoning: string;
  } {
    try {
      // Try to extract JSON from response
      const jsonMatch = response.match(/\{[\s\S]*\}/);
      if (!jsonMatch) {
        console.warn('⚠️  No JSON object found in response');
        return {
          isDefinitive: false,
          confidence: 0.5,
          reasoning: 'Could not parse evaluation',
        };
      }
      
      const parsed = JSON.parse(jsonMatch[0]);
      
      return {
        isDefinitive: !!parsed.isDefinitive,
        confidence: Math.max(0, Math.min(1, parsed.confidence || 0.5)),
        reasoning: parsed.reasoning || 'No reasoning provided',
      };
    } catch (error) {
      console.error('❌ Failed to parse evaluation:', error);
      return {
        isDefinitive: false,
        confidence: 0.5,
        reasoning: 'Parse error',
      };
    }
  }
  
  /**
   * Parse EARS requirements from LM response
   */
  private parseEARS(response: string): string[] {
    // Split by newlines and filter EARS-like statements
    const lines = response
      .split('\n')
      .map(line => line.trim())
      .filter(line => line.length > 0)
      .filter(line => {
        // Check if line contains EARS keywords
        const earsKeywords = ['SHALL', 'WHEN', 'WHILE', 'IF', 'THEN'];
        return earsKeywords.some(keyword => line.includes(keyword));
      });
    
    return lines;
  }
}

/**
 * Create an LM reasoning instance
 */
export function createLMReasoning(
  provider: LMProvider,
  maxQuestions?: number
): LMReasoning {
  return new LMReasoning(provider, maxQuestions);
}
