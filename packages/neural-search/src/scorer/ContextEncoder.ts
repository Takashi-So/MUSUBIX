/**
 * Context Encoder
 * @module @nahisaho/musubix-neural-search
 * @description Encodes search context into embeddings
 */

import type {
  ContextFeatures,
  EncodedContext,
  IContextEncoder,
  IEmbeddingModel,
  SearchContext,
} from '../types.js';
import { EmbeddingModel } from './EmbeddingModel.js';

/**
 * Context encoder implementation
 */
export class ContextEncoder implements IContextEncoder {
  private readonly embeddingModel: IEmbeddingModel;
  private patterns: Set<string>;

  constructor(embeddingModel?: IEmbeddingModel) {
    this.embeddingModel = embeddingModel ?? new EmbeddingModel();
    this.patterns = new Set();
  }

  /**
   * Encode full search context
   */
  async encode(context: SearchContext): Promise<EncodedContext> {
    // Combine specification with constraints
    const combined = this.combineContextElements(context);
    const embedding = await this.embeddingModel.embedSpec(combined);
    const features = this.extractFeatures(context);

    return {
      embedding,
      features,
      tokens: this.estimateTokens(combined),
    };
  }

  /**
   * Encode specification only
   */
  async encodeSpec(spec: string): Promise<EncodedContext> {
    const embedding = await this.embeddingModel.embedSpec(spec);
    const features = this.extractSpecFeatures(spec);

    return {
      embedding,
      features,
      tokens: this.estimateTokens(spec),
    };
  }

  /**
   * Update encoder with learned patterns
   */
  updatePatterns(patterns: string[]): void {
    patterns.forEach((p) => this.patterns.add(p));
  }

  /**
   * Get learned patterns
   */
  getPatterns(): string[] {
    return Array.from(this.patterns);
  }

  /**
   * Combine context elements into a single string
   */
  private combineContextElements(context: SearchContext): string {
    const parts: string[] = [context.specification];

    if (context.constraints.length > 0) {
      parts.push(`Constraints: ${context.constraints.join(', ')}`);
    }

    if (context.history.length > 0) {
      const lastState = context.history[context.history.length - 1];
      parts.push(`Current state: ${lastState.code.substring(0, 100)}`);
    }

    return parts.join('\n');
  }

  /**
   * Extract features from full context
   */
  private extractFeatures(context: SearchContext): ContextFeatures {
    return {
      specLength: context.specification.length,
      constraintCount: context.constraints.length,
      complexityEstimate: this.estimateComplexity(context),
      domainSignals: this.extractDomainSignals(context.specification),
    };
  }

  /**
   * Extract features from specification only
   */
  private extractSpecFeatures(spec: string): ContextFeatures {
    return {
      specLength: spec.length,
      constraintCount: 0,
      complexityEstimate: this.estimateSpecComplexity(spec),
      domainSignals: this.extractDomainSignals(spec),
    };
  }

  /**
   * Estimate complexity of the context
   */
  private estimateComplexity(context: SearchContext): number {
    let complexity = context.specification.length / 100;
    complexity += context.constraints.length * 0.5;
    complexity += context.history.length * 0.2;
    return Math.min(10, complexity);
  }

  /**
   * Estimate complexity of specification
   */
  private estimateSpecComplexity(spec: string): number {
    const words = spec.split(/\s+/).length;
    const sentences = spec.split(/[.!?]+/).length;
    return Math.min(10, words / 50 + sentences / 5);
  }

  /**
   * Extract domain signals from text
   */
  private extractDomainSignals(text: string): string[] {
    const signals: string[] = [];
    const lowerText = text.toLowerCase();

    // Programming domain signals
    if (lowerText.includes('function') || lowerText.includes('method')) {
      signals.push('function');
    }
    if (lowerText.includes('class') || lowerText.includes('interface')) {
      signals.push('oop');
    }
    if (lowerText.includes('async') || lowerText.includes('await')) {
      signals.push('async');
    }
    if (lowerText.includes('test') || lowerText.includes('spec')) {
      signals.push('testing');
    }
    if (lowerText.includes('api') || lowerText.includes('endpoint')) {
      signals.push('api');
    }
    if (lowerText.includes('database') || lowerText.includes('query')) {
      signals.push('database');
    }

    // Check for learned patterns
    this.patterns.forEach((pattern) => {
      if (lowerText.includes(pattern.toLowerCase())) {
        signals.push(`pattern:${pattern}`);
      }
    });

    return signals;
  }

  /**
   * Estimate token count
   */
  private estimateTokens(text: string): number {
    // Rough estimate: ~4 characters per token
    return Math.ceil(text.length / 4);
  }
}
