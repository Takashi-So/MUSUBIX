/**
 * ModalFusion - Multi-modal Embedding Fusion
 * @module @nahisaho/musubix-neural-search
 * @see TSK-NS-106
 * @see DES-NS-106
 * @see REQ-NS-106 Text/code embedding fusion with 3+ strategies
 */

import type { Embedding } from '../types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Fusion strategy types
 */
export type FusionStrategy = 'concat' | 'attention' | 'weighted_sum';

/**
 * ModalFusion configuration
 */
export interface ModalFusionConfig {
  /** Default fusion strategy */
  defaultStrategy: FusionStrategy;
  /** Weight for text embedding (0-1) */
  textWeight: number;
  /** Weight for code embedding (0-1) */
  codeWeight: number;
  /** Attention temperature for softmax */
  attentionTemperature: number;
}

/**
 * Embedding pair for batch operations
 */
export interface EmbeddingPair {
  text: Embedding;
  code: Embedding;
}

/**
 * ModalFusion interface
 */
export interface ModalFusion {
  /**
   * Fuse text and code embeddings
   */
  fuse(
    textEmbedding: Embedding,
    codeEmbedding: Embedding,
    strategy?: FusionStrategy
  ): Embedding;

  /**
   * Fuse multiple embedding pairs
   */
  fuseBatch(pairs: EmbeddingPair[], strategy?: FusionStrategy): Embedding[];

  /**
   * Get available fusion strategies
   */
  getAvailableStrategies(): FusionStrategy[];

  /**
   * Get current configuration
   */
  getConfig(): ModalFusionConfig;

  /**
   * Serialize to JSON
   */
  toJSON(): string;

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void;
}

// ============================================================================
// Default Implementation
// ============================================================================

/**
 * Default ModalFusion implementation
 */
export class DefaultModalFusion implements ModalFusion {
  private config: ModalFusionConfig;

  constructor(config?: Partial<ModalFusionConfig>) {
    this.config = {
      defaultStrategy: config?.defaultStrategy ?? 'weighted_sum',
      textWeight: config?.textWeight ?? 0.5,
      codeWeight: config?.codeWeight ?? 0.5,
      attentionTemperature: config?.attentionTemperature ?? 1.0,
    };
  }

  /**
   * Fuse text and code embeddings using specified strategy
   */
  fuse(
    textEmbedding: Embedding,
    codeEmbedding: Embedding,
    strategy?: FusionStrategy
  ): Embedding {
    const fusionStrategy = strategy ?? this.config.defaultStrategy;

    switch (fusionStrategy) {
      case 'concat':
        return this.concatFusion(textEmbedding, codeEmbedding);
      case 'weighted_sum':
        return this.weightedSumFusion(textEmbedding, codeEmbedding);
      case 'attention':
        return this.attentionFusion(textEmbedding, codeEmbedding);
      default:
        return this.weightedSumFusion(textEmbedding, codeEmbedding);
    }
  }

  /**
   * Concatenation fusion: [text; code]
   */
  private concatFusion(text: Embedding, code: Embedding): Embedding {
    return [...text, ...code];
  }

  /**
   * Weighted sum fusion: w1 * text + w2 * code
   */
  private weightedSumFusion(text: Embedding, code: Embedding): Embedding {
    const minLength = Math.min(text.length, code.length);
    const result: Embedding = [];

    for (let i = 0; i < minLength; i++) {
      result.push(
        this.config.textWeight * text[i] + this.config.codeWeight * code[i]
      );
    }

    return result;
  }

  /**
   * Attention-based fusion with learned weights
   */
  private attentionFusion(text: Embedding, code: Embedding): Embedding {
    const minLength = Math.min(text.length, code.length);
    const result: Embedding = [];

    // Compute attention scores based on element magnitudes
    for (let i = 0; i < minLength; i++) {
      const textMag = Math.abs(text[i]);
      const codeMag = Math.abs(code[i]);

      // Softmax-like attention with temperature
      const expText = Math.exp(textMag / this.config.attentionTemperature);
      const expCode = Math.exp(codeMag / this.config.attentionTemperature);
      const sumExp = expText + expCode;

      const textAttention = expText / sumExp;
      const codeAttention = expCode / sumExp;

      result.push(textAttention * text[i] + codeAttention * code[i]);
    }

    return result;
  }

  /**
   * Fuse multiple embedding pairs
   */
  fuseBatch(pairs: EmbeddingPair[], strategy?: FusionStrategy): Embedding[] {
    return pairs.map((pair) => this.fuse(pair.text, pair.code, strategy));
  }

  /**
   * Get available fusion strategies
   */
  getAvailableStrategies(): FusionStrategy[] {
    return ['concat', 'attention', 'weighted_sum'];
  }

  /**
   * Get current configuration
   */
  getConfig(): ModalFusionConfig {
    return { ...this.config };
  }

  /**
   * Serialize to JSON
   */
  toJSON(): string {
    return JSON.stringify({
      config: this.config,
    });
  }

  /**
   * Deserialize from JSON
   */
  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.config) {
      this.config = {
        ...this.config,
        ...data.config,
      };
    }
  }
}

// ============================================================================
// Factory Function
// ============================================================================

/**
 * Create a ModalFusion instance
 * @param config - Optional configuration
 * @returns ModalFusion instance
 */
export function createModalFusion(
  config?: Partial<ModalFusionConfig>
): ModalFusion {
  return new DefaultModalFusion(config);
}
