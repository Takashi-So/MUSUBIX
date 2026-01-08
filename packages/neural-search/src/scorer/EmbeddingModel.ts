/**
 * Embedding Model
 * @module @nahisaho/musubix-neural-search
 * @description Neural embedding model for code and specifications
 * Traces to: REQ-NS-001 (分岐スコアリング)
 */

import type { Embedding, EmbeddingConfig, IEmbeddingModel } from '../types.js';
import { EmbeddingError } from '../errors.js';

/**
 * Default embedding configuration
 */
const DEFAULT_CONFIG: EmbeddingConfig = {
  modelName: 'simple-hash',
  dimension: 128,
  maxLength: 512,
  poolingStrategy: 'mean',
};

/**
 * Simple hash-based embedding model (for testing without ML dependencies)
 */
export class EmbeddingModel implements IEmbeddingModel {
  private readonly config: EmbeddingConfig;

  constructor(config: Partial<EmbeddingConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Embed source code
   */
  async embedCode(code: string): Promise<Embedding> {
    if (!code) {
      throw new EmbeddingError('Code cannot be empty');
    }
    return this.hashEmbed(code, 'code');
  }

  /**
   * Embed specification
   */
  async embedSpec(spec: string): Promise<Embedding> {
    if (!spec) {
      throw new EmbeddingError('Specification cannot be empty');
    }
    return this.hashEmbed(spec, 'spec');
  }

  /**
   * Calculate cosine similarity between embeddings
   */
  similarity(a: Embedding, b: Embedding): number {
    if (a.length !== b.length) {
      throw new EmbeddingError('Embedding dimensions must match');
    }

    let dotProduct = 0;
    let normA = 0;
    let normB = 0;

    for (let i = 0; i < a.length; i++) {
      const valA = a[i];
      const valB = b[i];
      dotProduct += valA * valB;
      normA += valA * valA;
      normB += valB * valB;
    }

    const denominator = Math.sqrt(normA) * Math.sqrt(normB);
    if (denominator === 0) {
      return 0;
    }

    return dotProduct / denominator;
  }

  /**
   * Batch embed multiple texts
   */
  async embedBatch(texts: string[]): Promise<Embedding[]> {
    return Promise.all(texts.map((text) => this.hashEmbed(text, 'batch')));
  }

  /**
   * Get configuration
   */
  getConfig(): EmbeddingConfig {
    return this.config;
  }

  /**
   * Simple hash-based embedding (deterministic, for testing)
   */
  private hashEmbed(text: string, prefix: string): Embedding {
    const combined = `${prefix}:${text}`;
    const embedding = new Float32Array(this.config.dimension);

    // Simple character-based hashing
    for (let i = 0; i < combined.length && i < this.config.maxLength; i++) {
      const charCode = combined.charCodeAt(i);
      const idx = i % this.config.dimension;
      embedding[idx] += charCode / 256;
    }

    // Normalize
    let norm = 0;
    for (let i = 0; i < embedding.length; i++) {
      norm += embedding[i] * embedding[i];
    }
    norm = Math.sqrt(norm);

    if (norm > 0) {
      for (let i = 0; i < embedding.length; i++) {
        embedding[i] /= norm;
      }
    }

    return embedding;
  }
}
