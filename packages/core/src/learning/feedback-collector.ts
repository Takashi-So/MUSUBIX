/**
 * Feedback Collector
 *
 * Collects and stores user feedback on generated artifacts
 *
 * @see REQ-LEARN-001 - Feedback Collection
 * @module @musubix/core/learning
 */

import { randomUUID } from 'crypto';
import { promises as fs } from 'fs';
import { join, dirname } from 'path';
import type {
  Feedback,
  FeedbackType,
  ArtifactType,
  FeedbackContext,
  LearningConfig,
} from './types.js';

/**
 * Feedback input for creating new feedback
 */
export interface FeedbackInput {
  type: FeedbackType;
  artifactType: ArtifactType;
  artifactId: string;
  context?: Partial<FeedbackContext>;
  reason?: string;
  original?: string;
  modified?: string;
}

/**
 * Feedback query options
 */
export interface FeedbackQuery {
  artifactType?: ArtifactType;
  type?: FeedbackType;
  project?: string;
  language?: string;
  framework?: string;
  since?: Date;
  limit?: number;
}

/**
 * Feedback Collector class
 *
 * Responsible for collecting, storing, and querying user feedback
 *
 * @see REQ-LEARN-001 - Feedback Collection
 * @see REQ-LEARN-006 - Privacy Protection (local storage only)
 */
export class FeedbackCollector {
  private feedbackCache: Map<string, Feedback> = new Map();
  private storagePath: string;
  private loaded: boolean = false;

  constructor(config: Partial<LearningConfig> = {}) {
    this.storagePath = config.storagePath || 'storage/learning';
  }

  /**
   * Record new feedback
   *
   * @see REQ-LEARN-001 - Feedback Collection
   * @param input - Feedback input data
   * @returns Created feedback with generated ID
   */
  async recordFeedback(input: FeedbackInput): Promise<Feedback> {
    await this.ensureLoaded();

    const feedback: Feedback = {
      id: `FB-${randomUUID().slice(0, 8).toUpperCase()}`,
      timestamp: new Date(),
      type: input.type,
      artifactType: input.artifactType,
      artifactId: input.artifactId,
      context: {
        project: input.context?.project || this.detectProject(),
        language: input.context?.language,
        framework: input.context?.framework,
        tags: input.context?.tags || [],
      },
      reason: input.reason,
      original: input.original,
      modified: input.modified,
    };

    // Sanitize feedback to remove sensitive data
    this.sanitizeFeedback(feedback);

    this.feedbackCache.set(feedback.id, feedback);
    await this.persist();

    return feedback;
  }

  /**
   * Get feedback by ID
   */
  async getFeedback(id: string): Promise<Feedback | undefined> {
    await this.ensureLoaded();
    return this.feedbackCache.get(id);
  }

  /**
   * Query feedback with filters
   */
  async queryFeedback(query: FeedbackQuery = {}): Promise<Feedback[]> {
    await this.ensureLoaded();

    let results = Array.from(this.feedbackCache.values());

    if (query.artifactType) {
      results = results.filter((f) => f.artifactType === query.artifactType);
    }
    if (query.type) {
      results = results.filter((f) => f.type === query.type);
    }
    if (query.project) {
      results = results.filter((f) => f.context.project === query.project);
    }
    if (query.language) {
      results = results.filter((f) => f.context.language === query.language);
    }
    if (query.framework) {
      results = results.filter((f) => f.context.framework === query.framework);
    }
    if (query.since) {
      results = results.filter((f) => f.timestamp >= query.since!);
    }

    // Sort by timestamp descending
    results.sort((a, b) => b.timestamp.getTime() - a.timestamp.getTime());

    if (query.limit) {
      results = results.slice(0, query.limit);
    }

    return results;
  }

  /**
   * Get feedback statistics
   */
  async getStats(): Promise<{
    total: number;
    byType: Record<FeedbackType, number>;
    byArtifactType: Record<ArtifactType, number>;
  }> {
    await this.ensureLoaded();

    const stats = {
      total: this.feedbackCache.size,
      byType: { accept: 0, reject: 0, modify: 0 } as Record<FeedbackType, number>,
      byArtifactType: { requirement: 0, design: 0, code: 0, test: 0 } as Record<
        ArtifactType,
        number
      >,
    };

    for (const feedback of this.feedbackCache.values()) {
      stats.byType[feedback.type]++;
      stats.byArtifactType[feedback.artifactType]++;
    }

    return stats;
  }

  /**
   * Delete feedback by ID
   */
  async deleteFeedback(id: string): Promise<boolean> {
    await this.ensureLoaded();
    const deleted = this.feedbackCache.delete(id);
    if (deleted) {
      await this.persist();
    }
    return deleted;
  }

  /**
   * Export all feedback
   */
  async export(): Promise<Feedback[]> {
    await this.ensureLoaded();
    return Array.from(this.feedbackCache.values());
  }

  /**
   * Import feedback from array
   */
  async import(feedbackList: Feedback[]): Promise<number> {
    await this.ensureLoaded();
    let imported = 0;
    for (const feedback of feedbackList) {
      if (!this.feedbackCache.has(feedback.id)) {
        this.feedbackCache.set(feedback.id, feedback);
        imported++;
      }
    }
    await this.persist();
    return imported;
  }

  /**
   * Clear all feedback
   */
  async clear(): Promise<void> {
    this.feedbackCache.clear();
    await this.persist();
  }

  /**
   * Sanitize feedback to remove sensitive data
   *
   * @see REQ-LEARN-006 - Privacy Protection
   */
  private sanitizeFeedback(feedback: Feedback): void {
    // Remove potential sensitive patterns
    const sensitivePatterns = [
      /password\s*[:=]\s*["']?[^"'\s]+["']?/gi,
      /api[_-]?key\s*[:=]\s*["']?[^"'\s]+["']?/gi,
      /secret\s*[:=]\s*["']?[^"'\s]+["']?/gi,
      /token\s*[:=]\s*["']?[^"'\s]+["']?/gi,
      /\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b/g, // emails
    ];

    const sanitize = (text: string | undefined): string | undefined => {
      if (!text) return text;
      let result = text;
      for (const pattern of sensitivePatterns) {
        result = result.replace(pattern, '[REDACTED]');
      }
      return result;
    };

    feedback.reason = sanitize(feedback.reason);
    feedback.original = sanitize(feedback.original);
    feedback.modified = sanitize(feedback.modified);
  }

  /**
   * Detect current project name
   */
  private detectProject(): string {
    // Try to detect from package.json or current directory
    try {
      const cwd = process.cwd();
      return cwd.split('/').pop() || 'unknown';
    } catch {
      return 'unknown';
    }
  }

  /**
   * Ensure data is loaded from storage
   */
  private async ensureLoaded(): Promise<void> {
    if (this.loaded) return;

    const filePath = join(this.storagePath, 'feedback.json');
    try {
      const data = await fs.readFile(filePath, 'utf-8');
      const feedbackList: Feedback[] = JSON.parse(data);
      for (const feedback of feedbackList) {
        // Convert date strings back to Date objects
        feedback.timestamp = new Date(feedback.timestamp);
        this.feedbackCache.set(feedback.id, feedback);
      }
    } catch {
      // File doesn't exist yet, start fresh
    }
    this.loaded = true;
  }

  /**
   * Persist data to storage
   *
   * @see REQ-LEARN-006 - Local storage only
   */
  private async persist(): Promise<void> {
    const filePath = join(this.storagePath, 'feedback.json');
    const dir = dirname(filePath);

    try {
      await fs.mkdir(dir, { recursive: true });
    } catch {
      // Directory exists
    }

    const feedbackList = Array.from(this.feedbackCache.values());
    await fs.writeFile(filePath, JSON.stringify(feedbackList, null, 2), 'utf-8');
  }
}
