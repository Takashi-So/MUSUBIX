/**
 * Pattern Extractor
 *
 * Extracts patterns from accumulated feedback
 *
 * @see REQ-LEARN-002 - Pattern Extraction
 * @module @musubix/core/learning
 */

import { randomUUID } from 'crypto';
import { promises as fs } from 'fs';
import { join, dirname } from 'path';
import type {
  Feedback,
  LearnedPattern,
  PatternCategory,
  PatternActionType,
  PatternTrigger,
  PatternAction,
  LearningConfig,
} from './types.js';

/**
 * Pattern candidate detected from feedback
 */
interface PatternCandidate {
  key: string;
  category: PatternCategory;
  context: Record<string, string>;
  actionType: PatternActionType;
  content: string;
  occurrences: number;
  feedbackIds: string[];
}

/**
 * Pattern Extractor class
 *
 * Analyzes feedback to extract recurring patterns
 *
 * @see REQ-LEARN-002 - Pattern Extraction
 */
export class PatternExtractor {
  private patternCache: Map<string, LearnedPattern> = new Map();
  private storagePath: string;
  private threshold: number;
  private loaded: boolean = false;

  constructor(config: Partial<LearningConfig> = {}) {
    this.storagePath = config.storagePath || 'storage/learning';
    this.threshold = config.patternThreshold || 3;
  }

  /**
   * Extract patterns from feedback list
   *
   * @see REQ-LEARN-002 - Pattern Extraction
   * @param feedbackList - List of feedback to analyze
   * @returns Newly created patterns
   */
  async extractPatterns(feedbackList: Feedback[]): Promise<LearnedPattern[]> {
    await this.ensureLoaded();

    // Group feedback by similarity
    const candidates = this.findCandidates(feedbackList);

    // Create patterns from candidates that meet threshold
    const newPatterns: LearnedPattern[] = [];
    for (const candidate of candidates) {
      if (candidate.occurrences >= this.threshold) {
        const existing = this.findSimilarPattern(candidate);
        if (existing) {
          // Update existing pattern
          existing.occurrences += candidate.occurrences;
          existing.confidence = this.calculateConfidence(existing);
          existing.lastUsed = new Date();
        } else {
          // Create new pattern
          const pattern = this.createPattern(candidate);
          this.patternCache.set(pattern.id, pattern);
          newPatterns.push(pattern);
        }
      }
    }

    await this.persist();
    return newPatterns;
  }

  /**
   * Get all patterns
   */
  async getPatterns(): Promise<LearnedPattern[]> {
    await this.ensureLoaded();
    return Array.from(this.patternCache.values());
  }

  /**
   * Get pattern by ID
   */
  async getPattern(id: string): Promise<LearnedPattern | undefined> {
    await this.ensureLoaded();
    return this.patternCache.get(id);
  }

  /**
   * Add pattern manually
   *
   * @param name - Pattern name
   * @param category - Pattern category
   * @param trigger - Trigger conditions
   * @param action - Action to take
   * @param confidence - Initial confidence (default: 0.5)
   */
  async addPattern(
    name: string,
    category: PatternCategory,
    trigger: PatternTrigger,
    action: PatternAction,
    confidence: number = 0.5
  ): Promise<LearnedPattern> {
    await this.ensureLoaded();

    const pattern: LearnedPattern = {
      id: `PAT-${randomUUID().slice(0, 8).toUpperCase()}`,
      name,
      category,
      trigger,
      action,
      confidence: Math.max(0, Math.min(1, confidence)),
      occurrences: 1,
      lastUsed: new Date(),
      createdAt: new Date(),
      source: 'manual',
    };

    this.patternCache.set(pattern.id, pattern);
    await this.persist();

    return pattern;
  }

  /**
   * Remove pattern by ID
   */
  async removePattern(id: string): Promise<boolean> {
    await this.ensureLoaded();
    const deleted = this.patternCache.delete(id);
    if (deleted) {
      await this.persist();
    }
    return deleted;
  }

  /**
   * Update pattern confidence based on usage
   */
  async updatePatternUsage(
    id: string,
    success: boolean
  ): Promise<LearnedPattern | undefined> {
    await this.ensureLoaded();
    const pattern = this.patternCache.get(id);
    if (!pattern) return undefined;

    pattern.lastUsed = new Date();
    if (success) {
      pattern.occurrences++;
      pattern.confidence = Math.min(1, pattern.confidence + 0.05);
    } else {
      pattern.confidence = Math.max(0, pattern.confidence - 0.1);
    }

    await this.persist();
    return pattern;
  }

  /**
   * Apply decay to unused patterns
   *
   * @see REQ-LEARN-004 - Pattern Decay
   * @param days - Days threshold for decay
   * @param rate - Decay rate
   * @param minConfidence - Minimum confidence to keep
   */
  async applyDecay(
    days: number = 30,
    rate: number = 0.1,
    minConfidence: number = 0.1
  ): Promise<{ decayed: number; archived: number }> {
    await this.ensureLoaded();

    const now = new Date();
    const threshold = new Date(now.getTime() - days * 24 * 60 * 60 * 1000);
    let decayed = 0;
    let archived = 0;
    const toArchive: string[] = [];

    for (const pattern of this.patternCache.values()) {
      if (pattern.lastUsed < threshold) {
        pattern.confidence = Math.max(0, pattern.confidence - rate);
        decayed++;

        if (pattern.confidence < minConfidence) {
          toArchive.push(pattern.id);
          archived++;
        }
      }
    }

    // Archive patterns below threshold
    for (const id of toArchive) {
      await this.archivePattern(id);
      this.patternCache.delete(id);
    }

    await this.persist();
    return { decayed, archived };
  }

  /**
   * Get patterns by category
   */
  async getPatternsByCategory(
    category: PatternCategory
  ): Promise<LearnedPattern[]> {
    await this.ensureLoaded();
    return Array.from(this.patternCache.values()).filter(
      (p) => p.category === category
    );
  }

  /**
   * Get high confidence patterns
   */
  async getHighConfidencePatterns(
    threshold: number = 0.7
  ): Promise<LearnedPattern[]> {
    await this.ensureLoaded();
    return Array.from(this.patternCache.values())
      .filter((p) => p.confidence >= threshold)
      .sort((a, b) => b.confidence - a.confidence);
  }

  /**
   * Export patterns
   */
  async export(): Promise<LearnedPattern[]> {
    await this.ensureLoaded();
    return Array.from(this.patternCache.values());
  }

  /**
   * Import patterns
   */
  async import(patterns: LearnedPattern[]): Promise<number> {
    await this.ensureLoaded();
    let imported = 0;
    for (const pattern of patterns) {
      if (!this.patternCache.has(pattern.id)) {
        this.patternCache.set(pattern.id, pattern);
        imported++;
      }
    }
    await this.persist();
    return imported;
  }

  /**
   * Import patterns with merge strategy
   * @param patterns - Patterns to import
   * @param strategy - Merge strategy: 'skip', 'overwrite', 'merge'
   *   - skip: Keep existing, skip duplicates
   *   - overwrite: Replace existing with imported
   *   - merge: Combine occurrences, use max confidence
   */
  async importWithStrategy(
    patterns: LearnedPattern[],
    strategy: 'skip' | 'overwrite' | 'merge' = 'skip'
  ): Promise<{ imported: number; merged: number }> {
    await this.ensureLoaded();
    let imported = 0;
    let merged = 0;

    for (const pattern of patterns) {
      const existing = this.patternCache.get(pattern.id);

      if (!existing) {
        // New pattern - always import
        this.patternCache.set(pattern.id, pattern);
        imported++;
      } else {
        // Existing pattern - apply strategy
        switch (strategy) {
          case 'skip':
            // Keep existing, do nothing
            break;

          case 'overwrite':
            // Replace with imported
            this.patternCache.set(pattern.id, pattern);
            imported++;
            break;

          case 'merge':
            // Merge: combine occurrences, use max confidence, update lastUsed
            const mergedPattern: LearnedPattern = {
              ...existing,
              occurrences: existing.occurrences + pattern.occurrences,
              confidence: Math.max(existing.confidence, pattern.confidence),
              lastUsed: new Date(Math.max(
                new Date(existing.lastUsed).getTime(),
                new Date(pattern.lastUsed).getTime()
              )),
              // Merge action content if different
              action: {
                ...existing.action,
                content: existing.action.content === pattern.action.content
                  ? existing.action.content
                  : `${existing.action.content}\n---\n${pattern.action.content}`,
              },
            };
            this.patternCache.set(pattern.id, mergedPattern);
            merged++;
            break;
        }
      }
    }

    await this.persist();
    return { imported, merged };
  }

  /**
   * Find pattern candidates from feedback
   */
  private findCandidates(feedbackList: Feedback[]): PatternCandidate[] {
    const candidateMap = new Map<string, PatternCandidate>();

    for (const feedback of feedbackList) {
      // Generate candidate key based on context
      const key = this.generateCandidateKey(feedback);

      if (candidateMap.has(key)) {
        const candidate = candidateMap.get(key)!;
        candidate.occurrences++;
        candidate.feedbackIds.push(feedback.id);
      } else {
        candidateMap.set(key, {
          key,
          category: feedback.artifactType as PatternCategory,
          context: this.extractContext(feedback),
          actionType: this.mapFeedbackToAction(feedback.type),
          content: this.extractContent(feedback),
          occurrences: 1,
          feedbackIds: [feedback.id],
        });
      }
    }

    return Array.from(candidateMap.values());
  }

  /**
   * Generate a key for grouping similar feedback
   */
  private generateCandidateKey(feedback: Feedback): string {
    const parts = [
      feedback.artifactType,
      feedback.type,
      feedback.context.language || 'any',
      feedback.context.framework || 'any',
    ];
    return parts.join(':');
  }

  /**
   * Extract context from feedback
   */
  private extractContext(feedback: Feedback): Record<string, string> {
    const context: Record<string, string> = {};
    if (feedback.context.language) {
      context.language = feedback.context.language;
    }
    if (feedback.context.framework) {
      context.framework = feedback.context.framework;
    }
    return context;
  }

  /**
   * Map feedback type to pattern action
   */
  private mapFeedbackToAction(
    type: Feedback['type']
  ): PatternActionType {
    switch (type) {
      case 'accept':
        return 'prefer';
      case 'reject':
        return 'avoid';
      case 'modify':
        return 'suggest';
    }
  }

  /**
   * Extract content for pattern
   */
  private extractContent(feedback: Feedback): string {
    if (feedback.modified) {
      return feedback.modified;
    }
    if (feedback.reason) {
      return feedback.reason;
    }
    return `${feedback.type} ${feedback.artifactType}`;
  }

  /**
   * Find similar existing pattern
   */
  private findSimilarPattern(
    candidate: PatternCandidate
  ): LearnedPattern | undefined {
    for (const pattern of this.patternCache.values()) {
      if (
        pattern.category === candidate.category &&
        pattern.action.type === candidate.actionType &&
        this.contextMatches(pattern.trigger.context, candidate.context)
      ) {
        return pattern;
      }
    }
    return undefined;
  }

  /**
   * Check if contexts match
   */
  private contextMatches(
    a: Record<string, string>,
    b: Record<string, string>
  ): boolean {
    const keysA = Object.keys(a);
    const keysB = Object.keys(b);
    if (keysA.length !== keysB.length) return false;
    return keysA.every((key) => a[key] === b[key]);
  }

  /**
   * Create pattern from candidate
   */
  private createPattern(candidate: PatternCandidate): LearnedPattern {
    return {
      id: `PAT-${randomUUID().slice(0, 8).toUpperCase()}`,
      name: this.generateDescriptiveName(candidate),
      category: candidate.category,
      trigger: {
        context: candidate.context,
        conditions: [],
      },
      action: {
        type: candidate.actionType,
        content: candidate.content,
      },
      confidence: this.calculateInitialConfidence(candidate),
      occurrences: candidate.occurrences,
      lastUsed: new Date(),
      createdAt: new Date(),
      source: 'auto',
    };
  }

  /**
   * Generate a descriptive name for auto-extracted pattern
   * 
   * Example outputs:
   * - "TypeScript Code: Prefer async repository methods"
   * - "TypeScript Design: Avoid direct database access"
   * - "Code: Suggest using Input DTO pattern"
   */
  private generateDescriptiveName(candidate: PatternCandidate): string {
    const parts: string[] = [];
    
    // Add language if available
    if (candidate.context.language) {
      parts.push(candidate.context.language);
    }
    
    // Add framework if available
    if (candidate.context.framework) {
      parts.push(candidate.context.framework);
    }
    
    // Add category (capitalize first letter)
    const categoryStr = candidate.category.charAt(0).toUpperCase() + candidate.category.slice(1);
    parts.push(categoryStr);
    
    // Create context prefix
    const prefix = parts.join(' ');
    
    // Create action description
    const actionVerb = candidate.actionType === 'prefer' ? 'Prefer' :
                       candidate.actionType === 'avoid' ? 'Avoid' : 'Suggest';
    
    // Extract meaningful content summary (first 40 chars)
    const contentSummary = this.extractContentSummary(candidate.content);
    
    return `${prefix}: ${actionVerb} ${contentSummary}`;
  }
  
  /**
   * Extract a meaningful summary from pattern content
   */
  private extractContentSummary(content: string): string {
    // Remove code blocks
    let summary = content.replace(/```[\s\S]*?```/g, '');
    // Remove markdown formatting
    summary = summary.replace(/[*_#`]/g, '');
    // Remove multiple whitespace
    summary = summary.replace(/\s+/g, ' ').trim();
    // Take first meaningful part (up to 50 chars)
    if (summary.length > 50) {
      summary = summary.slice(0, 47) + '...';
    }
    // Fallback if empty
    if (!summary) {
      summary = 'pattern from feedback';
    }
    return summary.toLowerCase();
  }

  /**
   * Calculate initial confidence for new pattern
   */
  private calculateInitialConfidence(candidate: PatternCandidate): number {
    // Base confidence starts at 0.3 and increases with occurrences
    const base = 0.3;
    const bonus = Math.min(0.5, (candidate.occurrences - this.threshold) * 0.1);
    return Math.min(1, base + bonus);
  }

  /**
   * Calculate confidence for existing pattern
   */
  private calculateConfidence(pattern: LearnedPattern): number {
    // Confidence increases with occurrences, max 0.95
    const base = 0.3;
    const bonus = Math.min(0.65, pattern.occurrences * 0.05);
    return Math.min(0.95, base + bonus);
  }

  /**
   * Archive pattern to separate file
   */
  private async archivePattern(id: string): Promise<void> {
    const pattern = this.patternCache.get(id);
    if (!pattern) return;

    const archivePath = join(this.storagePath, 'patterns-archive.json');
    let archive: LearnedPattern[] = [];

    try {
      const data = await fs.readFile(archivePath, 'utf-8');
      archive = JSON.parse(data);
    } catch {
      // File doesn't exist
    }

    archive.push(pattern);
    await fs.writeFile(archivePath, JSON.stringify(archive, null, 2), 'utf-8');
  }

  /**
   * Ensure data is loaded from storage
   */
  private async ensureLoaded(): Promise<void> {
    if (this.loaded) return;

    const filePath = join(this.storagePath, 'patterns.json');
    try {
      const data = await fs.readFile(filePath, 'utf-8');
      const patterns: LearnedPattern[] = JSON.parse(data);
      for (const pattern of patterns) {
        pattern.lastUsed = new Date(pattern.lastUsed);
        pattern.createdAt = new Date(pattern.createdAt);
        this.patternCache.set(pattern.id, pattern);
      }
    } catch {
      // File doesn't exist yet
    }
    this.loaded = true;
  }

  /**
   * Persist data to storage
   */
  private async persist(): Promise<void> {
    const filePath = join(this.storagePath, 'patterns.json');
    const dir = dirname(filePath);

    try {
      await fs.mkdir(dir, { recursive: true });
    } catch {
      // Directory exists
    }

    const patterns = Array.from(this.patternCache.values());
    await fs.writeFile(filePath, JSON.stringify(patterns, null, 2), 'utf-8');
  }
}
