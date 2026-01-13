/**
 * Pattern Learning Service
 *
 * Service for integrating pattern learning with scaffold generation.
 * Coordinates PatternExtractor, PatternMerger, and PatternLibrary.
 *
 * @traceability REQ-PTN-001, REQ-PTN-002, REQ-PTN-003
 * @see TSK-PTN-003 - Pattern Learning Service Integration
 */

import type { GeneratedFile } from './value-object-generator.js';
import {
  PatternAutoExtractor,
  createPatternExtractor,
  type ExtractedPattern,
} from './pattern-extractor.js';
import {
  PatternMerger,
  createPatternMerger,
} from './pattern-merger.js';

/**
 * Pattern learning service configuration
 */
export interface PatternLearningConfig {
  /** Whether pattern learning is enabled */
  enabled: boolean;
  /** Minimum confidence threshold for pattern storage */
  minConfidence: number;
  /** Enable auto-extraction after scaffold generation */
  autoExtract: boolean;
  /** Enable pattern suggestions during generation */
  enableSuggestions: boolean;
  /** Maximum patterns to store per category */
  maxPatternsPerCategory: number;
  /** Path to pattern library storage */
  libraryPath?: string;
}

/**
 * Default pattern learning configuration
 */
export const DEFAULT_PATTERN_LEARNING_CONFIG: PatternLearningConfig = {
  enabled: true,
  minConfidence: 0.7,
  autoExtract: true,
  enableSuggestions: true,
  maxPatternsPerCategory: 100,
  libraryPath: 'storage/learning/patterns.json',
};

/**
 * Pattern suggestion for scaffold generation
 */
export interface PatternSuggestion {
  patternId: string;
  category: string;
  description: string;
  confidence: number;
  applicableTo: string;
  suggestedCode?: string;
}

/**
 * Pattern learning result
 */
export interface PatternLearningResult {
  extractedPatterns: ExtractedPattern[];
  mergedPatterns: ExtractedPattern[];
  newPatternsCount: number;
  updatedPatternsCount: number;
  suggestions: PatternSuggestion[];
  executionTime: number;
}

/**
 * Pattern library entry
 */
export interface PatternLibraryEntry {
  pattern: ExtractedPattern;
  usageCount: number;
  lastUsed: string;
  successRate: number;
  feedback: Array<{
    timestamp: string;
    type: 'accept' | 'reject' | 'modify';
    comment?: string;
  }>;
}

/**
 * Pattern learning service for scaffold generation
 */
export class PatternLearningService {
  private config: PatternLearningConfig;
  private extractor: PatternAutoExtractor;
  private merger: PatternMerger;
  private library: Map<string, PatternLibraryEntry>;
  private suggestions: Map<string, PatternSuggestion[]>;

  constructor(config: Partial<PatternLearningConfig> = {}) {
    this.config = { ...DEFAULT_PATTERN_LEARNING_CONFIG, ...config };
    this.extractor = createPatternExtractor({
      minConfidence: this.config.minConfidence,
    });
    this.merger = createPatternMerger();
    this.library = new Map();
    this.suggestions = new Map();
  }

  /**
   * Learn patterns from generated files
   */
  async learnFromGeneration(files: GeneratedFile[]): Promise<PatternLearningResult> {
    const startTime = Date.now();

    if (!this.config.enabled || files.length === 0) {
      return {
        extractedPatterns: [],
        mergedPatterns: [],
        newPatternsCount: 0,
        updatedPatternsCount: 0,
        suggestions: [],
        executionTime: Date.now() - startTime,
      };
    }

    // Extract patterns from generated files
    const extractedPatterns: ExtractedPattern[] = [];

    for (const file of files) {
      if (this.config.autoExtract) {
        const patterns = this.extractor.extractFromCode(file.content, file.path, 'AUTO');
        extractedPatterns.push(...patterns);
      }
    }

    // Filter by confidence threshold
    const filteredPatterns = extractedPatterns.filter(
      (p) => p.metadata.confidence >= this.config.minConfidence
    );

    // Merge with existing patterns (only if we have patterns to merge)
    const existingPatterns = Array.from(this.library.values()).map((e) => e.pattern);
    const allPatterns = [...existingPatterns, ...filteredPatterns];
    
    // Skip merge if no patterns
    const mergedPatterns: ExtractedPattern[] = [];
    if (allPatterns.length > 0) {
      try {
        const mergeResult = this.merger.merge(allPatterns);
        if (mergeResult && mergeResult.patterns) {
          mergedPatterns.push(...mergeResult.patterns);
        }
      } catch (_error) {
        // Merge failed, use filtered patterns directly
        mergedPatterns.push(...filteredPatterns);
      }
    }

    // Update library
    let newPatternsCount = 0;
    let updatedPatternsCount = 0;

    for (const pattern of mergedPatterns) {
      const existingEntry = this.library.get(pattern.id);

      if (existingEntry) {
        // Update existing pattern
        existingEntry.pattern = pattern;
        existingEntry.usageCount++;
        existingEntry.lastUsed = new Date().toISOString();
        updatedPatternsCount++;
      } else {
        // Add new pattern
        this.library.set(pattern.id, {
          pattern,
          usageCount: 1,
          lastUsed: new Date().toISOString(),
          successRate: 1.0,
          feedback: [],
        });
        newPatternsCount++;
      }
    }

    // Enforce max patterns per category
    this.enforceMaxPatterns();

    // Generate suggestions for next generation
    const suggestions = this.generateSuggestions(files);

    return {
      extractedPatterns: filteredPatterns,
      mergedPatterns,
      newPatternsCount,
      updatedPatternsCount,
      suggestions,
      executionTime: Date.now() - startTime,
    };
  }

  /**
   * Get pattern suggestions for a given context
   */
  getSuggestions(context: string, category?: string): PatternSuggestion[] {
    if (!this.config.enableSuggestions) {
      return [];
    }

    const cachedSuggestions = this.suggestions.get(context);
    if (cachedSuggestions) {
      return category
        ? cachedSuggestions.filter((s) => s.category === category)
        : cachedSuggestions;
    }

    return this.generateSuggestions([{ path: context, content: '', type: 'unknown' }]);
  }

  /**
   * Record feedback for a pattern
   */
  recordFeedback(
    patternId: string,
    type: 'accept' | 'reject' | 'modify',
    comment?: string
  ): boolean {
    const entry = this.library.get(patternId);
    if (!entry) {
      return false;
    }

    entry.feedback.push({
      timestamp: new Date().toISOString(),
      type,
      comment,
    });

    // Update success rate based on feedback
    const feedbackCount = entry.feedback.length;
    const acceptCount = entry.feedback.filter((f) => f.type === 'accept').length;
    const modifyCount = entry.feedback.filter((f) => f.type === 'modify').length;

    entry.successRate = (acceptCount + modifyCount * 0.5) / feedbackCount;

    return true;
  }

  /**
   * Get pattern by ID
   */
  getPattern(patternId: string): ExtractedPattern | undefined {
    return this.library.get(patternId)?.pattern;
  }

  /**
   * Get all patterns in library
   */
  getAllPatterns(): ExtractedPattern[] {
    return Array.from(this.library.values()).map((e) => e.pattern);
  }

  /**
   * Get patterns by category
   */
  getPatternsByCategory(category: string): ExtractedPattern[] {
    return Array.from(this.library.values())
      .filter((e) => e.pattern.category === category)
      .map((e) => e.pattern);
  }

  /**
   * Get library statistics
   */
  getStatistics(): {
    totalPatterns: number;
    byCategory: Record<string, number>;
    averageConfidence: number;
    averageSuccessRate: number;
    topPatterns: Array<{ id: string; usageCount: number }>;
  } {
    const entries = Array.from(this.library.values());
    const totalPatterns = entries.length;

    const byCategory: Record<string, number> = {};
    let totalConfidence = 0;
    let totalSuccessRate = 0;

    for (const entry of entries) {
      const category = entry.pattern.category;
      byCategory[category] = (byCategory[category] || 0) + 1;
      totalConfidence += entry.pattern.metadata.confidence;
      totalSuccessRate += entry.successRate;
    }

    const topPatterns = entries
      .sort((a, b) => b.usageCount - a.usageCount)
      .slice(0, 10)
      .map((e) => ({ id: e.pattern.id, usageCount: e.usageCount }));

    return {
      totalPatterns,
      byCategory,
      averageConfidence: totalPatterns > 0 ? totalConfidence / totalPatterns : 0,
      averageSuccessRate: totalPatterns > 0 ? totalSuccessRate / totalPatterns : 0,
      topPatterns,
    };
  }

  /**
   * Export library to JSON
   */
  exportLibrary(): string {
    const data = {
      version: '1.0.0',
      exportedAt: new Date().toISOString(),
      patterns: Array.from(this.library.entries()).map(([id, entry]) => ({
        id,
        ...entry,
      })),
    };

    return JSON.stringify(data, null, 2);
  }

  /**
   * Import library from JSON
   */
  importLibrary(json: string): { imported: number; skipped: number } {
    try {
      const data = JSON.parse(json) as {
        patterns: Array<{ id: string } & PatternLibraryEntry>;
      };

      let imported = 0;
      let skipped = 0;

      for (const item of data.patterns) {
        if (!this.library.has(item.id)) {
          this.library.set(item.id, {
            pattern: item.pattern,
            usageCount: item.usageCount,
            lastUsed: item.lastUsed,
            successRate: item.successRate,
            feedback: item.feedback,
          });
          imported++;
        } else {
          skipped++;
        }
      }

      return { imported, skipped };
    } catch (_error) {
      return { imported: 0, skipped: 0 };
    }
  }

  /**
   * Clear all patterns from library
   */
  clearLibrary(): void {
    this.library.clear();
    this.suggestions.clear();
  }

  /**
   * Generate suggestions based on generated files
   */
  private generateSuggestions(files: GeneratedFile[]): PatternSuggestion[] {
    const suggestions: PatternSuggestion[] = [];

    // Find relevant patterns based on file types
    for (const file of files) {
      const relevantCategory = this.inferCategory(file);
      const relevantPatterns = this.getPatternsByCategory(relevantCategory);

      for (const pattern of relevantPatterns.slice(0, 3)) {
        const entry = this.library.get(pattern.id);
        if (entry && entry.successRate >= 0.5) {
          suggestions.push({
            patternId: pattern.id,
            category: pattern.category,
            description: `Apply ${pattern.name} pattern`,
            confidence: pattern.metadata.confidence * entry.successRate,
            applicableTo: file.path,
            suggestedCode: pattern.template,
          });
        }
      }
    }

    // Cache suggestions
    for (const file of files) {
      const filesuggestions = suggestions.filter((s) => s.applicableTo === file.path);
      this.suggestions.set(file.path, filesuggestions);
    }

    return suggestions;
  }

  /**
   * Infer pattern category from file
   */
  private inferCategory(file: GeneratedFile): string {
    const path = file.path.toLowerCase();

    if (path.includes('value-object') || path.includes('vo')) {
      return 'value-object';
    }
    if (path.includes('status') || path.includes('state')) {
      return 'status-machine';
    }
    if (path.includes('entity') || path.includes('entities')) {
      return 'entity';
    }
    if (path.includes('repository') || path.includes('repositories')) {
      return 'repository';
    }
    if (path.includes('service') || path.includes('services')) {
      return 'service';
    }

    return 'general';
  }

  /**
   * Enforce maximum patterns per category
   */
  private enforceMaxPatterns(): void {
    const byCategory = new Map<string, PatternLibraryEntry[]>();

    // Group by category
    for (const entry of this.library.values()) {
      const category = entry.pattern.category;
      const list = byCategory.get(category) || [];
      list.push(entry);
      byCategory.set(category, list);
    }

    // Remove excess patterns (lowest confidence first)
    for (const [_category, entries] of byCategory) {
      if (entries.length > this.config.maxPatternsPerCategory) {
        // Sort by confidence and success rate
        entries.sort(
          (a, b) => b.pattern.metadata.confidence * b.successRate - a.pattern.metadata.confidence * a.successRate
        );

        // Remove excess
        const toRemove = entries.slice(this.config.maxPatternsPerCategory);
        for (const entry of toRemove) {
          this.library.delete(entry.pattern.id);
        }
      }
    }
  }
}

/**
 * Create pattern learning service
 */
export function createPatternLearningService(
  config?: Partial<PatternLearningConfig>
): PatternLearningService {
  return new PatternLearningService(config);
}
