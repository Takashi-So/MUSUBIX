/**
 * @fileoverview Skill-Pattern Bridge Implementation
 * Integrates learning-hooks skill with pattern-mcp
 * 
 * @traceability TSK-INT-002, DES-v3.7.0 Section 9.4
 */

import type { Pattern, PatternHole, ASTNode } from '../types.js';
import {
  DEFAULT_SKILL_PATTERN_BRIDGE_CONFIG,
} from './types.js';
import type {
  SkillPatternBridge,
  SkillPatternBridgeConfig,
  LearnedPattern,
  LearnedPatternCategory,
  PatternQueryContext,
  PatternMatchResult,
  PatternStorageResult,
  PatternStatistics,
  ConsolidationResult,
} from './types.js';

/**
 * Create a Skill-Pattern Bridge instance
 */
export function createSkillPatternBridge(
  config: Partial<SkillPatternBridgeConfig> = {}
): SkillPatternBridge {
  const fullConfig: SkillPatternBridgeConfig = {
    ...DEFAULT_SKILL_PATTERN_BRIDGE_CONFIG,
    ...config,
  };

  // In-memory storage for patterns (would be file-based in production)
  const patterns: Map<string, LearnedPattern> = new Map();

  /**
   * Calculate text similarity using simple word overlap
   */
  function calculateSimilarity(text1: string, text2: string): number {
    const words1 = new Set(text1.toLowerCase().split(/\s+/));
    const words2 = new Set(text2.toLowerCase().split(/\s+/));
    
    const intersection = new Set([...words1].filter(w => words2.has(w)));
    const union = new Set([...words1, ...words2]);
    
    return union.size > 0 ? intersection.size / union.size : 0;
  }

  /**
   * Find similar patterns
   */
  function findSimilarPatterns(pattern: LearnedPattern): LearnedPattern[] {
    const similar: LearnedPattern[] = [];
    
    for (const existing of patterns.values()) {
      if (existing.id === pattern.id) continue;
      if (existing.category !== pattern.category) continue;
      
      const similarity = calculateSimilarity(
        `${existing.problem} ${existing.solution}`,
        `${pattern.problem} ${pattern.solution}`
      );
      
      if (similarity >= fullConfig.consolidationThreshold) {
        similar.push(existing);
      }
    }
    
    return similar;
  }

  /**
   * Apply privacy filter to pattern content
   */
  function applyPrivacyFilter(text: string): string {
    if (!fullConfig.enablePrivacyFilter) return text;
    
    // Simple patterns for sensitive data
    const sensitivePatterns = [
      /api[_-]?key["\s:=]+([a-zA-Z0-9_-]{20,})/gi,
      /password["\s:=]+([^\s"']+)/gi,
      /secret["\s:=]+([a-zA-Z0-9_-]{20,})/gi,
      /token["\s:=]+([a-zA-Z0-9_.-]{20,})/gi,
      /AKIA[0-9A-Z]{16}/gi,
    ];
    
    let filtered = text;
    for (const pattern of sensitivePatterns) {
      filtered = filtered.replace(pattern, '[REDACTED]');
    }
    
    return filtered;
  }

  /**
   * Generate unique pattern ID
   */
  function generatePatternId(): string {
    const timestamp = Date.now().toString(36);
    const random = Math.random().toString(36).substring(2, 8);
    return `LP-${timestamp}-${random}`;
  }

  return {
    async storeLearnedPattern(pattern: LearnedPattern): Promise<PatternStorageResult> {
      try {
        // Validate confidence
        if (pattern.confidence < fullConfig.minConfidence) {
          return {
            success: false,
            consolidated: false,
            error: `Confidence ${pattern.confidence} is below minimum ${fullConfig.minConfidence}`,
          };
        }

        // Apply privacy filter
        const filteredPattern: LearnedPattern = {
          ...pattern,
          problem: applyPrivacyFilter(pattern.problem),
          solution: applyPrivacyFilter(pattern.solution),
          example: pattern.example ? applyPrivacyFilter(pattern.example) : undefined,
        };

        // Check for consolidation
        if (fullConfig.autoConsolidate) {
          const similar = findSimilarPatterns(filteredPattern);
          
          if (similar.length > 0) {
            const mostSimilar = similar[0];
            // Merge: update usage count and confidence
            mostSimilar.usageCount += 1;
            mostSimilar.confidence = Math.min(1, (mostSimilar.confidence + filteredPattern.confidence) / 2);
            patterns.set(mostSimilar.id, mostSimilar);
            
            return {
              success: true,
              patternId: mostSimilar.id,
              consolidated: true,
              consolidatedWith: mostSimilar.id,
            };
          }
        }

        // Check max patterns limit
        if (patterns.size >= fullConfig.maxPatterns) {
          // Remove least used pattern
          let leastUsed: LearnedPattern | null = null;
          for (const p of patterns.values()) {
            if (!leastUsed || p.usageCount < leastUsed.usageCount) {
              leastUsed = p;
            }
          }
          if (leastUsed) {
            patterns.delete(leastUsed.id);
          }
        }

        // Store new pattern
        const patternId = filteredPattern.id || generatePatternId();
        filteredPattern.id = patternId;
        patterns.set(patternId, filteredPattern);

        return {
          success: true,
          patternId,
          consolidated: false,
        };
      } catch (error) {
        return {
          success: false,
          consolidated: false,
          error: error instanceof Error ? error.message : 'Unknown error',
        };
      }
    },

    async queryPatterns(context: PatternQueryContext): Promise<PatternMatchResult[]> {
      const results: PatternMatchResult[] = [];
      const maxResults = context.maxResults ?? 10;

      for (const pattern of patterns.values()) {
        let relevance = 0;
        let matchReason = '';

        // Match by error message
        if (context.errorMessage) {
          const errorSimilarity = calculateSimilarity(
            context.errorMessage,
            pattern.problem
          );
          if (errorSimilarity > 0.3) {
            relevance = Math.max(relevance, errorSimilarity);
            matchReason = 'Error message similarity';
          }
        }

        // Match by keywords
        if (context.keywords && context.keywords.length > 0) {
          const patternText = `${pattern.name} ${pattern.problem} ${pattern.solution}`.toLowerCase();
          const matchedKeywords = context.keywords.filter(k => 
            patternText.includes(k.toLowerCase())
          );
          
          if (matchedKeywords.length > 0) {
            const keywordRelevance = matchedKeywords.length / context.keywords.length;
            if (keywordRelevance > relevance) {
              relevance = keywordRelevance;
              matchReason = `Matched keywords: ${matchedKeywords.join(', ')}`;
            }
          }
        }

        // Match by language
        if (context.language) {
          const languageMatch = pattern.triggerConditions.some(tc =>
            tc.toLowerCase().includes(context.language!.toLowerCase())
          );
          if (languageMatch) {
            relevance = Math.max(relevance, 0.5);
            if (!matchReason) matchReason = 'Language match';
          }
        }

        // Boost by confidence and usage
        if (relevance > 0) {
          relevance *= (0.7 + 0.3 * pattern.confidence);
          relevance *= (1 + Math.log10(1 + pattern.usageCount) * 0.1);
          
          results.push({
            pattern,
            relevance: Math.min(1, relevance),
            matchReason,
          });
        }
      }

      // Sort by relevance and limit
      return results
        .sort((a, b) => b.relevance - a.relevance)
        .slice(0, maxResults);
    },

    convertToPattern(learned: LearnedPattern): Pattern {
      // Create a simple AST representation
      const ast: ASTNode = {
        type: 'learned_pattern',
        children: [],
        value: learned.solution,
        startPosition: { row: 0, column: 0 },
        endPosition: { row: 0, column: 0 },
      };

      // Create holes for variable parts (simplified)
      const holes: PatternHole[] = [];
      const placeholderPattern = /\[([A-Z_]+)\]/g;
      let match;
      let holeIndex = 0;
      
      while ((match = placeholderPattern.exec(learned.solution)) !== null) {
        holes.push({
          id: `hole-${holeIndex++}`,
          type: match[1],
        });
      }

      return {
        id: learned.id,
        name: learned.name,
        language: 'typescript', // Default, could be extracted from context
        ast,
        holes,
        frequency: learned.usageCount,
        createdAt: learned.extractedAt,
        updatedAt: new Date().toISOString(),
      };
    },

    convertFromPattern(pattern: Pattern): LearnedPattern {
      return {
        id: pattern.id,
        name: pattern.name,
        category: 'project_specific',
        extractedAt: pattern.createdAt,
        context: `Language: ${pattern.language}`,
        problem: `Pattern with ${pattern.holes.length} variable parts`,
        solution: pattern.ast.value ?? '',
        triggerConditions: [`language:${pattern.language}`],
        confidence: Math.min(1, pattern.frequency / 10),
        usageCount: pattern.frequency,
      };
    },

    async getStatistics(): Promise<PatternStatistics> {
      const byCategory: Record<LearnedPatternCategory, number> = {
        error_resolution: 0,
        user_corrections: 0,
        workarounds: 0,
        debugging_techniques: 0,
        project_specific: 0,
        performance_optimization: 0,
        refactoring: 0,
      };

      let totalConfidence = 0;
      let totalUsageCount = 0;
      let mostUsed: LearnedPattern | undefined;
      let recentlyAdded = 0;
      
      const sevenDaysAgo = new Date();
      sevenDaysAgo.setDate(sevenDaysAgo.getDate() - 7);

      for (const pattern of patterns.values()) {
        byCategory[pattern.category]++;
        totalConfidence += pattern.confidence;
        totalUsageCount += pattern.usageCount;
        
        if (!mostUsed || pattern.usageCount > mostUsed.usageCount) {
          mostUsed = pattern;
        }
        
        if (new Date(pattern.extractedAt) >= sevenDaysAgo) {
          recentlyAdded++;
        }
      }

      return {
        totalPatterns: patterns.size,
        byCategory,
        averageConfidence: patterns.size > 0 ? totalConfidence / patterns.size : 0,
        totalUsageCount,
        mostUsed,
        recentlyAdded,
      };
    },

    async consolidatePatterns(): Promise<ConsolidationResult> {
      const merges: Array<{ sourceId: string; targetId: string; similarity: number }> = [];
      const processed = new Set<string>();
      
      const patternList = Array.from(patterns.values());
      
      for (let i = 0; i < patternList.length; i++) {
        const pattern = patternList[i];
        if (processed.has(pattern.id)) continue;
        
        for (let j = i + 1; j < patternList.length; j++) {
          const other = patternList[j];
          if (processed.has(other.id)) continue;
          if (pattern.category !== other.category) continue;
          
          const similarity = calculateSimilarity(
            `${pattern.problem} ${pattern.solution}`,
            `${other.problem} ${other.solution}`
          );
          
          if (similarity >= fullConfig.consolidationThreshold) {
            // Merge other into pattern
            pattern.usageCount += other.usageCount;
            pattern.confidence = (pattern.confidence + other.confidence) / 2;
            
            patterns.delete(other.id);
            processed.add(other.id);
            
            merges.push({
              sourceId: other.id,
              targetId: pattern.id,
              similarity,
            });
          }
        }
      }

      return {
        mergedCount: merges.length,
        remainingCount: patterns.size,
        merges,
      };
    },
  };
}

/**
 * Create learned pattern from session data
 */
export function createLearnedPatternFromSession(
  category: LearnedPatternCategory,
  problem: string,
  solution: string,
  options: {
    name?: string;
    context?: string;
    example?: string;
    triggerConditions?: string[];
    sourceSession?: string;
    confidence?: number;
  } = {}
): LearnedPattern {
  const now = new Date().toISOString();
  const id = `LP-${Date.now().toString(36)}-${Math.random().toString(36).substring(2, 8)}`;
  
  return {
    id,
    name: options.name ?? `Pattern: ${problem.substring(0, 50)}...`,
    category,
    extractedAt: now,
    context: options.context ?? '',
    problem,
    solution,
    example: options.example,
    triggerConditions: options.triggerConditions ?? [],
    sourceSession: options.sourceSession,
    confidence: options.confidence ?? 0.7,
    usageCount: 1,
  };
}

/**
 * Format pattern match results as markdown
 */
export function formatPatternMatchesAsMarkdown(matches: PatternMatchResult[]): string {
  if (matches.length === 0) {
    return '📝 No relevant patterns found.\n';
  }

  const lines = ['# 📚 Relevant Patterns\n'];
  
  for (let i = 0; i < matches.length; i++) {
    const { pattern, relevance, matchReason } = matches[i];
    
    lines.push(`## ${i + 1}. ${pattern.name}`);
    lines.push('');
    lines.push(`**Relevance**: ${(relevance * 100).toFixed(1)}%`);
    lines.push(`**Reason**: ${matchReason}`);
    lines.push(`**Category**: ${pattern.category}`);
    lines.push('');
    lines.push('### Problem');
    lines.push(pattern.problem);
    lines.push('');
    lines.push('### Solution');
    lines.push(pattern.solution);
    
    if (pattern.example) {
      lines.push('');
      lines.push('### Example');
      lines.push('```');
      lines.push(pattern.example);
      lines.push('```');
    }
    
    lines.push('');
    lines.push('---');
    lines.push('');
  }

  return lines.join('\n');
}
