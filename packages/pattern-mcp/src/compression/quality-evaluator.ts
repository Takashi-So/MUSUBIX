/**
 * @fileoverview Pattern quality evaluator
 * @traceability TSK-PATTERN-002, REQ-PATTERN-001-F002
 */

import type { ASTNode, Pattern } from '../types.js';

/**
 * Quality metrics for a pattern
 */
export interface PatternQuality {
  /** Overall quality score 0-1 */
  score: number;
  /** Generality: how abstractable is the pattern */
  generality: number;
  /** Specificity: how precisely does it match */
  specificity: number;
  /** Utility: how useful for code generation */
  utility: number;
  /** Stability: how consistent across codebases */
  stability: number;
}

/**
 * Quality evaluation configuration
 */
export interface QualityConfig {
  /** Minimum frequency for high utility */
  minFrequency: number;
  /** Maximum holes for high specificity */
  maxHoles: number;
  /** Ideal depth range for quality patterns */
  idealDepthRange: [number, number];
}

/**
 * Pattern quality evaluator
 * 
 * @description
 * Evaluates pattern quality based on:
 * - Generality: abstractness level (holes vs concrete)
 * - Specificity: how precise the pattern is
 * - Utility: usefulness based on frequency and coverage
 * - Stability: consistency of the pattern
 */
export class PatternQualityEvaluator {
  private config: QualityConfig;

  constructor(config: Partial<QualityConfig> = {}) {
    this.config = {
      minFrequency: config.minFrequency ?? 3,
      maxHoles: config.maxHoles ?? 5,
      idealDepthRange: config.idealDepthRange ?? [3, 8],
    };
  }

  /**
   * Evaluate overall pattern quality
   */
  evaluate(pattern: Pattern): PatternQuality {
    const generality = this.evaluateGenerality(pattern);
    const specificity = this.evaluateSpecificity(pattern);
    const utility = this.evaluateUtility(pattern);
    const stability = this.evaluateStability(pattern);

    // Weighted average for overall score
    const score = (
      generality * 0.25 +
      specificity * 0.25 +
      utility * 0.30 +
      stability * 0.20
    );

    return {
      score,
      generality,
      specificity,
      utility,
      stability,
    };
  }

  /**
   * Evaluate pattern generality (abstractness)
   */
  private evaluateGenerality(pattern: Pattern): number {
    const totalNodes = this.countNodes(pattern.ast);
    const holeCount = pattern.holes.length;

    if (totalNodes === 0) return 0;

    // Ratio of holes to total nodes
    const holeRatio = holeCount / totalNodes;

    // Too few holes = too specific
    // Too many holes = too general (pattern is just holes)
    // Sweet spot: 10-30% holes
    if (holeRatio < 0.05) return 0.3;
    if (holeRatio < 0.10) return 0.6;
    if (holeRatio < 0.30) return 1.0;
    if (holeRatio < 0.50) return 0.7;
    return 0.3;
  }

  /**
   * Evaluate pattern specificity
   */
  private evaluateSpecificity(pattern: Pattern): number {
    const totalNodes = this.countNodes(pattern.ast);
    const depth = this.calculateDepth(pattern.ast);
    const holeCount = pattern.holes.length;

    // More nodes = more specific
    const nodeScore = Math.min(totalNodes / 20, 1.0);

    // Fewer holes = more specific
    const holeScore = Math.max(0, 1 - holeCount / this.config.maxHoles);

    // Ideal depth range
    const [minDepth, maxDepth] = this.config.idealDepthRange;
    let depthScore = 0;
    if (depth >= minDepth && depth <= maxDepth) {
      depthScore = 1.0;
    } else if (depth < minDepth) {
      depthScore = depth / minDepth;
    } else {
      depthScore = Math.max(0, 1 - (depth - maxDepth) / maxDepth);
    }

    return (nodeScore + holeScore + depthScore) / 3;
  }

  /**
   * Evaluate pattern utility
   */
  private evaluateUtility(pattern: Pattern): number {
    // Frequency-based utility
    const freqScore = Math.min(pattern.frequency / this.config.minFrequency, 1.0);

    // Type-based utility (some patterns are more useful)
    const typeScore = this.getTypeUtility(pattern.ast.type);

    // Hole usability (named holes are more useful)
    const holeScore = pattern.holes.length > 0
      ? pattern.holes.filter(h => h.type !== 'any').length / pattern.holes.length
      : 0.5;

    return (freqScore * 0.5 + typeScore * 0.3 + holeScore * 0.2);
  }

  /**
   * Evaluate pattern stability
   */
  private evaluateStability(pattern: Pattern): number {
    // Stability is harder to measure without historical data
    // Use structural consistency as proxy
    
    const ast = pattern.ast;
    
    // Consistent structure = stable
    const hasConsistentChildren = this.hasConsistentChildTypes(ast);
    const hasNoAmbiguity = !this.hasAmbiguousHoles(pattern);
    
    let score = 0.5; // Base score
    
    if (hasConsistentChildren) score += 0.25;
    if (hasNoAmbiguity) score += 0.25;
    
    return score;
  }

  /**
   * Count total nodes in AST
   */
  private countNodes(ast: ASTNode): number {
    let count = 1;
    for (const child of ast.children) {
      count += this.countNodes(child);
    }
    return count;
  }

  /**
   * Calculate AST depth
   */
  private calculateDepth(ast: ASTNode): number {
    if (ast.children.length === 0) return 1;
    return 1 + Math.max(...ast.children.map(c => this.calculateDepth(c)));
  }

  /**
   * Get utility score for AST node type
   */
  private getTypeUtility(type: string): number {
    const highUtility = [
      'FunctionDeclaration',
      'MethodDeclaration', 
      'ClassDeclaration',
      'ArrowFunction',
    ];
    const mediumUtility = [
      'IfStatement',
      'ForStatement',
      'WhileStatement',
      'TryStatement',
      'SwitchStatement',
    ];
    const lowUtility = [
      'VariableDeclaration',
      'ExpressionStatement',
      'ReturnStatement',
    ];

    if (highUtility.includes(type)) return 1.0;
    if (mediumUtility.includes(type)) return 0.7;
    if (lowUtility.includes(type)) return 0.4;
    return 0.5;
  }

  /**
   * Check if children have consistent types
   */
  private hasConsistentChildTypes(ast: ASTNode): boolean {
    if (ast.children.length < 2) return true;

    const types = ast.children.map(c => c.type);
    const uniqueTypes = new Set(types);
    
    // More than 80% same type = consistent
    const mostCommon = Math.max(...Array.from(uniqueTypes).map(
      t => types.filter(tt => tt === t).length
    ));
    
    return mostCommon / types.length >= 0.8;
  }

  /**
   * Check if pattern has ambiguous holes
   */
  private hasAmbiguousHoles(pattern: Pattern): boolean {
    // Holes without type constraints are ambiguous
    const ambiguous = pattern.holes.filter(h => h.type === 'any');
    return ambiguous.length > pattern.holes.length * 0.5;
  }

  /**
   * Rank patterns by quality
   */
  rankPatterns(patterns: Pattern[]): Array<{ pattern: Pattern; quality: PatternQuality }> {
    return patterns
      .map(pattern => ({
        pattern,
        quality: this.evaluate(pattern),
      }))
      .sort((a, b) => b.quality.score - a.quality.score);
  }

  /**
   * Filter patterns by minimum quality
   */
  filterByQuality(patterns: Pattern[], minScore: number): Pattern[] {
    return patterns.filter(p => this.evaluate(p).score >= minScore);
  }
}
