/**
 * @fileoverview Pattern compression using MDL (Minimum Description Length)
 * @traceability TSK-PATTERN-002, REQ-PATTERN-001-F002
 */

import type { ASTNode, Pattern } from '../types.js';

/**
 * MDL scoring configuration
 */
export interface MDLConfig {
  /** Weight for library size */
  libraryWeight: number;
  /** Weight for encoding cost */
  encodingWeight: number;
  /** Minimum compression ratio to accept abstraction */
  minCompressionRatio: number;
}

/**
 * MDL score result
 */
export interface MDLScore {
  /** Total MDL score (lower is better) */
  total: number;
  /** Library description length */
  libraryLength: number;
  /** Data encoding length given library */
  encodingLength: number;
  /** Compression ratio vs raw */
  compressionRatio: number;
}

/**
 * Pattern library entry
 */
export interface LibraryEntry {
  pattern: Pattern;
  usageCount: number;
  compressionGain: number;
}

/**
 * Pattern compression using MDL principle
 * 
 * @description
 * Implements DreamCoder-style compression using MDL:
 * - Library = set of reusable patterns
 * - Goal: minimize |Library| + |Data given Library|
 */
export class PatternCompressor {
  private config: MDLConfig;
  private library: Map<string, LibraryEntry> = new Map();

  constructor(config: Partial<MDLConfig> = {}) {
    this.config = {
      libraryWeight: config.libraryWeight ?? 1.0,
      encodingWeight: config.encodingWeight ?? 1.0,
      minCompressionRatio: config.minCompressionRatio ?? 1.1,
    };
  }

  /**
   * Calculate MDL score for a set of patterns
   */
  calculateMDL(patterns: Pattern[], data: ASTNode[]): MDLScore {
    // Library description length: sum of pattern complexities
    const libraryLength = this.calculateLibraryLength(patterns);

    // Encoding length: cost to describe data using library
    const encodingLength = this.calculateEncodingLength(patterns, data);

    // Raw description length (without library)
    const rawLength = this.calculateRawLength(data);

    const total = 
      this.config.libraryWeight * libraryLength +
      this.config.encodingWeight * encodingLength;

    const compressionRatio = rawLength / (libraryLength + encodingLength);

    return {
      total,
      libraryLength,
      encodingLength,
      compressionRatio,
    };
  }

  /**
   * Calculate library description length
   */
  private calculateLibraryLength(patterns: Pattern[]): number {
    let length = 0;

    for (const pattern of patterns) {
      // Cost of pattern structure
      length += this.astComplexity(pattern.ast);
      
      // Cost of holes (each hole adds to description)
      length += pattern.holes.length * 2;
    }

    return length;
  }

  /**
   * Calculate encoding length given library
   */
  private calculateEncodingLength(patterns: Pattern[], data: ASTNode[]): number {
    let totalLength = 0;

    for (const ast of data) {
      // Find best matching pattern
      const matches = this.findMatches(patterns, ast);
      
      if (matches.length > 0) {
        // Cost = log(pattern index) + cost of hole bindings
        const bestMatch = matches[0];
        totalLength += Math.log2(patterns.length + 1); // Pattern selection
        totalLength += bestMatch.bindingCost; // Hole binding cost
      } else {
        // No pattern matches - use raw encoding
        totalLength += this.astComplexity(ast);
      }
    }

    return totalLength;
  }

  /**
   * Calculate raw description length (no library)
   */
  private calculateRawLength(data: ASTNode[]): number {
    return data.reduce((sum, ast) => sum + this.astComplexity(ast), 0);
  }

  /**
   * Calculate AST complexity (node count + depth penalty)
   */
  private astComplexity(ast: ASTNode, depth = 0): number {
    let complexity = 1 + depth * 0.1; // Base + depth penalty

    // Type complexity
    complexity += ast.type.length * 0.1;

    // Value complexity
    if (ast.value !== undefined) {
      complexity += String(ast.value).length * 0.05;
    }

    // Recursive children
    for (const child of ast.children) {
      complexity += this.astComplexity(child, depth + 1);
    }

    return complexity;
  }

  /**
   * Find patterns that match an AST
   */
  private findMatches(patterns: Pattern[], ast: ASTNode): Array<{
    patternId: string;
    bindingCost: number;
    bindings: Map<string, ASTNode>;
  }> {
    const matches: Array<{
      patternId: string;
      bindingCost: number;
      bindings: Map<string, ASTNode>;
    }> = [];

    for (const pattern of patterns) {
      const result = this.matchPattern(pattern.ast, ast);
      if (result.matches) {
        matches.push({
          patternId: pattern.id,
          bindingCost: result.bindingCost,
          bindings: result.bindings,
        });
      }
    }

    // Sort by binding cost (lower is better)
    return matches.sort((a, b) => a.bindingCost - b.bindingCost);
  }

  /**
   * Match pattern against AST
   */
  private matchPattern(pattern: ASTNode, target: ASTNode): {
    matches: boolean;
    bindingCost: number;
    bindings: Map<string, ASTNode>;
  } {
    const bindings = new Map<string, ASTNode>();
    let bindingCost = 0;

    const match = (p: ASTNode, t: ASTNode): boolean => {
      // Hole matches anything
      if (p.type === 'Hole') {
        const holeId = p.value as string;
        bindings.set(holeId, t);
        bindingCost += this.astComplexity(t);
        return true;
      }

      // Type must match
      if (p.type !== t.type) {
        return false;
      }

      // Value must match if present
      if (p.value !== undefined && p.value !== t.value) {
        return false;
      }

      // Children must match
      if (p.children.length !== t.children.length) {
        return false;
      }

      for (let i = 0; i < p.children.length; i++) {
        if (!match(p.children[i], t.children[i])) {
          return false;
        }
      }

      return true;
    };

    const matches = match(pattern, target);
    return { matches, bindingCost, bindings };
  }

  /**
   * Compress library by merging similar patterns
   */
  compressLibrary(patterns: Pattern[]): Pattern[] {
    if (patterns.length < 2) return patterns;

    const compressed: Pattern[] = [];
    const merged = new Set<string>();

    for (let i = 0; i < patterns.length; i++) {
      if (merged.has(patterns[i].id)) continue;

      let bestMerge: Pattern | null = null;
      let bestScore = Infinity;

      for (let j = i + 1; j < patterns.length; j++) {
        if (merged.has(patterns[j].id)) continue;

        // Try merging i and j
        const mergedPattern = this.tryMerge(patterns[i], patterns[j]);
        if (mergedPattern) {
          const beforeMDL = this.calculateMDL([patterns[i], patterns[j]], []);
          const afterMDL = this.calculateMDL([mergedPattern], []);

          if (afterMDL.total < beforeMDL.total && afterMDL.compressionRatio >= this.config.minCompressionRatio) {
            if (afterMDL.total < bestScore) {
              bestScore = afterMDL.total;
              bestMerge = mergedPattern;
              merged.add(patterns[j].id);
            }
          }
        }
      }

      compressed.push(bestMerge ?? patterns[i]);
      merged.add(patterns[i].id);
    }

    return compressed;
  }

  /**
   * Try to merge two patterns
   */
  private tryMerge(a: Pattern, b: Pattern): Pattern | null {
    // Simple structural merge - if same type, create pattern with holes for differences
    if (a.ast.type !== b.ast.type) {
      return null;
    }

    const mergedAst = this.mergeAsts(a.ast, b.ast);
    if (!mergedAst) return null;

    const holes = this.extractHolesFromMerged(mergedAst);

    return {
      id: `merged-${Date.now()}`,
      name: `merged_${a.name}_${b.name}`,
      language: a.language,
      ast: mergedAst,
      holes,
      frequency: a.frequency + b.frequency,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    };
  }

  /**
   * Merge two ASTs, creating holes for differences
   */
  private mergeAsts(a: ASTNode, b: ASTNode): ASTNode | null {
    const defaultPos = { row: 0, column: 0 };

    // Different types - create hole
    if (a.type !== b.type) {
      return {
        type: 'Hole',
        value: `H${Date.now()}`,
        children: [],
        startPosition: defaultPos,
        endPosition: defaultPos,
      };
    }

    // Same type - check children
    const children: ASTNode[] = [];
    const maxChildren = Math.max(a.children.length, b.children.length);

    for (let i = 0; i < maxChildren; i++) {
      const childA = a.children[i];
      const childB = b.children[i];

      if (!childA || !childB) {
        // Optional child - create hole
        children.push({
          type: 'Hole',
          value: `H${Date.now()}_${i}`,
          children: [],
          startPosition: defaultPos,
          endPosition: defaultPos,
        });
      } else {
        const merged = this.mergeAsts(childA, childB);
        if (merged) {
          children.push(merged);
        }
      }
    }

    return {
      type: a.type,
      value: a.value === b.value ? a.value : undefined,
      children,
      startPosition: a.startPosition,
      endPosition: b.endPosition,
    };
  }

  /**
   * Extract holes from merged AST
   */
  private extractHolesFromMerged(ast: ASTNode): Pattern['holes'] {
    const holes: Pattern['holes'] = [];

    const traverse = (node: ASTNode): void => {
      if (node.type === 'Hole' && node.value) {
        holes.push({
          id: String(node.value),
          type: 'any',
        });
      }
      for (const child of node.children) {
        traverse(child);
      }
    };

    traverse(ast);
    return holes;
  }

  /**
   * Add pattern to library
   */
  addToLibrary(pattern: Pattern): void {
    this.library.set(pattern.id, {
      pattern,
      usageCount: pattern.frequency,
      compressionGain: 0,
    });
  }

  /**
   * Get library entries sorted by usage
   */
  getLibrary(): LibraryEntry[] {
    return Array.from(this.library.values())
      .sort((a, b) => b.usageCount - a.usageCount);
  }

  /**
   * Clear library
   */
  clearLibrary(): void {
    this.library.clear();
  }

  /**
   * Get library size
   */
  get librarySize(): number {
    return this.library.size;
  }
}
