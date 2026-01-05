/**
 * @fileoverview AST-based pattern extraction
 * @traceability TSK-PATTERN-001, REQ-PATTERN-001-F001
 */

import type { ASTNode, Pattern, ExtractionOptions } from '../types.js';
import { TypeScriptParser } from './typescript-parser.js';
import { SubtreeFinder, type SubtreeCandidate } from './subtree-finder.js';
import { AntiUnifier } from './anti-unifier.js';

/**
 * Pattern extractor using AST analysis
 * 
 * @description
 * Extracts recurring patterns from source code by:
 * 1. Parsing code into AST using TypeScript Compiler API
 * 2. Detecting repeated subtrees via structural hashing
 * 3. Abstracting common structures via anti-unification
 */
export class PatternExtractor {
  private options: ExtractionOptions;
  private parser: TypeScriptParser;
  private finder: SubtreeFinder;
  private antiUnifier: AntiUnifier;

  constructor(options: Partial<ExtractionOptions> = {}) {
    this.options = {
      language: options.language ?? 'typescript',
      minFrequency: options.minFrequency ?? 2,
      maxDepth: options.maxDepth ?? 10,
    };

    this.parser = new TypeScriptParser({ maxDepth: this.options.maxDepth });
    this.finder = new SubtreeFinder({
      minFrequency: this.options.minFrequency,
      maxDepth: this.options.maxDepth,
    });
    this.antiUnifier = new AntiUnifier();
  }

  /**
   * Extract patterns from source code
   * @param source - Source code string
   * @returns Extracted patterns
   */
  async extract(source: string): Promise<Pattern[]> {
    // Phase 1: Parse to AST
    const ast = this.parser.parse(source);
    
    // Phase 2: Find repeated subtrees
    const candidates = this.finder.find(ast);
    
    // Phase 3: Convert to patterns
    const patterns = candidates.map(c => this.createPattern(c));

    return patterns;
  }

  /**
   * Extract patterns from multiple source files
   */
  async extractFromMultiple(sources: string[]): Promise<Pattern[]> {
    // Parse all sources
    const asts = sources.map(s => this.parser.parse(s));
    
    // Find patterns in combined AST space
    const allPatterns: Pattern[] = [];
    const patternMap = new Map<string, SubtreeCandidate>();

    for (const ast of asts) {
      const candidates = this.finder.find(ast);
      for (const candidate of candidates) {
        const existing = patternMap.get(candidate.hash);
        if (existing) {
          existing.frequency += candidate.frequency;
          existing.locations.push(...candidate.locations);
        } else {
          patternMap.set(candidate.hash, { ...candidate });
        }
      }
    }

    // Filter by global frequency
    const filtered = Array.from(patternMap.values())
      .filter(c => c.frequency >= this.options.minFrequency);

    // Abstract similar patterns
    const abstractedPatterns = this.abstractSimilarPatterns(filtered);
    
    for (const candidate of abstractedPatterns) {
      allPatterns.push(this.createPattern(candidate));
    }

    return allPatterns;
  }

  /**
   * Abstract similar patterns using anti-unification
   */
  private abstractSimilarPatterns(candidates: SubtreeCandidate[]): SubtreeCandidate[] {
    if (candidates.length < 2) return candidates;

    // Group by similar structure
    const groups: SubtreeCandidate[][] = [];
    const processed = new Set<number>();

    for (let i = 0; i < candidates.length; i++) {
      if (processed.has(i)) continue;
      
      const group = [candidates[i]];
      processed.add(i);

      for (let j = i + 1; j < candidates.length; j++) {
        if (processed.has(j)) continue;
        
        const similarity = this.antiUnifier.calculateSimilarity(
          candidates[i].ast,
          candidates[j].ast
        );
        
        if (similarity > 0.7) {
          group.push(candidates[j]);
          processed.add(j);
        }
      }
      
      groups.push(group);
    }

    // Abstract each group
    const result: SubtreeCandidate[] = [];
    
    for (const group of groups) {
      if (group.length === 1) {
        result.push(group[0]);
      } else {
        // Anti-unify the group
        const asts = group.map(c => c.ast);
        const unified = this.antiUnifier.antiUnifyAll(asts);
        
        result.push({
          ast: unified.pattern,
          hash: `abstract-${Date.now()}`,
          frequency: group.reduce((sum, c) => sum + c.frequency, 0),
          depth: Math.max(...group.map(c => c.depth)),
          locations: group.flatMap(c => c.locations),
        });
      }
    }

    return result;
  }

  /**
   * Create pattern from candidate
   */
  private createPattern(candidate: SubtreeCandidate): Pattern {
    const id = `PAT-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
    const now = new Date().toISOString();

    // Extract holes from AST if it was anti-unified
    const holes = this.extractHoles(candidate.ast);

    return {
      id,
      name: this.generatePatternName(candidate.ast),
      language: this.options.language,
      ast: candidate.ast,
      holes,
      frequency: candidate.frequency,
      createdAt: now,
      updatedAt: now,
    };
  }

  /**
   * Generate a descriptive pattern name
   */
  private generatePatternName(ast: ASTNode): string {
    const typeNames: Record<string, string> = {
      'FunctionDeclaration': 'function_pattern',
      'MethodDeclaration': 'method_pattern',
      'ClassDeclaration': 'class_pattern',
      'IfStatement': 'conditional_pattern',
      'ForStatement': 'loop_pattern',
      'ForOfStatement': 'iteration_pattern',
      'ForInStatement': 'enumeration_pattern',
      'WhileStatement': 'while_loop_pattern',
      'TryStatement': 'error_handling_pattern',
      'SwitchStatement': 'switch_pattern',
      'ArrowFunction': 'lambda_pattern',
      'CallExpression': 'call_pattern',
      'VariableDeclaration': 'variable_pattern',
      'PropertyDeclaration': 'property_pattern',
    };

    const baseName = typeNames[ast.type] ?? `${ast.type.toLowerCase()}_pattern`;
    return `${baseName}_${Math.random().toString(36).slice(2, 6)}`;
  }

  /**
   * Extract holes from anti-unified AST
   */
  private extractHoles(ast: ASTNode): Pattern['holes'] {
    const holes: Pattern['holes'] = [];
    
    const traverse = (node: ASTNode): void => {
      if (node.type === 'Hole' && node.value) {
        holes.push({
          id: node.value,
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
   * Get parser for direct AST access
   */
  getParser(): TypeScriptParser {
    return this.parser;
  }

  /**
   * Get anti-unifier for direct access
   */
  getAntiUnifier(): AntiUnifier {
    return this.antiUnifier;
  }
}
