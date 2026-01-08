/**
 * PatternMiner - Extracts patterns from code corpus
 *
 * REQ-LL-001: 階層的抽象化
 * DES-PHASE2-001: Abstraction Engine / PatternMiner
 */

import type {
  CodeCorpus,
  PatternCandidate,
  PatternMinerConfig,
  ASTNode,
  PatternOccurrence,
} from '../types.js';
import { PatternMiningError } from '../errors.js';

/**
 * PatternMiner interface
 */
export interface PatternMiner {
  /** Mine patterns from a code corpus */
  mine(corpus: CodeCorpus): Promise<PatternCandidate[]>;

  /** Set minimum occurrences threshold */
  setMinOccurrences(count: number): void;

  /** Get current configuration */
  getConfig(): PatternMinerConfig;
}

/**
 * Default PatternMiner implementation
 */
class PatternMinerImpl implements PatternMiner {
  private config: PatternMinerConfig;

  constructor(config: PatternMinerConfig = {}) {
    this.config = {
      minOccurrences: config.minOccurrences ?? 2,
      maxDepth: config.maxDepth ?? 10,
      minSize: config.minSize ?? 3,
      maxSize: config.maxSize ?? 50,
    };
  }

  async mine(corpus: CodeCorpus): Promise<PatternCandidate[]> {
    if (!corpus || !corpus.files || corpus.files.length === 0) {
      throw new PatternMiningError('Corpus is empty or invalid');
    }

    const candidates: PatternCandidate[] = [];
    const patternMap = new Map<string, PatternOccurrence[]>();

    // Parse and extract subtrees from each file
    for (const file of corpus.files) {
      try {
        const ast = this.parseFile(file.content);
        const subtrees = this.extractSubtrees(ast, file.path);

        for (const { hash, occurrence } of subtrees) {
          const occurrences = patternMap.get(hash) ?? [];
          occurrences.push(occurrence);
          patternMap.set(hash, occurrences);
        }
      } catch (error) {
        // Skip files that fail to parse
        console.warn(`Failed to parse ${file.path}: ${error}`);
      }
    }

    // Filter by minimum occurrences and create candidates
    let idCounter = 0;
    for (const [hash, occurrences] of patternMap) {
      if (occurrences.length >= this.config.minOccurrences!) {
        const ast = this.hashToAST(hash);
        if (ast && this.isValidPatternSize(ast)) {
          candidates.push({
            id: `PAT-${++idCounter}`,
            ast,
            occurrences,
            score: this.computeScore(occurrences.length, ast),
          });
        }
      }
    }

    // Sort by score descending
    candidates.sort((a, b) => b.score - a.score);

    return candidates;
  }

  setMinOccurrences(count: number): void {
    if (count < 1) {
      throw new PatternMiningError('minOccurrences must be at least 1');
    }
    this.config.minOccurrences = count;
  }

  getConfig(): PatternMinerConfig {
    return { ...this.config };
  }

  // =========================================================================
  // Private methods
  // =========================================================================

  private parseFile(content: string): ASTNode {
    // Simplified parser - in production, use a real parser like TypeScript compiler API
    // For now, we create a simple token-based AST
    const tokens = this.tokenize(content);
    return this.buildAST(tokens);
  }

  private tokenize(content: string): string[] {
    // Simple tokenization
    return content
      .replace(/\/\/.*$/gm, '') // Remove single-line comments
      .replace(/\/\*[\s\S]*?\*\//g, '') // Remove multi-line comments
      .split(/(\s+|[{}()\[\];,.:=<>+\-*/&|!?])/g)
      .filter((t) => t.trim().length > 0);
  }

  private buildAST(tokens: string[]): ASTNode {
    // Simplified AST building
    const root: ASTNode = { type: 'Program', children: [] };

    let i = 0;
    while (i < tokens.length) {
      const node = this.parseStatement(tokens, i);
      if (node.node) {
        root.children!.push(node.node);
      }
      i = node.nextIndex;
    }

    return root;
  }

  private parseStatement(
    tokens: string[],
    start: number
  ): { node: ASTNode | null; nextIndex: number } {
    if (start >= tokens.length) {
      return { node: null, nextIndex: start };
    }

    const token = tokens[start];

    // Handle different statement types
    if (token === 'function' || token === 'const' || token === 'let' || token === 'var') {
      return this.parseDeclaration(tokens, start);
    }

    if (token === 'if') {
      return this.parseIfStatement(tokens, start);
    }

    if (token === 'for' || token === 'while') {
      return this.parseLoop(tokens, start);
    }

    if (token === 'return') {
      return this.parseReturn(tokens, start);
    }

    // Default: wrap as expression
    return {
      node: { type: 'Expression', value: token },
      nextIndex: start + 1,
    };
  }

  private parseDeclaration(
    tokens: string[],
    start: number
  ): { node: ASTNode; nextIndex: number } {
    const kind = tokens[start];
    const name = tokens[start + 1] ?? 'unknown';

    return {
      node: {
        type: 'Declaration',
        kind,
        name,
        children: [],
      },
      nextIndex: this.findStatementEnd(tokens, start),
    };
  }

  private parseIfStatement(
    tokens: string[],
    start: number
  ): { node: ASTNode; nextIndex: number } {
    return {
      node: {
        type: 'IfStatement',
        children: [],
      },
      nextIndex: this.findBlockEnd(tokens, start),
    };
  }

  private parseLoop(
    tokens: string[],
    start: number
  ): { node: ASTNode; nextIndex: number } {
    const kind = tokens[start];
    return {
      node: {
        type: kind === 'for' ? 'ForLoop' : 'WhileLoop',
        children: [],
      },
      nextIndex: this.findBlockEnd(tokens, start),
    };
  }

  private parseReturn(
    tokens: string[],
    start: number
  ): { node: ASTNode; nextIndex: number } {
    return {
      node: {
        type: 'ReturnStatement',
        children: [],
      },
      nextIndex: this.findStatementEnd(tokens, start),
    };
  }

  private findStatementEnd(tokens: string[], start: number): number {
    let i = start;
    while (i < tokens.length && tokens[i] !== ';' && tokens[i] !== '}') {
      i++;
    }
    return Math.min(i + 1, tokens.length);
  }

  private findBlockEnd(tokens: string[], start: number): number {
    let depth = 0;
    let i = start;

    while (i < tokens.length) {
      if (tokens[i] === '{') depth++;
      if (tokens[i] === '}') {
        depth--;
        if (depth === 0) return i + 1;
      }
      i++;
    }

    return tokens.length;
  }

  private extractSubtrees(
    ast: ASTNode,
    filePath: string,
    depth = 0
  ): Array<{ hash: string; node: ASTNode; occurrence: PatternOccurrence }> {
    const results: Array<{ hash: string; node: ASTNode; occurrence: PatternOccurrence }> = [];

    if (depth > this.config.maxDepth!) {
      return results;
    }

    // Add current node as potential pattern
    const hash = this.hashAST(ast);
    results.push({
      hash,
      node: ast,
      occurrence: {
        file: filePath,
        startLine: 1, // Simplified - would need source map in production
        endLine: 1,
        bindings: new Map(),
      },
    });

    // Recurse into children
    if (ast.children) {
      for (const child of ast.children) {
        results.push(...this.extractSubtrees(child, filePath, depth + 1));
      }
    }

    return results;
  }

  private hashAST(node: ASTNode): string {
    // Create a structural hash of the AST
    const parts: string[] = [node.type];

    if (node.kind) parts.push(String(node.kind));
    if (node.value !== undefined) parts.push(String(node.value));

    if (node.children) {
      for (const child of node.children) {
        parts.push(this.hashAST(child));
      }
    }

    return parts.join('|');
  }

  private hashToAST(hash: string): ASTNode | null {
    // Reconstruct AST from hash (simplified)
    const parts = hash.split('|');
    if (parts.length === 0) return null;

    return {
      type: parts[0],
      children: [],
    };
  }

  private isValidPatternSize(ast: ASTNode): boolean {
    const size = this.countNodes(ast);
    return size >= this.config.minSize! && size <= this.config.maxSize!;
  }

  private countNodes(ast: ASTNode): number {
    let count = 1;
    if (ast.children) {
      for (const child of ast.children) {
        count += this.countNodes(child);
      }
    }
    return count;
  }

  private computeScore(occurrences: number, ast: ASTNode): number {
    // Score based on occurrences and pattern complexity
    const size = this.countNodes(ast);
    // Higher occurrences and moderate size = better score
    return occurrences * Math.log2(size + 1);
  }
}

/**
 * Factory function to create a PatternMiner
 */
export function createPatternMiner(config?: PatternMinerConfig): PatternMiner {
  return new PatternMinerImpl(config);
}
