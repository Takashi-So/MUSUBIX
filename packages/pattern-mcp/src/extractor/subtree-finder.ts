/**
 * @fileoverview Repeated subtree detection in AST
 * @traceability TSK-PATTERN-001, REQ-PATTERN-001-F002
 */

import type { ASTNode } from '../types.js';

/**
 * Subtree candidate with frequency information
 */
export interface SubtreeCandidate {
  ast: ASTNode;
  hash: string;
  frequency: number;
  depth: number;
  locations: SubtreeLocation[];
}

/**
 * Location of a subtree in source
 */
export interface SubtreeLocation {
  startRow: number;
  startColumn: number;
  endRow: number;
  endColumn: number;
}

/**
 * Subtree finder options
 */
export interface SubtreeFinderOptions {
  /** Minimum frequency to be considered a pattern */
  minFrequency: number;
  /** Minimum subtree depth to consider */
  minDepth: number;
  /** Maximum subtree depth to consider */
  maxDepth: number;
  /** Node types to ignore */
  ignoreTypes: string[];
}

/**
 * Finds repeated subtrees in an AST
 * 
 * @description
 * Uses structural hashing to identify repeated code patterns.
 * Implements anti-unification to find common structures.
 */
export class SubtreeFinder {
  private options: SubtreeFinderOptions;

  constructor(options: Partial<SubtreeFinderOptions> = {}) {
    this.options = {
      minFrequency: options.minFrequency ?? 2,
      minDepth: options.minDepth ?? 2,
      maxDepth: options.maxDepth ?? 10,
      ignoreTypes: options.ignoreTypes ?? [
        'EndOfFileToken',
        'SemicolonToken',
        'OpenBraceToken',
        'CloseBraceToken',
        'OpenParenToken',
        'CloseParenToken',
      ],
    };
  }

  /**
   * Find all repeated subtrees in AST
   */
  find(ast: ASTNode): SubtreeCandidate[] {
    const subtreeMap = new Map<string, SubtreeCandidate>();

    this.traverse(ast, subtreeMap, 0);

    // Filter by minimum frequency and depth
    const candidates = Array.from(subtreeMap.values())
      .filter(c => 
        c.frequency >= this.options.minFrequency &&
        c.depth >= this.options.minDepth
      );

    // Remove subsumed patterns (smaller patterns contained in larger ones)
    return this.removeSubsumed(candidates);
  }

  /**
   * Traverse AST and collect subtree hashes
   */
  private traverse(
    node: ASTNode,
    subtreeMap: Map<string, SubtreeCandidate>,
    depth: number
  ): { hash: string; depth: number } {
    // Skip ignored node types
    if (this.options.ignoreTypes.includes(node.type)) {
      return { hash: '', depth: 0 };
    }

    // Skip if max depth exceeded
    if (depth > this.options.maxDepth) {
      return { hash: this.hashLeaf(node), depth: 1 };
    }

    // Calculate children hashes
    const childResults = node.children.map(child =>
      this.traverse(child, subtreeMap, depth + 1)
    );

    // Build hash for this subtree
    const hash = this.hashSubtree(node, childResults.map(r => r.hash));
    const subtreeDepth = 1 + Math.max(0, ...childResults.map(r => r.depth));

    // Skip trivial subtrees
    if (subtreeDepth < this.options.minDepth) {
      return { hash, depth: subtreeDepth };
    }

    // Register or update in map
    const location: SubtreeLocation = {
      startRow: node.startPosition.row,
      startColumn: node.startPosition.column,
      endRow: node.endPosition.row,
      endColumn: node.endPosition.column,
    };

    const existing = subtreeMap.get(hash);
    if (existing) {
      existing.frequency++;
      existing.locations.push(location);
    } else {
      subtreeMap.set(hash, {
        ast: node,
        hash,
        frequency: 1,
        depth: subtreeDepth,
        locations: [location],
      });
    }

    return { hash, depth: subtreeDepth };
  }

  /**
   * Hash a leaf node
   */
  private hashLeaf(node: ASTNode): string {
    // Include type and optionally value for identifiers
    return `L:${node.type}`;
  }

  /**
   * Hash a subtree
   */
  private hashSubtree(node: ASTNode, childHashes: string[]): string {
    const childPart = childHashes.filter(h => h).join(',');
    return `N:${node.type}[${childPart}]`;
  }

  /**
   * Remove subsumed patterns (patterns contained in larger patterns)
   */
  private removeSubsumed(candidates: SubtreeCandidate[]): SubtreeCandidate[] {
    // Sort by depth (largest first)
    const sorted = [...candidates].sort((a, b) => b.depth - a.depth);
    const result: SubtreeCandidate[] = [];
    const seenHashes = new Set<string>();

    for (const candidate of sorted) {
      // Check if this subtree's locations are all covered by a larger pattern
      const isSubsumed = this.isSubsumedByAny(candidate, result);
      
      if (!isSubsumed && !seenHashes.has(candidate.hash)) {
        result.push(candidate);
        seenHashes.add(candidate.hash);
      }
    }

    return result;
  }

  /**
   * Check if candidate is subsumed by any existing pattern
   */
  private isSubsumedByAny(
    candidate: SubtreeCandidate,
    existing: SubtreeCandidate[]
  ): boolean {
    for (const pattern of existing) {
      // Skip if same or smaller depth
      if (pattern.depth <= candidate.depth) continue;

      // Check if candidate's hash appears in pattern's AST
      if (this.containsHash(pattern.ast, candidate.hash)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Check if AST contains a subtree with given hash
   */
  private containsHash(ast: ASTNode, targetHash: string): boolean {
    const currentHash = this.computeHash(ast);
    if (currentHash === targetHash) return true;

    for (const child of ast.children) {
      if (this.containsHash(child, targetHash)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Compute hash for AST node (for containment check)
   */
  private computeHash(node: ASTNode): string {
    const childHashes = node.children.map(c => this.computeHash(c));
    return this.hashSubtree(node, childHashes);
  }
}
