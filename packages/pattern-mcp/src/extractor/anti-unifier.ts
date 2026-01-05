/**
 * @fileoverview Anti-unification for pattern abstraction
 * @traceability TSK-PATTERN-001, REQ-PATTERN-001-F003
 */

import type { ASTNode, PatternHole } from '../types.js';

/**
 * Anti-unification result
 */
export interface AntiUnificationResult {
  /** Generalized pattern AST */
  pattern: ASTNode;
  /** Holes (variable parts) in the pattern */
  holes: PatternHole[];
  /** Substitutions for each input AST */
  substitutions: Map<string, ASTNode>[];
}

/**
 * Anti-unifier for AST patterns
 * 
 * @description
 * Computes the most specific generalization (anti-unification)
 * of two or more AST structures. Creates holes for variable parts.
 */
export class AntiUnifier {
  private holeCounter = 0;

  /**
   * Anti-unify two AST nodes
   */
  antiUnify(ast1: ASTNode, ast2: ASTNode): AntiUnificationResult {
    this.holeCounter = 0;
    const holes: PatternHole[] = [];
    const substitutions: Map<string, ASTNode>[] = [new Map(), new Map()];

    const pattern = this.antiUnifyNodes(ast1, ast2, holes, substitutions);

    return {
      pattern,
      holes,
      substitutions,
    };
  }

  /**
   * Anti-unify multiple AST nodes
   */
  antiUnifyAll(asts: ASTNode[]): AntiUnificationResult {
    if (asts.length === 0) {
      throw new Error('Cannot anti-unify empty array');
    }
    if (asts.length === 1) {
      return {
        pattern: this.cloneNode(asts[0]),
        holes: [],
        substitutions: [new Map()],
      };
    }

    // Pairwise anti-unification
    let result = this.antiUnify(asts[0], asts[1]);
    
    for (let i = 2; i < asts.length; i++) {
      const nextResult = this.antiUnify(result.pattern, asts[i]);
      result = {
        pattern: nextResult.pattern,
        holes: [...result.holes, ...nextResult.holes],
        substitutions: [...result.substitutions, nextResult.substitutions[1]],
      };
    }

    return result;
  }

  /**
   * Anti-unify two nodes recursively
   */
  private antiUnifyNodes(
    node1: ASTNode,
    node2: ASTNode,
    holes: PatternHole[],
    substitutions: Map<string, ASTNode>[]
  ): ASTNode {
    // If types differ, create a hole
    if (node1.type !== node2.type) {
      return this.createHole(node1, node2, holes, substitutions);
    }

    // If values differ (for identifiers/literals), create a hole
    if (node1.value !== node2.value) {
      if (node1.value !== undefined || node2.value !== undefined) {
        return this.createHoleForValue(node1, node2, holes, substitutions);
      }
    }

    // If children count differs, create a hole
    if (node1.children.length !== node2.children.length) {
      return this.createHole(node1, node2, holes, substitutions);
    }

    // Recursively anti-unify children
    const children: ASTNode[] = [];
    for (let i = 0; i < node1.children.length; i++) {
      children.push(
        this.antiUnifyNodes(
          node1.children[i],
          node2.children[i],
          holes,
          substitutions
        )
      );
    }

    return {
      type: node1.type,
      children,
      value: node1.value,
      startPosition: { row: 0, column: 0 },
      endPosition: { row: 0, column: 0 },
    };
  }

  /**
   * Create a hole node for differing structures
   */
  private createHole(
    node1: ASTNode,
    node2: ASTNode,
    holes: PatternHole[],
    substitutions: Map<string, ASTNode>[]
  ): ASTNode {
    const holeId = `hole_${this.holeCounter++}`;
    
    holes.push({
      id: holeId,
      type: 'any',
      constraints: [node1.type, node2.type],
    });

    substitutions[0].set(holeId, node1);
    substitutions[1].set(holeId, node2);

    return {
      type: 'Hole',
      children: [],
      value: holeId,
      startPosition: { row: 0, column: 0 },
      endPosition: { row: 0, column: 0 },
    };
  }

  /**
   * Create a hole for differing values (identifiers, literals)
   */
  private createHoleForValue(
    node1: ASTNode,
    node2: ASTNode,
    holes: PatternHole[],
    substitutions: Map<string, ASTNode>[]
  ): ASTNode {
    const holeId = `hole_${this.holeCounter++}`;
    
    holes.push({
      id: holeId,
      type: node1.type,
      constraints: node1.value && node2.value 
        ? [`value1:${node1.value}`, `value2:${node2.value}`]
        : undefined,
    });

    substitutions[0].set(holeId, node1);
    substitutions[1].set(holeId, node2);

    return {
      type: 'Hole',
      children: [],
      value: holeId,
      startPosition: { row: 0, column: 0 },
      endPosition: { row: 0, column: 0 },
    };
  }

  /**
   * Clone an AST node
   */
  private cloneNode(node: ASTNode): ASTNode {
    return {
      type: node.type,
      children: node.children.map(c => this.cloneNode(c)),
      value: node.value,
      startPosition: { ...node.startPosition },
      endPosition: { ...node.endPosition },
    };
  }

  /**
   * Calculate similarity between two patterns (0-1)
   */
  calculateSimilarity(pattern1: ASTNode, pattern2: ASTNode): number {
    const result = this.antiUnify(pattern1, pattern2);
    
    const patternSize = this.countNodes(result.pattern);
    const avgInputSize = (this.countNodes(pattern1) + this.countNodes(pattern2)) / 2;
    const holeCount = result.holes.length;

    // Similarity = (pattern nodes - holes) / average input size
    return Math.max(0, (patternSize - holeCount) / avgInputSize);
  }

  /**
   * Count nodes in AST
   */
  private countNodes(node: ASTNode): number {
    let count = 1;
    for (const child of node.children) {
      count += this.countNodes(child);
    }
    return count;
  }

  /**
   * Reset hole counter (for testing)
   */
  resetCounter(): void {
    this.holeCounter = 0;
  }
}
