/**
 * Version Space
 * @module @nahisaho/musubix-synthesis
 * @description Efficient representation of candidate programs
 */

import type { Example, IDSL, IVersionSpace, Program } from '../types.js';

/**
 * Version space implementation
 */
export class VersionSpace implements IVersionSpace {
  private candidates: Program[];

  constructor(_dsl?: IDSL) {
    this.candidates = [];
  }

  /**
   * Add a program to the version space
   */
  add(program: Program): void {
    // Avoid duplicates
    if (!this.candidates.some((p) => this.programsEqual(p, program))) {
      this.candidates.push(program);
    }
  }

  /**
   * Refine version space with example
   */
  refine(example: Example, dsl: IDSL): IVersionSpace {
    const refined = new VersionSpace(dsl);

    for (const candidate of this.candidates) {
      if (this.satisfiesExample(candidate, example, dsl)) {
        refined.add(candidate);
      }
    }

    return refined;
  }

  /**
   * Check if version space has converged to single program
   */
  isConverged(): boolean {
    return this.candidates.length === 1;
  }

  /**
   * Get the single program if converged
   */
  getProgram(): Program | null {
    if (this.candidates.length === 1) {
      return this.candidates[0];
    }
    return null;
  }

  /**
   * Get number of candidates
   */
  size(): number {
    return this.candidates.length;
  }

  /**
   * Get candidates up to limit
   */
  getCandidates(limit?: number): Program[] {
    if (limit !== undefined) {
      return this.candidates.slice(0, limit);
    }
    return [...this.candidates];
  }

  /**
   * Check if program satisfies example
   */
  private satisfiesExample(
    program: Program,
    example: Example,
    dsl: IDSL
  ): boolean {
    try {
      const result = dsl.execute(program, example.input);
      return this.valuesEqual(result, example.output);
    } catch {
      return false;
    }
  }

  /**
   * Check if programs are equal
   */
  private programsEqual(a: Program, b: Program): boolean {
    return JSON.stringify(a.expression) === JSON.stringify(b.expression);
  }

  /**
   * Value equality check
   */
  private valuesEqual(a: unknown, b: unknown): boolean {
    if (a === b) return true;
    if (typeof a !== typeof b) return false;
    if (Array.isArray(a) && Array.isArray(b)) {
      if (a.length !== b.length) return false;
      return a.every((v, i) => this.valuesEqual(v, b[i]));
    }
    if (typeof a === 'object' && a !== null && b !== null) {
      return JSON.stringify(a) === JSON.stringify(b);
    }
    return false;
  }
}
