/**
 * PBE Synthesizer
 * @module @nahisaho/musubix-synthesis
 * @description Programming by Example synthesizer
 * Traces to: REQ-SYN-003 (PBE Synthesis)
 */

import type {
  Example,
  IDSL,
  IPBESynthesizer,
  Program,
  Specification,
  SynthesisOptions,
  SynthesisResult,
} from '../types.js';
import { SynthesisTimeoutError } from '../errors.js';
import { Enumerator, resetProgramIdCounter } from './Enumerator.js';

/**
 * Default synthesis options
 */
const DEFAULT_OPTIONS: Required<SynthesisOptions> = {
  maxDepth: 5,
  maxCost: 20,
  timeout: 30000,
  maxCandidates: 100,
  useNeuralGuidance: false,
  pruneThreshold: 0.1,
};

/**
 * PBE Synthesizer implementation
 */
export class PBESynthesizer implements IPBESynthesizer {
  private searchNodes: number;
  private pruned: number;
  private lastDsl: IDSL | null;

  constructor() {
    this.searchNodes = 0;
    this.pruned = 0;
    this.lastDsl = null;
  }

  /**
   * Synthesize a program from specification
   */
  async synthesize(
    spec: Specification,
    dsl: IDSL,
    options?: SynthesisOptions
  ): Promise<SynthesisResult> {
    const opts = { ...DEFAULT_OPTIONS, ...options };
    const startTime = Date.now();
    this.searchNodes = 0;
    this.pruned = 0;
    this.lastDsl = dsl;

    // Reset ID counter for consistent test results
    resetProgramIdCounter();

    const candidates: Program[] = [];
    const enumerator = new Enumerator(dsl);

    try {
      // Enumerate programs
      const enumeration = enumerator.enumerateForSpec(spec, {
        maxDepth: opts.maxDepth,
        maxCost: opts.maxCost,
        yieldInterval: 100,
      });

      for await (const program of enumeration) {
        // Check timeout
        if (Date.now() - startTime > opts.timeout) {
          throw new SynthesisTimeoutError(opts.timeout);
        }

        this.searchNodes++;

        // Check if program satisfies all examples
        if (this.satisfiesAllExamples(program, spec.examples, dsl)) {
          candidates.push(program);

          // Return immediately if we have a good solution
          if (candidates.length >= opts.maxCandidates) {
            break;
          }
        } else {
          this.pruned++;
        }
      }

      const duration = Date.now() - startTime;

      if (candidates.length > 0) {
        // Sort by cost
        candidates.sort((a, b) => (a.cost ?? 0) - (b.cost ?? 0));

        return {
          success: true,
          program: candidates[0],
          candidates,
          duration,
          synthesisTime: duration,
          searchNodes: this.searchNodes,
          candidatesExplored: this.searchNodes,
          pruned: this.pruned,
        };
      }

      return {
        success: false,
        candidates: [],
        duration,
        synthesisTime: duration,
        searchNodes: this.searchNodes,
        candidatesExplored: this.searchNodes,
        pruned: this.pruned,
        error: 'No program found that satisfies all examples',
      };
    } catch (error) {
      if (error instanceof SynthesisTimeoutError) {
        const duration = Date.now() - startTime;
        return {
          success: candidates.length > 0,
          program: candidates[0],
          candidates,
          duration,
          synthesisTime: duration,
          searchNodes: this.searchNodes,
          candidatesExplored: this.searchNodes,
          pruned: this.pruned,
          error: candidates.length > 0 ? undefined : 'Synthesis timed out',
        };
      }
      throw error;
    }
  }

  /**
   * Get candidates from last synthesis
   */
  getCandidates(spec: Specification, dsl: IDSL, limit?: number): Program[] {
    // Simple enumeration-based candidate generation
    const enumerator = new Enumerator(dsl);
    const programs = enumerator.enumerate({ maxDepth: 3, maxPrograms: limit ?? 10 });
    
    // Filter programs that satisfy at least one example
    return programs.filter((p) => {
      try {
        const firstExample = spec.examples[0];
        if (!firstExample) return true;
        const result = dsl.execute(p, firstExample.input as Record<string, unknown>);
        return this.valuesEqual(result, firstExample.output);
      } catch {
        return false;
      }
    }).slice(0, limit ?? 10);
  }

  /**
   * Disambiguate candidates with additional example
   */
  disambiguate(candidates: Program[], example: Example): Program[] {
    if (!this.lastDsl) return candidates;
    
    return candidates.filter((p) => {
      try {
        const result = this.lastDsl!.execute(p, example.input as Record<string, unknown>);
        return this.valuesEqual(result, example.output);
      } catch {
        return false;
      }
    });
  }

  /**
   * Check if program satisfies all examples
   */
  private satisfiesAllExamples(
    program: Program,
    examples: Example[],
    dsl: IDSL
  ): boolean {
    for (const example of examples) {
      try {
        const result = dsl.execute(program, example.input as Record<string, unknown>);
        if (!this.valuesEqual(result, example.output)) {
          return false;
        }
      } catch {
        return false;
      }
    }
    return true;
  }

  /**
   * Check value equality
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
