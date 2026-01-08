/**
 * Witness Engine
 * @module @nahisaho/musubix-synthesis
 * @description Deductive synthesis with witness functions
 * Traces to: REQ-SYN-002 (Witness Functions)
 */

import type {
  DecomposedSpec,
  IDSL,
  IWitnessEngine,
  Program,
  Specification,
  SynthesisOptions,
  SynthesisResult,
  WitnessFunction,
} from '../types.js';

/**
 * Witness engine implementation
 */
export class WitnessEngine implements IWitnessEngine {
  private readonly dsl: IDSL;
  private readonly witnesses: Map<string, WitnessFunction[]>;

  constructor(dsl: IDSL) {
    this.dsl = dsl;
    this.witnesses = new Map();
  }

  /**
   * Register a witness function
   */
  register(witness: WitnessFunction): void {
    this.registerWitness(witness);
  }

  /**
   * Register a witness function (alias for tests)
   */
  registerWitness(witness: WitnessFunction): void {
    const existing = this.witnesses.get(witness.operator) ?? [];
    existing.push(witness);
    this.witnesses.set(witness.operator, existing);
  }

  /**
   * Get all witness functions for an operator
   */
  getWitnesses(operator: string): WitnessFunction[] {
    return this.witnesses.get(operator) ?? [];
  }

  /**
   * Clear all registered witnesses
   */
  clearWitnesses(): void {
    this.witnesses.clear();
  }

  /**
   * Decompose a specification using witness functions
   */
  decompose(spec: Specification, operator: string): DecomposedSpec {
    const witnesses = this.witnesses.get(operator);
    
    if (!witnesses || witnesses.length === 0) {
      return {
        operator,
        argSpecs: [],
        confidence: 0,
      };
    }

    const argSpecs: Specification[] = [];

    // Apply each witness function
    for (const witness of witnesses) {
      const witnessFunc = witness.witness ?? witness.inverse;
      if (witnessFunc) {
        const specs = witnessFunc(spec);
        argSpecs.push(...specs);
      }
    }

    return {
      operator,
      argSpecs,
      confidence: this.computeConfidence(argSpecs, spec),
    };
  }

  /**
   * Synthesize using witness functions
   */
  async synthesizeWithWitness(
    spec: Specification,
    options?: SynthesisOptions
  ): Promise<SynthesisResult> {
    const startTime = Date.now();
    const maxDepth = options?.maxDepth ?? 3;
    let searchNodes = 0;

    // Try to synthesize using deductive approach
    const program = await this.synthesizeDeductivelyInternal(spec, maxDepth, () => {
      searchNodes++;
    });

    const duration = Date.now() - startTime;

    if (program) {
      return {
        success: true,
        program,
        duration,
        synthesisTime: duration,
        searchNodes,
        candidatesExplored: searchNodes,
        pruned: 0,
      };
    }

    return {
      success: false,
      duration,
      synthesisTime: duration,
      searchNodes,
      candidatesExplored: searchNodes,
      pruned: 0,
    };
  }

  /**
   * Synthesize deductively using witness functions (interface method)
   */
  async synthesizeDeductively(
    _dsl: IDSL,
    spec: Specification
  ): Promise<Program | null> {
    return this.synthesizeDeductivelyInternal(spec, 3, () => {});
  }

  /**
   * Internal deductive synthesis with depth limit
   */
  private async synthesizeDeductivelyInternal(
    spec: Specification,
    maxDepth: number,
    onNode: () => void
  ): Promise<Program | null> {
    onNode();

    if (maxDepth <= 0) {
      return null;
    }

    // Base case: check if constant satisfies spec
    for (const [, constant] of this.dsl.constants) {
      if (this.constantSatisfiesSpec(constant.value, spec)) {
        return {
          id: `const-${Date.now()}`,
          expression: { kind: 'constant', name: constant.name },
        };
      }
    }

    // Check if input directly satisfies spec
    if (this.inputSatisfiesSpec(spec)) {
      return {
        id: `input-${Date.now()}`,
        expression: { kind: 'variable', name: 'input' },
      };
    }

    // Try each operator with witnesses
    for (const [, operator] of this.dsl.operators) {
      const decomp = this.decompose(spec, operator.name);
      
      if (decomp.argSpecs.length > 0) {
        // Try to synthesize each argument
        const argPrograms: Program[] = [];
        let allSolved = true;

        for (const argSpec of decomp.argSpecs) {
          const argProgram = await this.synthesizeDeductivelyInternal(
            argSpec,
            maxDepth - 1,
            onNode
          );
          if (argProgram) {
            argPrograms.push(argProgram);
          } else {
            allSolved = false;
            break;
          }
        }

        if (allSolved && argPrograms.length === operator.inputTypes.length) {
          return {
            id: `deductive-${Date.now()}`,
            expression: {
              kind: 'application',
              operator: operator.name,
              args: argPrograms.map((p) => p.expression),
            },
          };
        }
      }
    }

    return null;
  }

  /**
   * Compute confidence of decomposition
   */
  private computeConfidence(
    argSpecs: Specification[],
    _outputSpec: Specification
  ): number {
    if (argSpecs.length === 0) return 0;
    // Higher confidence for more constrained specs
    let confidence = 1.0;
    for (const spec of argSpecs) {
      confidence *= 1 / (1 + spec.examples.length * 0.1);
    }
    return confidence;
  }

  /**
   * Check if input directly satisfies spec
   */
  private inputSatisfiesSpec(spec: Specification): boolean {
    for (const example of spec.examples) {
      if (!this.valuesEqual(example.input, example.output)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Check if constant satisfies spec
   */
  private constantSatisfiesSpec(value: unknown, spec: Specification): boolean {
    for (const example of spec.examples) {
      if (!this.valuesEqual(value, example.output)) {
        return false;
      }
    }
    return true;
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
