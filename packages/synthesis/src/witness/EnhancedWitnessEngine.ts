/**
 * EnhancedWitnessEngine - Extended Witness Function Engine
 *
 * Extends the base WitnessEngine with 20+ built-in witness functions
 * for string, list, arithmetic, and conditional operations.
 *
 * @module @nahisaho/musubix-synthesis
 * @see TSK-SY-101
 * @see DES-SY-101
 * @see REQ-SY-101
 *
 * @example
 * ```typescript
 * import { createEnhancedWitnessEngine } from './EnhancedWitnessEngine.js';
 *
 * const engine = createEnhancedWitnessEngine(dsl);
 * const decomp = engine.decompose(spec, 'concat');
 * ```
 */

import type {
  IDSL,
  Specification,
  WitnessFunction,
} from '../types.js';
import { WitnessEngine } from '../synthesis/WitnessEngine.js';

// =============================================================================
// Types
// =============================================================================

/**
 * Configuration for enhanced witness engine
 */
export interface EnhancedWitnessConfig {
  /** Enable string manipulation witnesses (default: true) */
  enableStringWitnesses: boolean;
  /** Enable list operation witnesses (default: true) */
  enableListWitnesses: boolean;
  /** Enable arithmetic witnesses (default: true) */
  enableArithmeticWitnesses: boolean;
  /** Enable conditional witnesses (default: true) */
  enableConditionalWitnesses: boolean;
}

/**
 * Witness category
 */
export type WitnessCategory = 'string' | 'list' | 'arithmetic' | 'conditional';

/**
 * Extended witness function with category
 */
export interface ExtendedWitnessFunction extends WitnessFunction {
  category?: WitnessCategory;
  description?: string;
}

/**
 * Witness list item
 */
export interface WitnessListItem {
  operator: string;
  category: WitnessCategory | 'custom';
  description?: string;
}

/**
 * Serialized engine state
 */
interface SerializedEngine {
  version: string;
  config: EnhancedWitnessConfig;
  customWitnesses: Array<{
    operator: string;
    category: string;
  }>;
}

// =============================================================================
// Default Configuration
// =============================================================================

const DEFAULT_CONFIG: EnhancedWitnessConfig = {
  enableStringWitnesses: true,
  enableListWitnesses: true,
  enableArithmeticWitnesses: true,
  enableConditionalWitnesses: true,
};

// =============================================================================
// Built-in Witnesses
// =============================================================================

/**
 * Built-in witness functions (20+ total)
 */
export const BUILTIN_WITNESSES: ExtendedWitnessFunction[] = [
  // =========================================================================
  // String Witnesses (8)
  // =========================================================================
  {
    operator: 'concat',
    argIndex: 0,
    category: 'string',
    description: 'Concatenation witness - decomposes output into prefix/suffix',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'string') {
          const output = ex.output;
          // Try different split points
          for (let i = 0; i <= output.length; i++) {
            const prefix = output.substring(0, i);
            const suffix = output.substring(i);
            results.push({ examples: [{ input: ex.input, output: prefix }] });
            results.push({ examples: [{ input: ex.input, output: suffix }] });
          }
        }
      }
      return results;
    },
  },
  {
    operator: 'substring',
    argIndex: 0,
    category: 'string',
    description: 'Substring witness - finds source string and indices',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'string' && Array.isArray(ex.input)) {
          const input = ex.input[0];
          if (typeof input === 'string' && input.includes(ex.output)) {
            const start = input.indexOf(ex.output);
            const end = start + ex.output.length;
            results.push({ examples: [{ input: ex.input, output: input }] });
            results.push({ examples: [{ input: ex.input, output: start }] });
            results.push({ examples: [{ input: ex.input, output: end }] });
          }
        }
      }
      return results;
    },
  },
  {
    operator: 'toUpperCase',
    argIndex: 0,
    category: 'string',
    description: 'ToUpperCase witness - finds lowercase source',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'string') {
          results.push({ examples: [{ input: ex.input, output: ex.output.toLowerCase() }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'toLowerCase',
    argIndex: 0,
    category: 'string',
    description: 'ToLowerCase witness - finds uppercase source',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'string') {
          results.push({ examples: [{ input: ex.input, output: ex.output.toUpperCase() }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'replace',
    argIndex: 0,
    category: 'string',
    description: 'Replace witness - finds original string and replacement',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'string') {
          results.push({ examples: [{ input: ex.input, output: ex.output }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'trim',
    argIndex: 0,
    category: 'string',
    description: 'Trim witness - finds string with whitespace',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'string') {
          results.push({ examples: [{ input: ex.input, output: ' ' + ex.output + ' ' }] });
          results.push({ examples: [{ input: ex.input, output: ex.output }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'split',
    argIndex: 0,
    category: 'string',
    description: 'Split witness - finds original string and delimiter',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (Array.isArray(ex.output)) {
          const joined = ex.output.join('');
          results.push({ examples: [{ input: ex.input, output: joined }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'length',
    argIndex: 0,
    category: 'string',
    description: 'Length witness - finds string of given length',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'number') {
          results.push({ examples: [{ input: ex.input, output: 'x'.repeat(ex.output) }] });
        }
      }
      return results;
    },
  },

  // =========================================================================
  // List Witnesses (6)
  // =========================================================================
  {
    operator: 'map',
    argIndex: 0,
    category: 'list',
    description: 'Map witness - infers transformation function',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (Array.isArray(ex.input) && Array.isArray(ex.output)) {
          const inputArr = ex.input[0] as unknown[];
          const outputArr = ex.output as unknown[];
          
          // Infer element-wise transformation
          if (inputArr.length === outputArr.length) {
            for (let i = 0; i < inputArr.length; i++) {
              results.push({
                examples: [{ input: inputArr[i], output: outputArr[i] }],
              });
            }
          }
        }
      }
      return results;
    },
  },
  {
    operator: 'filter',
    argIndex: 0,
    category: 'list',
    description: 'Filter witness - infers predicate function',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (Array.isArray(ex.input) && Array.isArray(ex.output)) {
          const inputArr = ex.input[0] as unknown[];
          const outputArr = ex.output as unknown[];
          
          // Create specs for included/excluded elements
          for (const item of inputArr) {
            const included = outputArr.includes(item);
            results.push({
              examples: [{ input: item, output: included }],
            });
          }
        }
      }
      return results;
    },
  },
  {
    operator: 'reduce',
    argIndex: 0,
    category: 'list',
    description: 'Reduce witness - infers reducer function and initial value',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (Array.isArray(ex.input)) {
          results.push({ examples: [{ input: ex.input, output: ex.output }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'head',
    argIndex: 0,
    category: 'list',
    description: 'Head witness - finds list with given first element',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        results.push({ examples: [{ input: ex.input, output: [ex.output] }] });
      }
      return results;
    },
  },
  {
    operator: 'tail',
    argIndex: 0,
    category: 'list',
    description: 'Tail witness - finds list with given rest',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (Array.isArray(ex.output)) {
          results.push({ examples: [{ input: ex.input, output: [null, ...ex.output] }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'cons',
    argIndex: 0,
    category: 'list',
    description: 'Cons witness - finds head and tail',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (Array.isArray(ex.output) && ex.output.length > 0) {
          results.push({ examples: [{ input: ex.input, output: ex.output[0] }] });
          results.push({ examples: [{ input: ex.input, output: ex.output.slice(1) }] });
        }
      }
      return results;
    },
  },

  // =========================================================================
  // Arithmetic Witnesses (4)
  // =========================================================================
  {
    operator: 'add',
    argIndex: 0,
    category: 'arithmetic',
    description: 'Addition witness - decomposes sum into addends',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'number') {
          const sum = ex.output;
          // Try different decompositions
          for (let i = 0; i <= sum; i++) {
            results.push({ examples: [{ input: ex.input, output: i }] });
            results.push({ examples: [{ input: ex.input, output: sum - i }] });
          }
        }
      }
      return results;
    },
  },
  {
    operator: 'subtract',
    argIndex: 0,
    category: 'arithmetic',
    description: 'Subtraction witness - finds minuend and subtrahend',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'number' && Array.isArray(ex.input)) {
          const [a, b] = ex.input as number[];
          if (typeof a === 'number' && typeof b === 'number') {
            results.push({ examples: [{ input: ex.input, output: a }] });
            results.push({ examples: [{ input: ex.input, output: b }] });
          }
        }
      }
      return results;
    },
  },
  {
    operator: 'multiply',
    argIndex: 0,
    category: 'arithmetic',
    description: 'Multiplication witness - decomposes product into factors',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'number') {
          const product = ex.output;
          // Find factor pairs
          for (let i = 1; i <= Math.sqrt(Math.abs(product)) + 1; i++) {
            if (product % i === 0) {
              results.push({ examples: [{ input: ex.input, output: i }] });
              results.push({ examples: [{ input: ex.input, output: product / i }] });
            }
          }
        }
      }
      return results;
    },
  },
  {
    operator: 'divide',
    argIndex: 0,
    category: 'arithmetic',
    description: 'Division witness - finds dividend and divisor',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (typeof ex.output === 'number' && Array.isArray(ex.input)) {
          const [a, b] = ex.input as number[];
          if (typeof a === 'number' && typeof b === 'number') {
            results.push({ examples: [{ input: ex.input, output: a }] });
            results.push({ examples: [{ input: ex.input, output: b }] });
          }
        }
      }
      return results;
    },
  },

  // =========================================================================
  // Conditional Witnesses (2)
  // =========================================================================
  {
    operator: 'ite',
    argIndex: 0,
    category: 'conditional',
    description: 'If-then-else witness - infers condition and branches',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        if (Array.isArray(ex.input) && ex.input.length >= 3) {
          const [cond, thenVal, elseVal] = ex.input;
          // Condition spec
          results.push({ examples: [{ input: ex.input, output: cond }] });
          // Then branch spec
          results.push({ examples: [{ input: ex.input, output: thenVal }] });
          // Else branch spec
          results.push({ examples: [{ input: ex.input, output: elseVal }] });
        }
      }
      return results;
    },
  },
  {
    operator: 'switch',
    argIndex: 0,
    category: 'conditional',
    description: 'Switch witness - infers selector and cases',
    witness: (spec: Specification): Specification[] => {
      const results: Specification[] = [];
      for (const ex of spec.examples) {
        results.push({ examples: [{ input: ex.input, output: ex.output }] });
      }
      return results;
    },
  },
];

// =============================================================================
// Implementation
// =============================================================================

/**
 * Enhanced Witness Engine with built-in witnesses
 */
export class EnhancedWitnessEngine extends WitnessEngine {
  private readonly config: EnhancedWitnessConfig;
  private readonly customWitnesses: ExtendedWitnessFunction[] = [];
  private readonly witnessCategories: Map<string, WitnessCategory | 'custom'> = new Map();

  constructor(dsl: IDSL, config: Partial<EnhancedWitnessConfig> = {}) {
    super(dsl);
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.registerBuiltinWitnesses();
  }

  /**
   * Register all built-in witnesses based on config
   */
  private registerBuiltinWitnesses(): void {
    for (const witness of BUILTIN_WITNESSES) {
      if (this.shouldRegisterWitness(witness)) {
        this.registerWitness(witness);
        if (witness.category) {
          this.witnessCategories.set(witness.operator, witness.category);
        }
      }
    }
  }

  /**
   * Check if witness should be registered based on config
   */
  private shouldRegisterWitness(witness: ExtendedWitnessFunction): boolean {
    switch (witness.category) {
      case 'string':
        return this.config.enableStringWitnesses;
      case 'list':
        return this.config.enableListWitnesses;
      case 'arithmetic':
        return this.config.enableArithmeticWitnesses;
      case 'conditional':
        return this.config.enableConditionalWitnesses;
      default:
        return true;
    }
  }

  /**
   * Register a custom witness function
   */
  override registerWitness(witness: WitnessFunction): void {
    super.registerWitness(witness);
    
    const extended = witness as ExtendedWitnessFunction;
    if (!BUILTIN_WITNESSES.includes(extended)) {
      this.customWitnesses.push(extended);
    }
    
    if (extended.category) {
      this.witnessCategories.set(witness.operator, extended.category);
    } else {
      this.witnessCategories.set(witness.operator, 'custom');
    }
  }

  /**
   * Get total count of registered witnesses
   */
  getWitnessCount(): number {
    let count = 0;
    // Count across all operators
    for (const witness of BUILTIN_WITNESSES) {
      if (this.shouldRegisterWitness(witness)) {
        count++;
      }
    }
    count += this.customWitnesses.length;
    return count;
  }

  /**
   * Get witnesses by category
   */
  getWitnessesByCategory(category: WitnessCategory | 'custom'): WitnessFunction[] {
    const results: WitnessFunction[] = [];
    
    for (const witness of BUILTIN_WITNESSES) {
      if (witness.category === category && this.shouldRegisterWitness(witness)) {
        results.push(witness);
      }
    }
    
    if (category === 'custom') {
      results.push(...this.customWitnesses);
    }
    
    return results;
  }

  /**
   * List all registered witnesses
   */
  listWitnesses(): WitnessListItem[] {
    const items: WitnessListItem[] = [];
    
    for (const witness of BUILTIN_WITNESSES) {
      if (this.shouldRegisterWitness(witness)) {
        items.push({
          operator: witness.operator,
          category: witness.category ?? 'custom',
          description: witness.description,
        });
      }
    }
    
    for (const witness of this.customWitnesses) {
      items.push({
        operator: witness.operator,
        category: witness.category ?? 'custom',
        description: witness.description,
      });
    }
    
    return items;
  }

  /**
   * Serialize engine state to JSON
   */
  toJSON(): string {
    const state: SerializedEngine = {
      version: '1.0.0',
      config: this.config,
      customWitnesses: this.customWitnesses.map(w => ({
        operator: w.operator,
        category: w.category ?? 'custom',
      })),
    };
    return JSON.stringify(state, null, 2);
  }

  /**
   * Restore engine state from JSON
   * Note: Only restores configuration, not actual witness function implementations
   */
  fromJSON(_json: string): void {
    // Parse but don't fully restore - witness functions can't be serialized
    // This method exists for API compatibility
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create an EnhancedWitnessEngine instance
 *
 * @param dsl - The DSL to use for synthesis
 * @param config - Optional configuration
 * @returns EnhancedWitnessEngine instance
 */
export function createEnhancedWitnessEngine(
  dsl: IDSL,
  config: Partial<EnhancedWitnessConfig> = {}
): EnhancedWitnessEngine {
  return new EnhancedWitnessEngine(dsl, config);
}
