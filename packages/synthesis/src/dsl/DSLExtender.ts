/**
 * DSLExtender
 * @module @nahisaho/musubix-synthesis
 * @description DSL grammar extension capabilities
 * Traces to: TSK-SY-104, DES-SY-104, REQ-SY-104
 */

/**
 * DSL expressiveness gap
 */
export interface DSLGap {
  type: 'missing-operator' | 'type-conversion' | 'composition';
  severity: 'low' | 'medium' | 'high';
  description: string;
  suggestedFix?: string;
}

/**
 * Operator suggestion
 */
export interface OperatorSuggestion {
  name: string;
  signature: string;
  confidence: number;
  description: string;
}

/**
 * Operator validation result
 */
export interface OperatorValidationResult {
  valid: boolean;
  error?: string;
}

/**
 * Example input/output pair
 */
export interface Example {
  input: unknown;
  output: unknown;
}

/**
 * Configuration for DSL extender
 */
export interface DSLExtenderConfig {
  maxSuggestions: number;
  minConfidence: number;
}

/**
 * DSL extender interface
 */
export interface DSLExtender {
  /**
   * Analyze gap between DSL capabilities and required transformation
   */
  analyzeGap(examples: Example[], dslOperators: string[]): DSLGap[];

  /**
   * Suggest operators to fill gaps
   */
  suggestOperators(examples: Example[]): OperatorSuggestion[];

  /**
   * Generate code for suggested operator
   */
  generateOperatorCode(suggestion: OperatorSuggestion): string;

  /**
   * Get list of known operators
   */
  getAvailableOperators(): string[];

  /**
   * Get operators grouped by category
   */
  getOperatorCategories(): Record<string, string[]>;

  /**
   * Validate an operator implementation
   */
  validateOperator(
    name: string,
    signature: string,
    implementation: (...args: unknown[]) => unknown
  ): OperatorValidationResult;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: DSLExtenderConfig = {
  maxSuggestions: 5,
  minConfidence: 0.5,
};

/**
 * Known operator database
 */
const KNOWN_OPERATORS: Record<string, string[]> = {
  string: [
    'uppercase',
    'lowercase',
    'concat',
    'substring',
    'trim',
    'split',
    'join',
    'replace',
    'charAt',
    'length',
  ],
  array: [
    'map',
    'filter',
    'reduce',
    'sum',
    'length',
    'head',
    'tail',
    'reverse',
    'sort',
    'flatten',
  ],
  number: [
    'add',
    'subtract',
    'multiply',
    'divide',
    'modulo',
    'abs',
    'floor',
    'ceil',
    'round',
  ],
  conversion: [
    'toString',
    'toNumber',
    'toBoolean',
    'parseFloat',
    'parseInt',
  ],
};

/**
 * Pattern-to-operator mapping
 */
interface TransformationPattern {
  pattern: (input: unknown, output: unknown) => boolean;
  operator: string;
  signature: string;
  confidence: number;
}

const TRANSFORMATION_PATTERNS: TransformationPattern[] = [
  {
    pattern: (i, o) => typeof i === 'string' && typeof o === 'string' && 
      o === (i as string).toUpperCase(),
    operator: 'uppercase',
    signature: 'string -> string',
    confidence: 0.95,
  },
  {
    pattern: (i, o) => typeof i === 'string' && typeof o === 'string' && 
      o === (i as string).toLowerCase(),
    operator: 'lowercase',
    signature: 'string -> string',
    confidence: 0.95,
  },
  {
    pattern: (i, o) => typeof i === 'string' && typeof o === 'string' &&
      isTitleCase(i as string, o as string),
    operator: 'titleCase',
    signature: 'string -> string',
    confidence: 0.85,
  },
  {
    pattern: (i, o) => Array.isArray(i) && typeof o === 'number' &&
      (i as number[]).reduce((a: number, b: number) => a + b, 0) === o,
    operator: 'sum',
    signature: 'number[] -> number',
    confidence: 0.9,
  },
  {
    pattern: (i, o) => typeof i === 'string' && typeof o === 'number' &&
      Number(i) === o,
    operator: 'toNumber',
    signature: 'string -> number',
    confidence: 0.9,
  },
  {
    pattern: (i, o) => typeof i === 'number' && typeof o === 'string' &&
      String(i) === o,
    operator: 'toString',
    signature: 'number -> string',
    confidence: 0.9,
  },
  {
    pattern: (i, o) => Array.isArray(i) && Array.isArray(o) &&
      (i as number[]).length === (o as number[]).length,
    operator: 'map',
    signature: '(a -> b) -> [a] -> [b]',
    confidence: 0.7,
  },
];

/**
 * Check if output is title case of input
 */
function isTitleCase(input: string, output: string): boolean {
  const expected = input.split(' ')
    .map(word => word.charAt(0).toUpperCase() + word.slice(1).toLowerCase())
    .join(' ');
  return output === expected;
}

/**
 * Default DSL extender implementation
 */
class DefaultDSLExtender implements DSLExtender {
  private readonly config: DSLExtenderConfig;

  constructor(config: DSLExtenderConfig = DEFAULT_CONFIG) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  analyzeGap(examples: Example[], dslOperators: string[]): DSLGap[] {
    const gaps: DSLGap[] = [];
    const operatorSet = new Set(dslOperators.map(o => o.toLowerCase()));

    for (const example of examples) {
      // Analyze type transformations
      const inputType = this.detectType(example.input);
      const outputType = this.detectType(example.output);

      if (inputType !== outputType) {
        const conversionOp = this.findConversionOperator(inputType, outputType);
        if (conversionOp && !operatorSet.has(conversionOp.toLowerCase())) {
          gaps.push({
            type: 'type-conversion',
            severity: 'high',
            description: `Missing ${inputType} to ${outputType} conversion operator (e.g., ${conversionOp})`,
            suggestedFix: `Add ${conversionOp} operator`,
          });
        }
      }

      // Analyze required operators
      const requiredOps = this.detectRequiredOperators(example);
      for (const op of requiredOps) {
        if (!operatorSet.has(op.toLowerCase())) {
          gaps.push({
            type: 'missing-operator',
            severity: 'medium',
            description: `Missing operator: ${op} (may need ${op} or reduce for this transformation)`,
            suggestedFix: `Add ${op} operator`,
          });
        }
      }
    }

    // Deduplicate gaps
    const seen = new Set<string>();
    return gaps.filter(g => {
      const key = `${g.type}:${g.description}`;
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  }

  suggestOperators(examples: Example[]): OperatorSuggestion[] {
    const suggestions: OperatorSuggestion[] = [];

    for (const pattern of TRANSFORMATION_PATTERNS) {
      let matchCount = 0;
      for (const example of examples) {
        if (pattern.pattern(example.input, example.output)) {
          matchCount++;
        }
      }

      if (matchCount > 0) {
        const confidence = (matchCount / examples.length) * pattern.confidence;
        if (confidence >= this.config.minConfidence) {
          suggestions.push({
            name: pattern.operator,
            signature: pattern.signature,
            confidence,
            description: `Transform using ${pattern.operator}`,
          });
        }
      }
    }

    // Sort by confidence and limit
    suggestions.sort((a, b) => b.confidence - a.confidence);
    return suggestions.slice(0, this.config.maxSuggestions);
  }

  generateOperatorCode(suggestion: OperatorSuggestion): string {
    const [inputType, outputType] = suggestion.signature.split('->').map(s => s.trim());
    
    // Generate type-safe function template
    const templates: Record<string, string> = {
      titleCase: `function titleCase(input: string): string {
  return input.split(' ')
    .map(word => word.charAt(0).toUpperCase() + word.slice(1).toLowerCase())
    .join(' ');
}`,
      sum: `function sum(input: number[]): number {
  return input.reduce((acc, val) => acc + val, 0);
}`,
      toNumber: `function toNumber(input: string): number {
  return Number(input);
}`,
      toString: `function toString(input: number): string {
  return String(input);
}`,
    };

    if (templates[suggestion.name]) {
      return templates[suggestion.name];
    }

    // Generate generic template
    return `function ${suggestion.name}(input: ${inputType}): ${outputType} {
  // TODO: Implement ${suggestion.description}
  throw new Error('Not implemented');
}`;
  }

  getAvailableOperators(): string[] {
    return Object.values(KNOWN_OPERATORS).flat();
  }

  getOperatorCategories(): Record<string, string[]> {
    return { ...KNOWN_OPERATORS };
  }

  validateOperator(
    _name: string,
    signature: string,
    implementation: (...args: unknown[]) => unknown
  ): OperatorValidationResult {
    try {
      // Basic validation - try to call the function
      const testInputs = this.generateTestInputs(signature);
      for (const input of testInputs) {
        implementation(input);
      }
      return { valid: true };
    } catch (error) {
      return {
        valid: false,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }

  /**
   * Detect type of value
   */
  private detectType(value: unknown): string {
    if (value === null) return 'null';
    if (value === undefined) return 'undefined';
    if (Array.isArray(value)) return 'array';
    return typeof value;
  }

  /**
   * Find conversion operator for type transformation
   */
  private findConversionOperator(fromType: string, toType: string): string | null {
    const conversionMap: Record<string, string> = {
      'string->number': 'toNumber',
      'number->string': 'toString',
      'string->boolean': 'toBoolean',
      'array->number': 'reduce',
    };

    return conversionMap[`${fromType}->${toType}`] || null;
  }

  /**
   * Detect required operators for transformation
   */
  private detectRequiredOperators(example: Example): string[] {
    const ops: string[] = [];

    // Check for array sum pattern
    if (Array.isArray(example.input) && typeof example.output === 'number') {
      const input = example.input as number[];
      if (input.every(x => typeof x === 'number')) {
        const sum = input.reduce((a, b) => a + b, 0);
        if (sum === example.output) {
          ops.push('sum', 'reduce');
        }
      }
    }

    // Check for title case pattern
    if (typeof example.input === 'string' && typeof example.output === 'string') {
      if (isTitleCase(example.input, example.output)) {
        ops.push('capitalize', 'titleCase');
      }
    }

    return ops;
  }

  /**
   * Generate test inputs based on signature
   */
  private generateTestInputs(signature: string): unknown[] {
    const inputType = signature.split('->')[0].trim();
    
    const testInputs: Record<string, unknown[]> = {
      'string': ['test', 'hello world'],
      'number': [42, 0, -1],
      'number[]': [[1, 2, 3], []],
      'boolean': [true, false],
    };

    return testInputs[inputType] || ['test'];
  }
}

/**
 * Create DSL extender
 */
export function createDSLExtender(config?: Partial<DSLExtenderConfig>): DSLExtender {
  return new DefaultDSLExtender(config as DSLExtenderConfig);
}
