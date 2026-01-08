/**
 * ExampleAnalyzer
 * @module @nahisaho/musubix-synthesis
 * @description Input/output example quality analysis
 * Traces to: TSK-SY-105, DES-SY-105, REQ-SY-105
 */

/**
 * Example input/output pair
 */
export interface Example {
  input: unknown;
  output: unknown;
}

/**
 * Example quality assessment
 */
export interface ExampleQuality {
  score: number;
  diversity: number;
  consistency: number;
  issues: string[];
  missingEdgeCases: string[];
}

/**
 * Ambiguity detection result
 */
export interface Ambiguity {
  type: 'semantic-ambiguity' | 'type-ambiguity' | 'transformation-ambiguity';
  description: string;
  possibleInterpretations: string[];
  suggestedDisambiguation: Example[];
}

/**
 * Example suggestion
 */
export interface ExampleSuggestion {
  input: unknown;
  reason: string;
  priority: 'high' | 'medium' | 'low';
}

/**
 * Coverage metrics
 */
export interface ExampleCoverage {
  inputTypes: string[];
  edgeCases: string[];
  totalCoverage: number;
}

/**
 * Configuration for example analyzer
 */
export interface ExampleAnalyzerConfig {
  minExamples: number;
  ambiguityThreshold: number;
}

/**
 * Example analyzer interface
 */
export interface ExampleAnalyzer {
  /**
   * Analyze quality of examples
   */
  analyzeQuality(examples: Example[]): ExampleQuality;

  /**
   * Suggest additional examples
   */
  suggestAdditionalExamples(examples: Example[], maxSuggestions?: number): ExampleSuggestion[];

  /**
   * Detect ambiguity in examples
   */
  detectAmbiguity(examples: Example[]): Ambiguity[];

  /**
   * Get coverage metrics
   */
  getExampleCoverage(examples: Example[]): ExampleCoverage;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: ExampleAnalyzerConfig = {
  minExamples: 3,
  ambiguityThreshold: 0.5,
};

/**
 * Edge case definitions
 */
const EDGE_CASES = {
  string: ['empty', 'whitespace', 'special-chars', 'unicode', 'numeric-string'],
  number: ['zero', 'negative', 'large', 'decimal', 'infinity'],
  array: ['empty', 'single-element', 'large', 'nested', 'mixed-types'],
};

/**
 * Default example analyzer implementation
 */
class DefaultExampleAnalyzer implements ExampleAnalyzer {
  private readonly config: ExampleAnalyzerConfig;

  constructor(config: ExampleAnalyzerConfig = DEFAULT_CONFIG) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  analyzeQuality(examples: Example[]): ExampleQuality {
    const issues: string[] = [];
    const missingEdgeCases: string[] = [];

    // Check minimum examples
    if (examples.length < this.config.minExamples) {
      issues.push('Insufficient examples');
    }

    // Check for duplicates
    const uniqueInputs = new Set(examples.map(e => JSON.stringify(e.input)));
    if (uniqueInputs.size < examples.length) {
      issues.push('Contains redundant/duplicate examples');
    }

    // Calculate diversity
    const diversity = this.calculateDiversity(examples);

    // Calculate consistency
    const consistency = this.calculateConsistency(examples);

    // Find missing edge cases
    const inputType = this.detectType(examples[0]?.input);
    const coveredEdgeCases = this.detectCoveredEdgeCases(examples);
    const allEdgeCases = EDGE_CASES[inputType as keyof typeof EDGE_CASES] || [];
    
    for (const edgeCase of allEdgeCases) {
      if (!coveredEdgeCases.has(edgeCase)) {
        missingEdgeCases.push(edgeCase);
      }
    }

    // Calculate overall score
    let score = 0.5;
    
    // Adjust for number of examples
    if (examples.length >= this.config.minExamples) {
      score += 0.2;
    } else {
      score -= 0.2;
    }

    // Adjust for diversity
    score += diversity * 0.2;

    // Adjust for consistency
    score += consistency * 0.1;

    // Penalize for issues
    score -= issues.length * 0.1;

    // Heavy penalty for duplicates (redundant examples)
    const duplicateRatio = (examples.length - uniqueInputs.size) / examples.length;
    if (duplicateRatio > 0.5) {
      score -= 0.5; // Major penalty for mostly duplicates
    } else if (duplicateRatio > 0) {
      score -= 0.2; // Minor penalty for some duplicates
    }

    // Clamp score
    score = Math.max(0, Math.min(1, score));

    return {
      score,
      diversity,
      consistency,
      issues,
      missingEdgeCases,
    };
  }

  suggestAdditionalExamples(examples: Example[], maxSuggestions = 5): ExampleSuggestion[] {
    const suggestions: ExampleSuggestion[] = [];
    const inputType = this.detectType(examples[0]?.input);

    // Check for empty/zero case
    const hasEmptyCase = examples.some(e => {
      if (typeof e.input === 'string') return e.input === '';
      if (Array.isArray(e.input)) return e.input.length === 0;
      if (typeof e.input === 'number') return e.input === 0;
      return false;
    });

    if (!hasEmptyCase) {
      if (inputType === 'string') {
        suggestions.push({
          input: '',
          reason: 'Missing empty string edge case',
          priority: 'high',
        });
      } else if (inputType === 'array') {
        suggestions.push({
          input: [],
          reason: 'Missing empty array edge case',
          priority: 'high',
        });
      }
    }

    // Suggest numeric content for strings
    if (inputType === 'string') {
      const hasNumericInput = examples.some(e => 
        typeof e.input === 'string' && /\d/.test(e.input)
      );
      if (!hasNumericInput) {
        suggestions.push({
          input: 'test123',
          reason: 'Missing numeric content in string examples',
          priority: 'medium',
        });
      }
    }

    // Suggest negative numbers
    if (inputType === 'array') {
      const hasNegative = examples.some(e => 
        Array.isArray(e.input) && (e.input as number[]).some(n => n < 0)
      );
      if (!hasNegative) {
        suggestions.push({
          input: [-1, -2, -3],
          reason: 'Missing negative number examples',
          priority: 'medium',
        });
      }
    }

    // Suggest special characters
    if (inputType === 'string') {
      const hasSpecialChars = examples.some(e => 
        typeof e.input === 'string' && /[!@#$%^&*]/.test(e.input)
      );
      if (!hasSpecialChars) {
        suggestions.push({
          input: 'test@example!',
          reason: 'Missing special character examples',
          priority: 'low',
        });
      }
    }

    // Suggest whitespace handling
    if (inputType === 'string') {
      const hasWhitespace = examples.some(e => 
        typeof e.input === 'string' && /^\s|\s$/.test(e.input)
      );
      if (!hasWhitespace) {
        suggestions.push({
          input: '  padded  ',
          reason: 'Missing whitespace handling examples',
          priority: 'low',
        });
      }
    }

    return suggestions.slice(0, maxSuggestions);
  }

  detectAmbiguity(examples: Example[]): Ambiguity[] {
    const ambiguities: Ambiguity[] = [];

    // Check for type ambiguity (string to number conversion)
    const hasTypeConversion = examples.some(e => {
      const inputType = typeof e.input;
      const outputType = typeof e.output;
      return inputType !== outputType;
    });

    if (hasTypeConversion && examples.length < 3) {
      ambiguities.push({
        type: 'type-ambiguity',
        description: 'Type conversion detected with insufficient examples',
        possibleInterpretations: [
          'Direct type conversion (e.g., parseInt)',
          'Custom parsing logic',
          'Format-specific conversion',
        ],
        suggestedDisambiguation: [
          { input: '0', output: 0 },
          { input: '-42', output: -42 },
          { input: '3.14', output: 3 },
        ],
      });
    }

    // Check for capitalization ambiguity
    const stringExamples = examples.filter(e => 
      typeof e.input === 'string' && typeof e.output === 'string'
    );
    
    if (stringExamples.length === 1) {
      const [ex] = stringExamples;
      const input = ex.input as string;
      const output = ex.output as string;
      
      // Check if it's ambiguous capitalization
      if (output !== input.toUpperCase() && 
          output !== input.toLowerCase() &&
          output.charAt(0) === input.charAt(0).toUpperCase()) {
        ambiguities.push({
          type: 'semantic-ambiguity',
          description: 'Capitalization pattern unclear',
          possibleInterpretations: [
            'Title case (capitalize first letter of each word)',
            'Sentence case (capitalize first letter only)',
            'Custom capitalization rules',
          ],
          suggestedDisambiguation: [
            { input: 'hello world', output: 'Hello World' },
            { input: 'test case', output: 'Test Case' },
            { input: 'ALL CAPS', output: 'All Caps' },
          ],
        });
      }
    }

    // No ambiguity for clear uppercase transformation
    if (stringExamples.length >= 3) {
      const allUppercase = stringExamples.every(e => 
        (e.output as string) === (e.input as string).toUpperCase()
      );
      if (allUppercase) {
        // Clear transformation, no ambiguity
        return [];
      }
    }

    return ambiguities;
  }

  getExampleCoverage(examples: Example[]): ExampleCoverage {
    const inputTypes = new Set<string>();
    const edgeCases: string[] = [];

    for (const example of examples) {
      inputTypes.add(this.detectType(example.input));
    }

    // Check covered edge cases
    const coveredEdgeCases = this.detectCoveredEdgeCases(examples);
    edgeCases.push(...coveredEdgeCases);

    // Calculate total coverage
    const possibleEdgeCases = Array.from(inputTypes)
      .flatMap(t => EDGE_CASES[t as keyof typeof EDGE_CASES] || []);
    
    const totalCoverage = possibleEdgeCases.length > 0
      ? edgeCases.length / possibleEdgeCases.length
      : examples.length >= 3 ? 0.5 : 0.2;

    return {
      inputTypes: Array.from(inputTypes),
      edgeCases,
      totalCoverage: Math.min(1, totalCoverage),
    };
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
   * Calculate diversity score
   */
  private calculateDiversity(examples: Example[]): number {
    if (examples.length <= 1) return 0;

    // Check type diversity
    const inputTypes = new Set(examples.map(e => this.detectType(e.input)));
    const typeDiversity = inputTypes.size / Math.max(3, examples.length);

    // Check value diversity for same types
    const stringInputs = examples
      .filter(e => typeof e.input === 'string')
      .map(e => (e.input as string).length);
    
    let lengthDiversity = 0;
    if (stringInputs.length > 1) {
      const minLen = Math.min(...stringInputs);
      const maxLen = Math.max(...stringInputs);
      lengthDiversity = minLen === maxLen ? 0 : 0.5;
    }

    return Math.min(1, typeDiversity + lengthDiversity);
  }

  /**
   * Calculate consistency score
   */
  private calculateConsistency(examples: Example[]): number {
    if (examples.length <= 1) return 1;

    // Check if transformation is consistent
    const stringExamples = examples.filter(e => 
      typeof e.input === 'string' && typeof e.output === 'string'
    );

    if (stringExamples.length >= 2) {
      // Check if all follow same pattern (e.g., all uppercase)
      const patterns = stringExamples.map(e => {
        const input = e.input as string;
        const output = e.output as string;
        if (output === input.toUpperCase()) return 'uppercase';
        if (output === input.toLowerCase()) return 'lowercase';
        return 'other';
      });

      const uniquePatterns = new Set(patterns);
      return uniquePatterns.size === 1 ? 1 : 0.5;
    }

    return 0.8; // Default for non-string types
  }

  /**
   * Detect which edge cases are covered
   */
  private detectCoveredEdgeCases(examples: Example[]): Set<string> {
    const covered = new Set<string>();

    for (const example of examples) {
      const input = example.input;

      // String edge cases
      if (typeof input === 'string') {
        if (input === '') covered.add('empty');
        if (/^\s*$/.test(input) && input !== '') covered.add('whitespace');
        if (/[!@#$%^&*]/.test(input)) covered.add('special-chars');
        if (/[\u0080-\uffff]/.test(input)) covered.add('unicode');
        if (/\d/.test(input)) covered.add('numeric-string');
      }

      // Number edge cases
      if (typeof input === 'number') {
        if (input === 0) covered.add('zero');
        if (input < 0) covered.add('negative');
        if (input > 1000000) covered.add('large');
        if (!Number.isInteger(input)) covered.add('decimal');
        if (!Number.isFinite(input)) covered.add('infinity');
      }

      // Array edge cases
      if (Array.isArray(input)) {
        if (input.length === 0) covered.add('empty');
        if (input.length === 1) covered.add('single-element');
        if (input.length > 100) covered.add('large');
        if (input.some(Array.isArray)) covered.add('nested');
        const types = new Set(input.map(i => typeof i));
        if (types.size > 1) covered.add('mixed-types');
      }
    }

    return covered;
  }
}

/**
 * Create example analyzer
 */
export function createExampleAnalyzer(config?: Partial<ExampleAnalyzerConfig>): ExampleAnalyzer {
  return new DefaultExampleAnalyzer(config as ExampleAnalyzerConfig);
}
