/**
 * Type Definitions for MUSUBIX Synthesis
 * @module @nahisaho/musubix-synthesis
 * @description DSL-based program synthesis types
 */

// =============================================================================
// Type System
// =============================================================================

/**
 * Type signature
 */
export type TypeSignature = string | { kind: 'function'; inputs: TypeSignature[]; output: TypeSignature } | { kind: 'generic'; name: string };

/**
 * Type definition
 */
export interface TypeDefinition {
  readonly name: string;
  readonly kind: 'primitive' | 'composite' | 'function' | 'generic';
  readonly parameters?: TypeSignature[];
  readonly fields?: Map<string, TypeSignature>;
}

/**
 * Type check result
 */
export interface TypeCheckResult {
  readonly valid: boolean;
  readonly inferredType?: TypeSignature;
  readonly errors: TypeCheckError[];
}

/**
 * Type check error
 */
export interface TypeCheckError {
  readonly message: string;
  readonly location?: ExpressionLocation;
  readonly expected?: TypeSignature;
  readonly actual?: TypeSignature;
}

/**
 * Expression location
 */
export interface ExpressionLocation {
  readonly path: number[];
}

// =============================================================================
// DSL Framework
// =============================================================================

/**
 * DSL operator
 * Traces to: REQ-SYN-001 (DSL Definition Framework)
 */
export interface Operator {
  readonly name: string;
  readonly inputTypes: TypeSignature[];
  readonly outputType: TypeSignature;
  readonly implementation?: (...args: unknown[]) => unknown;
  readonly semantics?: (...args: unknown[]) => unknown;
  readonly description?: string;
  readonly cost?: number;
}

/**
 * DSL constant
 */
export interface Constant {
  readonly name: string;
  readonly type: TypeSignature;
  readonly value: unknown;
}

/**
 * DSL configuration
 */
export interface DSLConfig {
  readonly name?: string;
  readonly operators: Operator[];
  readonly constants: Constant[];
  readonly types: TypeDefinition[];
}

/**
 * DSL interface
 */
export interface IDSL {
  readonly name: string;
  readonly operators: Map<string, Operator>;
  readonly constants: Map<string, Constant>;
  readonly types: Map<string, TypeDefinition>;
  
  execute(program: Program, input: unknown): unknown;
  validate(program: Program): boolean;
  validateWithDetails?(program: Program): ValidationResult;
  getOperator(name: string): Operator | undefined;
  getConstant(name: string): Constant | undefined;
  getType(name: string): TypeDefinition | undefined;
  getOperators(): Operator[];
  getConstants(): Constant[];
  getConstant(name: string): Constant | undefined;
  getType(name: string): TypeDefinition | undefined;
}

/**
 * Validation result
 */
export interface ValidationResult {
  readonly valid: boolean;
  readonly errors: ValidationError[];
}

/**
 * Validation error
 */
export interface ValidationError {
  readonly message: string;
  readonly path?: number[];
}

// =============================================================================
// Program Representation
// =============================================================================

/**
 * Program expression
 */
export type Expression =
  | ConstantExpression
  | VariableExpression
  | ApplicationExpression
  | LambdaExpression;

/**
 * Constant expression
 */
export interface ConstantExpression {
  readonly kind: 'constant';
  readonly name: string;
}

/**
 * Variable expression
 */
export interface VariableExpression {
  readonly kind: 'variable';
  readonly name: string;
  readonly index?: number;
}

/**
 * Application expression
 */
export interface ApplicationExpression {
  readonly kind: 'application';
  readonly operator: string;
  readonly args: Expression[];
}

/**
 * Lambda expression
 */
export interface LambdaExpression {
  readonly kind: 'lambda';
  readonly parameter: string;
  readonly parameterType: TypeSignature;
  readonly body: Expression;
}

/**
 * Program
 */
export interface Program {
  readonly id?: string;
  readonly expression: Expression;
  readonly type?: TypeSignature;
  readonly cost?: number;
  readonly metadata?: Record<string, unknown>;
}

// =============================================================================
// Synthesis
// =============================================================================

/**
 * Input-output example
 * Traces to: REQ-SYN-003 (PBE Synthesis)
 */
export interface Example {
  readonly input: unknown;
  readonly output: unknown;
  readonly metadata?: Record<string, unknown>;
}

/**
 * Specification
 */
export interface Specification {
  readonly examples: Example[];
  readonly inputType?: TypeSignature;
  readonly outputType?: TypeSignature;
  readonly constraints?: Constraint[];
}

/**
 * Constraint
 */
export interface Constraint {
  readonly kind: 'type' | 'size' | 'custom';
  readonly predicate: (program: Program) => boolean;
  readonly description?: string;
}

/**
 * Synthesis options
 */
export interface SynthesisOptions {
  readonly maxDepth?: number;
  readonly maxCost?: number;
  readonly timeout?: number;
  readonly maxCandidates?: number;
  readonly useNeuralGuidance?: boolean;
  readonly pruneThreshold?: number;
}

/**
 * Synthesis result
 */
export interface SynthesisResult {
  readonly success: boolean;
  readonly program?: Program;
  readonly candidates?: Program[];
  readonly duration: number;
  readonly synthesisTime: number;
  readonly searchNodes: number;
  readonly candidatesExplored: number;
  readonly pruned: number;
  readonly error?: string;
}

/**
 * PBE synthesizer interface
 */
export interface IPBESynthesizer {
  synthesize(
    spec: Specification,
    dsl: IDSL,
    options?: SynthesisOptions
  ): Promise<SynthesisResult>;
  
  getCandidates?(
    spec: Specification,
    dsl: IDSL,
    limit?: number
  ): Program[];
  
  disambiguate(
    candidates: Program[],
    example: Example
  ): Program[];
}

// =============================================================================
// Witness Functions
// =============================================================================

/**
 * Witness function
 * Traces to: REQ-SYN-002 (Witness Functions)
 */
export interface WitnessFunction {
  readonly operator: string;
  readonly argIndex: number;
  
  witness?(spec: Specification): Specification[];
  inverse?(outputSpec: Specification): Specification[];
}

/**
 * Decomposed specification
 */
export interface DecomposedSpec {
  readonly operator: string;
  readonly argSpecs: Specification[];
  readonly confidence: number;
}

/**
 * Witness engine interface
 */
export interface IWitnessEngine {
  register(witness: WitnessFunction): void;
  registerWitness(witness: WitnessFunction): void;
  getWitnesses(operator: string): WitnessFunction[];
  clearWitnesses(): void;
  decompose(spec: Specification, operator: string): DecomposedSpec;
  synthesizeDeductively(dsl: IDSL, spec: Specification): Promise<Program | null>;
  synthesizeWithWitness(spec: Specification, options?: SynthesisOptions): Promise<SynthesisResult>;
}

// =============================================================================
// Version Space
// =============================================================================

/**
 * Version space interface
 */
export interface IVersionSpace {
  add(program: Program): void;
  refine(example: Example, dsl: IDSL): IVersionSpace;
  isConverged(): boolean;
  getProgram(): Program | null;
  size(): number;
  getCandidates(limit?: number): Program[];
}

// =============================================================================
// Rule Learning
// =============================================================================

/**
 * Specification pattern
 */
export interface SpecPattern {
  readonly inputPattern?: unknown;
  readonly outputPattern?: unknown;
  readonly typeConstraints?: TypeSignature[];
  readonly inputCount?: number;
  readonly exampleCount?: number;
  readonly outputType?: string;
}

/**
 * Program template
 */
export interface ProgramTemplate {
  readonly expression: Expression;
  readonly holes: HoleDefinition[];
}

/**
 * Hole definition in template
 */
export interface HoleDefinition {
  readonly name: string;
  readonly type: TypeSignature;
  readonly path: number[];
}

/**
 * Synthesis rule
 * Traces to: REQ-SYN-004 (Rule Learning)
 */
export interface SynthesisRule {
  readonly id: string;
  readonly name?: string;
  readonly pattern: SpecPattern;
  readonly template: ProgramTemplate;
  readonly confidence: number;
  readonly usageCount?: number;
  readonly successCount?: number;
}

/**
 * Rule library interface
 */
export interface IRuleLibrary {
  add(rule: SynthesisRule): Promise<void>;
  get(id: string): Promise<SynthesisRule | null>;
  match(spec: Specification): Promise<SynthesisRule[]>;
  recordUsage(ruleId: string, success: boolean): Promise<void>;
  prune(threshold: number): Promise<number>;
  getAll(): Promise<SynthesisRule[]>;
}

/**
 * Rule extractor interface
 */
export interface IRuleExtractor {
  extract(spec: Specification, program: Program): SynthesisRule[];
  generalize(rules: SynthesisRule[]): SynthesisRule[];
}

/**
 * Meta learner interface
 */
export interface IMetaLearner {
  learn(result: SynthesisResult, usedRules: SynthesisRule[]): Promise<void>;
  updateConfidence(ruleId: string, success: boolean): Promise<void>;
  suggestRules(): Promise<SynthesisRule[]>;
}

// =============================================================================
// Statistics
// =============================================================================

/**
 * Synthesis statistics
 */
export interface SynthesisStatistics {
  readonly totalSyntheses: number;
  readonly successfulSyntheses: number;
  readonly averageDuration: number;
  readonly averageSearchNodes: number;
  readonly rulesUsed: number;
}

/**
 * Type system interface
 */
export interface ITypeSystem {
  check(program: Program, env?: TypeContext): boolean;
  checkWithDetails?(program: Program, env?: TypeContext): TypeCheckResult;
  infer(expression: Expression, env?: TypeContext): TypeSignature | null;
  unify?(a: TypeSignature, b: TypeSignature): TypeSignature | null;
  isSubtype(sub: TypeSignature, sup: TypeSignature): boolean;
}

/**
 * Type context
 */
export interface TypeContext {
  readonly variables: Map<string, TypeSignature>;
}

// =============================================================================
// Enumerator
// =============================================================================

/**
 * Enumeration options
 */
export interface EnumerationOptions {
  readonly maxDepth: number;
  readonly maxCost: number;
  readonly targetType?: TypeSignature;
  readonly yieldInterval?: number;
}

/**
 * Enumerator interface
 */
export interface IEnumerator {
  enumerate(options: { maxDepth: number; maxPrograms?: number; targetType?: TypeSignature }): Program[];
  
  enumerateExpressions(depth: number): Expression[];
  
  getExpressionDepth(expr: Expression): number;
  
  countPrograms(depth: number): number;
  
  enumerateForSpec(
    spec: Specification,
    options: EnumerationOptions
  ): AsyncGenerator<Program, void, unknown>;
}
