/**
 * @fileoverview MQL (MUSUBIX Query Language) Type Definitions
 * @module @nahisaho/musubix-security/types/mql
 * @trace TSK-002, REQ-SEC-MQL-001, REQ-SEC-MQL-002, REQ-SEC-MQL-003
 */

// ============================================================================
// MQL AST Types
// ============================================================================

/**
 * MQL Query AST root node
 */
export interface MQLAst {
  /** Query type */
  type: 'query';
  /** From clause */
  from: FromClause;
  /** Select clause (optional) */
  select?: SelectClause;
  /** Where clause (optional) */
  where?: WhereClause;
  /** Order by clause (optional) */
  orderBy?: OrderByClause;
  /** Limit clause (optional) */
  limit?: LimitClause;
}

/**
 * From clause - specifies data source
 */
export interface FromClause {
  /** Source type */
  source: MQLSource;
  /** Alias (optional) */
  alias?: string;
}

/**
 * MQL data sources
 */
export type MQLSource =
  | { type: 'functions' }
  | { type: 'classes' }
  | { type: 'calls' }
  | { type: 'variables' }
  | { type: 'dataflow'; source?: MQLExpression; sink?: MQLExpression }
  | { type: 'controlflow'; from?: MQLExpression; to?: MQLExpression }
  | { type: 'ast'; nodeType?: string }
  | { type: 'symbols' };

/**
 * Select clause
 */
export interface SelectClause {
  /** Fields to select */
  fields: SelectField[];
  /** Distinct? */
  distinct?: boolean;
}

/**
 * Select field
 */
export interface SelectField {
  /** Field expression */
  expression: MQLExpression;
  /** Alias (optional) */
  alias?: string;
}

/**
 * Where clause
 */
export interface WhereClause {
  /** Condition */
  condition: MQLCondition;
}

/**
 * Order by clause
 */
export interface OrderByClause {
  /** Fields to order by */
  fields: OrderByField[];
}

/**
 * Order by field
 */
export interface OrderByField {
  /** Field expression */
  expression: MQLExpression;
  /** Direction */
  direction: 'asc' | 'desc';
}

/**
 * Limit clause
 */
export interface LimitClause {
  /** Maximum results */
  count: number;
  /** Offset (optional) */
  offset?: number;
}

// ============================================================================
// MQL Expressions
// ============================================================================

/**
 * MQL expression types
 */
export type MQLExpression =
  | FieldReference
  | Literal
  | FunctionCall
  | BinaryExpression
  | UnaryExpression
  | PropertyAccess
  | ArrayAccess
  | Wildcard;

/**
 * Field reference (e.g., `function.name`)
 */
export interface FieldReference {
  type: 'field';
  name: string;
  path?: string[];
}

/**
 * Literal value
 */
export interface Literal {
  type: 'literal';
  value: string | number | boolean | null;
  dataType: 'string' | 'number' | 'boolean' | 'null' | 'regex';
}

/**
 * Function call (e.g., `isTainted(node)`)
 */
export interface FunctionCall {
  type: 'function';
  name: string;
  arguments: MQLExpression[];
}

/**
 * Binary expression
 */
export interface BinaryExpression {
  type: 'binary';
  operator: BinaryOperator;
  left: MQLExpression;
  right: MQLExpression;
}

/**
 * Binary operators
 */
export type BinaryOperator =
  | '=' | '!=' | '<' | '<=' | '>' | '>='
  | 'and' | 'or'
  | 'in' | 'not in'
  | 'like' | 'matches'
  | '+' | '-' | '*' | '/';

/**
 * Unary expression
 */
export interface UnaryExpression {
  type: 'unary';
  operator: 'not' | '-' | 'exists';
  operand: MQLExpression;
}

/**
 * Property access (e.g., `node.location.line`)
 */
export interface PropertyAccess {
  type: 'property';
  object: MQLExpression;
  property: string;
}

/**
 * Array access (e.g., `arguments[0]`)
 */
export interface ArrayAccess {
  type: 'array';
  array: MQLExpression;
  index: MQLExpression;
}

/**
 * Wildcard
 */
export interface Wildcard {
  type: 'wildcard';
}

// ============================================================================
// MQL Conditions
// ============================================================================

/**
 * MQL condition
 */
export type MQLCondition =
  | ComparisonCondition
  | LogicalCondition
  | InCondition
  | ExistsCondition
  | PredicateCondition
  | PatternCondition;

/**
 * Comparison condition
 */
export interface ComparisonCondition {
  type: 'comparison';
  operator: '=' | '!=' | '<' | '<=' | '>' | '>=';
  left: MQLExpression;
  right: MQLExpression;
}

/**
 * Logical condition (AND/OR/NOT)
 */
export interface LogicalCondition {
  type: 'logical';
  operator: 'and' | 'or' | 'not';
  operands: MQLCondition[];
}

/**
 * IN condition
 */
export interface InCondition {
  type: 'in';
  expression: MQLExpression;
  values: MQLExpression[];
  negated?: boolean;
}

/**
 * EXISTS condition
 */
export interface ExistsCondition {
  type: 'exists';
  variable: string;
  source: MQLSource;
  condition?: MQLCondition;
}

/**
 * Predicate condition (built-in predicates)
 */
export interface PredicateCondition {
  type: 'predicate';
  name: string;
  arguments: MQLExpression[];
}

/**
 * Pattern match condition (LIKE/MATCHES)
 */
export interface PatternCondition {
  type: 'pattern';
  operator: 'like' | 'matches';
  expression: MQLExpression;
  pattern: string | RegExp;
}

// ============================================================================
// Query Execution Types
// ============================================================================

/**
 * Query plan
 */
export interface QueryPlan {
  /** Plan ID */
  id: string;
  /** Root operation */
  root: QueryOperation;
  /** Estimated cost */
  estimatedCost: number;
  /** Optimizations applied */
  optimizations: string[];
}

/**
 * Query operation
 */
export type QueryOperation =
  | ScanOperation
  | FilterOperation
  | ProjectOperation
  | JoinOperation
  | SortOperation
  | LimitOperation
  | DataFlowOperation
  | ControlFlowOperation;

/**
 * Scan operation (read from source)
 */
export interface ScanOperation {
  type: 'scan';
  source: MQLSource;
  estimatedRows: number;
}

/**
 * Filter operation
 */
export interface FilterOperation {
  type: 'filter';
  input: QueryOperation;
  condition: MQLCondition;
  selectivity: number;
}

/**
 * Project operation (select fields)
 */
export interface ProjectOperation {
  type: 'project';
  input: QueryOperation;
  fields: SelectField[];
}

/**
 * Join operation
 */
export interface JoinOperation {
  type: 'join';
  left: QueryOperation;
  right: QueryOperation;
  joinType: 'inner' | 'left' | 'cross';
  condition?: MQLCondition;
}

/**
 * Sort operation
 */
export interface SortOperation {
  type: 'sort';
  input: QueryOperation;
  orderBy: OrderByField[];
}

/**
 * Limit operation
 */
export interface LimitOperation {
  type: 'limit';
  input: QueryOperation;
  count: number;
  offset?: number;
}

/**
 * Data flow analysis operation
 */
export interface DataFlowOperation {
  type: 'dataflow';
  sourceSelector?: MQLExpression;
  sinkSelector?: MQLExpression;
  maxDepth?: number;
  includeSanitized?: boolean;
}

/**
 * Control flow analysis operation
 */
export interface ControlFlowOperation {
  type: 'controlflow';
  fromSelector?: MQLExpression;
  toSelector?: MQLExpression;
  maxPaths?: number;
}

// ============================================================================
// Query Result Types
// ============================================================================

/**
 * Query result
 */
export interface QueryResult {
  /** Result rows */
  rows: QueryRow[];
  /** Column names */
  columns: string[];
  /** Total rows (before limit) */
  totalRows?: number;
  /** Execution time in milliseconds */
  executionTime: number;
  /** Query plan used */
  queryPlan?: QueryPlan;
  /** Warnings */
  warnings?: string[];
}

/**
 * Query row
 */
export type QueryRow = Record<string, unknown>;

/**
 * Parse result
 */
export interface ParseResult {
  /** Parsed AST (if successful) */
  ast?: MQLAst;
  /** Parse errors */
  errors: ParseError[];
  /** Is valid? */
  isValid: boolean;
}

/**
 * Parse error
 */
export interface ParseError {
  /** Error message */
  message: string;
  /** Line number */
  line: number;
  /** Column number */
  column: number;
  /** Error type */
  type: 'syntax' | 'semantic' | 'type';
}

// ============================================================================
// Built-in Predicates
// ============================================================================

/**
 * Predicate function signature
 */
export type PredicateFunction = (
  ...args: unknown[]
) => boolean | Promise<boolean>;

/**
 * Built-in predicate definition
 */
export interface BuiltinPredicate {
  /** Predicate name */
  name: string;
  /** Description */
  description: string;
  /** Parameter types */
  parameters: PredicateParameter[];
  /** Return type */
  returnType: 'boolean';
  /** Implementation */
  impl: PredicateFunction;
}

/**
 * Predicate parameter
 */
export interface PredicateParameter {
  /** Parameter name */
  name: string;
  /** Parameter type */
  type: 'node' | 'path' | 'string' | 'number' | 'any';
  /** Is optional? */
  optional?: boolean;
}

/**
 * List of built-in predicates
 */
export const BUILTIN_PREDICATES: string[] = [
  // Taint predicates
  'isTainted',
  'isSanitized',
  'getTaintLabel',
  'hasTaintLabel',
  
  // Reachability predicates
  'reachable',
  'dominates',
  'postDominates',
  
  // Call predicates
  'calls',
  'calledBy',
  'transitivelyCallS',
  
  // Type predicates
  'hasType',
  'isSubtypeOf',
  'implements',
  
  // AST predicates
  'hasChild',
  'hasParent',
  'hasAncestor',
  'hasDescendant',
  
  // Symbol predicates
  'isExported',
  'isImported',
  'isAsync',
  'isGenerator',
];

// ============================================================================
// MQL Engine Configuration
// ============================================================================

/**
 * MQL engine options
 */
export interface MQLEngineOptions {
  /** Maximum query execution time (ms) */
  timeout?: number;
  /** Maximum result rows */
  maxResults?: number;
  /** Enable query caching */
  enableCache?: boolean;
  /** Cache TTL (ms) */
  cacheTTL?: number;
  /** Enable query optimization */
  enableOptimization?: boolean;
  /** Custom predicates */
  customPredicates?: Map<string, PredicateFunction>;
}

/**
 * Default MQL engine options
 */
export const DEFAULT_MQL_OPTIONS: Required<Omit<MQLEngineOptions, 'customPredicates'>> = {
  timeout: 30000,
  maxResults: 10000,
  enableCache: true,
  cacheTTL: 60000,
  enableOptimization: true,
};
