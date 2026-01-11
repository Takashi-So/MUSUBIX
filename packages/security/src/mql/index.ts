/**
 * @fileoverview MQL Module - MUSUBIX Query Language
 * @module @nahisaho/musubix-security/mql
 * @trace TSK-022, REQ-SEC-MQL-001
 */

export { MQLLexer, TokenType, type Token, type LexerError } from './lexer.js';
export { MQLParser, parse } from './parser.js';
export { MQLPlanner, createPlan, explainPlan } from './planner.js';
export { MQLExecutor, execute } from './executor.js';

// Re-export types
export type {
  MQLAst,
  FromClause,
  SelectClause,
  SelectField,
  WhereClause,
  OrderByClause,
  OrderByField,
  LimitClause,
  MQLSource,
  MQLExpression,
  MQLCondition,
  ParseResult,
  ParseError,
  QueryPlan,
  QueryOperation,
  QueryResult,
  QueryRow,
  MQLOptions,
} from '../types/mql.js';

import { parse as parseQuery, type ParseResult } from './parser.js';
import { createPlan, explainPlan, type QueryPlan } from './planner.js';
import { execute as executeQuery, type QueryResult } from './executor.js';
import type { CodeDB } from '../codedb/database.js';
import type { MQLOptions, DEFAULT_MQL_OPTIONS } from '../types/mql.js';

/**
 * MQL Query Engine
 * High-level API for executing MQL queries
 */
export class MQLEngine {
  private readonly options: Partial<MQLOptions>;

  constructor(options: Partial<MQLOptions> = {}) {
    this.options = options;
  }

  /**
   * Parse MQL query into AST
   */
  parse(query: string): ParseResult {
    return parseQuery(query);
  }

  /**
   * Plan query execution
   */
  plan(query: string): { plan: QueryPlan; errors: string[] } {
    const parseResult = parseQuery(query);
    if (!parseResult.isValid || !parseResult.ast) {
      return {
        plan: { operations: [], estimatedCost: 0, metadata: {} },
        errors: parseResult.errors.map((e) => e.message),
      };
    }

    const plan = createPlan(parseResult.ast, this.options);
    return { plan, errors: [] };
  }

  /**
   * Execute MQL query against CodeDB
   */
  async execute(query: string, db: CodeDB): Promise<QueryResult> {
    const parseResult = parseQuery(query);
    if (!parseResult.isValid || !parseResult.ast) {
      return {
        rows: [],
        metadata: {
          rowCount: 0,
          executionTime: 0,
          truncated: false,
          error: parseResult.errors.map((e) => e.message).join('; '),
        },
      };
    }

    const plan = createPlan(parseResult.ast, this.options);
    return executeQuery(plan, db, this.options);
  }

  /**
   * Explain query execution plan
   */
  explain(query: string): string {
    const { plan, errors } = this.plan(query);
    if (errors.length > 0) {
      return `Parse errors:\n${errors.join('\n')}`;
    }
    return explainPlan(plan);
  }

  /**
   * Validate MQL query syntax
   */
  validate(query: string): { isValid: boolean; errors: string[] } {
    const parseResult = parseQuery(query);
    return {
      isValid: parseResult.isValid,
      errors: parseResult.errors.map((e) => `${e.line}:${e.column}: ${e.message}`),
    };
  }
}

/**
 * Create MQL engine instance
 */
export function createMQLEngine(options?: Partial<MQLOptions>): MQLEngine {
  return new MQLEngine(options);
}

/**
 * Execute MQL query (convenience function)
 */
export async function query(
  mql: string,
  db: CodeDB,
  options?: Partial<MQLOptions>,
): Promise<QueryResult> {
  const engine = new MQLEngine(options);
  return engine.execute(mql, db);
}

/**
 * Validate MQL query (convenience function)
 */
export function validate(mql: string): { isValid: boolean; errors: string[] } {
  const engine = new MQLEngine();
  return engine.validate(mql);
}
