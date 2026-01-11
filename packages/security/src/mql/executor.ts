/**
 * @fileoverview MQL Query Executor - Execute queries against CodeDB
 * @module @nahisaho/musubix-security/mql/executor
 * @trace TSK-021, REQ-SEC-MQL-004
 */

import type { CodeDB } from '../codedb/database.js';
import type {
  QueryPlan,
  QueryOperation,
  PlanScan,
  PlanFilter,
  PlanProject,
  PlanSort,
  PlanLimit,
  QueryResult,
  QueryRow,
  MQLCondition,
  MQLExpression,
  LogicalCondition,
  ComparisonCondition,
  InCondition,
  ExistsCondition,
  PredicateCondition,
  PatternCondition,
  MQLOptions,
  DEFAULT_MQL_OPTIONS,
  FieldReference,
  Literal,
  FunctionCall,
  BinaryExpression,
  PropertyAccess,
  ArrayAccess,
} from '../types/mql.js';
import type { ASTNode, DFGNode, CFGNode, SymbolInfo } from '../types/codedb.js';

/**
 * Execution context
 */
interface ExecutionContext {
  readonly db: CodeDB;
  readonly options: MQLOptions;
  readonly variables: Map<string, unknown>;
  readonly startTime: number;
}

/**
 * Query row with dynamic properties
 */
interface ExecutableRow {
  [key: string]: unknown;
  _source?: string;
  _id?: string;
}

/**
 * Query Executor
 */
export class MQLExecutor {
  private readonly options: MQLOptions;

  constructor(options: Partial<MQLOptions> = {}) {
    this.options = { ...DEFAULT_MQL_OPTIONS, ...options };
  }

  /**
   * Execute query plan
   */
  async execute(plan: QueryPlan, db: CodeDB): Promise<QueryResult> {
    const context: ExecutionContext = {
      db,
      options: this.options,
      variables: new Map(),
      startTime: Date.now(),
    };

    let rows: ExecutableRow[] = [];

    try {
      for (const operation of plan.operations) {
        // Check timeout
        if (this.options.timeout && Date.now() - context.startTime > this.options.timeout) {
          return {
            rows: [],
            metadata: {
              rowCount: 0,
              executionTime: Date.now() - context.startTime,
              truncated: true,
              error: 'Query timeout exceeded',
            },
          };
        }

        rows = await this.executeOperation(operation, rows, context);
      }

      return {
        rows: rows as QueryRow[],
        metadata: {
          rowCount: rows.length,
          executionTime: Date.now() - context.startTime,
          truncated: rows.length >= this.options.maxResults,
        },
      };
    } catch (error) {
      return {
        rows: [],
        metadata: {
          rowCount: 0,
          executionTime: Date.now() - context.startTime,
          truncated: false,
          error: error instanceof Error ? error.message : String(error),
        },
      };
    }
  }

  /**
   * Execute single operation
   */
  private async executeOperation(
    operation: QueryOperation,
    input: ExecutableRow[],
    context: ExecutionContext,
  ): Promise<ExecutableRow[]> {
    switch (operation.type) {
      case 'scan':
        return this.executeScan(operation as PlanScan, context);
      case 'filter':
        return this.executeFilter(operation as PlanFilter, input, context);
      case 'project':
        return this.executeProject(operation as PlanProject, input);
      case 'sort':
        return this.executeSort(operation as PlanSort, input);
      case 'limit':
        return this.executeLimit(operation as PlanLimit, input);
      default:
        throw new Error(`Unknown operation type: ${operation.type}`);
    }
  }

  /**
   * Execute scan operation
   */
  private async executeScan(
    scan: PlanScan,
    context: ExecutionContext,
  ): Promise<ExecutableRow[]> {
    const { db } = context;
    const rows: ExecutableRow[] = [];
    const alias = scan.alias ?? scan.source.type;

    switch (scan.source.type) {
      case 'functions': {
        const symbols = db.queryAST({ type: 'function_declaration' });
        for (const node of symbols) {
          rows.push(this.astNodeToRow(node, alias));
        }
        // Also include methods
        const methods = db.queryAST({ type: 'method_declaration' });
        for (const node of methods) {
          rows.push(this.astNodeToRow(node, alias));
        }
        break;
      }

      case 'classes': {
        const classes = db.queryAST({ type: 'class_declaration' });
        for (const node of classes) {
          rows.push(this.astNodeToRow(node, alias));
        }
        break;
      }

      case 'calls': {
        const calls = db.queryAST({ type: 'call_expression' });
        for (const node of calls) {
          rows.push(this.astNodeToRow(node, alias));
        }
        break;
      }

      case 'variables': {
        const vars = db.queryAST({ type: 'variable_declaration' });
        for (const node of vars) {
          rows.push(this.astNodeToRow(node, alias));
        }
        // Also include parameters
        const params = db.queryAST({ type: 'parameter' });
        for (const node of params) {
          rows.push(this.astNodeToRow(node, alias));
        }
        break;
      }

      case 'dataflow': {
        const dfgNodes = db.queryDataFlow({});
        for (const node of dfgNodes) {
          rows.push(this.dfgNodeToRow(node, alias));
        }
        break;
      }

      case 'controlflow': {
        const cfgNodes = db.queryControlFlow({});
        for (const node of cfgNodes) {
          rows.push(this.cfgNodeToRow(node, alias));
        }
        break;
      }

      case 'ast': {
        const nodeType = scan.source.nodeType;
        const astNodes = nodeType ? db.queryAST({ type: nodeType }) : db.queryAST({});
        for (const node of astNodes) {
          rows.push(this.astNodeToRow(node, alias));
        }
        break;
      }

      case 'symbols': {
        // Get all symbols from AST nodes that have names
        const allNodes = db.queryAST({});
        for (const node of allNodes) {
          if (node.name) {
            rows.push({
              _source: 'symbols',
              _id: node.id,
              name: node.name,
              kind: node.type,
              file: node.location?.file,
              line: node.location?.start.line,
              scope: node.parent,
            });
          }
        }
        break;
      }
    }

    // Apply early limit hint if present
    const hint = (scan as PlanScan & { hint?: { earlyLimit: number } }).hint;
    if (hint?.earlyLimit) {
      return rows.slice(0, hint.earlyLimit);
    }

    return rows;
  }

  /**
   * Convert AST node to row
   */
  private astNodeToRow(node: ASTNode, alias: string): ExecutableRow {
    return {
      _source: alias,
      _id: node.id,
      id: node.id,
      type: node.type,
      name: node.name,
      value: node.value,
      file: node.location?.file,
      startLine: node.location?.start.line,
      endLine: node.location?.end.line,
      startColumn: node.location?.start.column,
      endColumn: node.location?.end.column,
      children: node.children?.length ?? 0,
      parent: node.parent,
      metadata: node.metadata,
    };
  }

  /**
   * Convert DFG node to row
   */
  private dfgNodeToRow(node: DFGNode, alias: string): ExecutableRow {
    return {
      _source: alias,
      _id: node.id,
      id: node.id,
      type: node.type,
      variable: node.variable,
      astNodeId: node.astNodeId,
      file: node.location?.file,
      line: node.location?.line,
      column: node.location?.column,
      predecessors: node.predecessors,
      successors: node.successors,
    };
  }

  /**
   * Convert CFG node to row
   */
  private cfgNodeToRow(node: CFGNode, alias: string): ExecutableRow {
    return {
      _source: alias,
      _id: node.id,
      id: node.id,
      type: node.type,
      label: node.label,
      astNodeId: node.astNodeId,
      predecessors: node.predecessors,
      successors: node.successors,
      isEntry: node.isEntry,
      isExit: node.isExit,
    };
  }

  /**
   * Execute filter operation
   */
  private async executeFilter(
    filter: PlanFilter,
    input: ExecutableRow[],
    context: ExecutionContext,
  ): Promise<ExecutableRow[]> {
    const results: ExecutableRow[] = [];

    for (const row of input) {
      if (this.evaluateCondition(filter.condition, row, context)) {
        results.push(row);
      }
    }

    return results;
  }

  /**
   * Evaluate condition
   */
  private evaluateCondition(
    condition: MQLCondition,
    row: ExecutableRow,
    context: ExecutionContext,
  ): boolean {
    switch (condition.type) {
      case 'comparison':
        return this.evaluateComparison(condition as ComparisonCondition, row, context);
      case 'logical':
        return this.evaluateLogical(condition as LogicalCondition, row, context);
      case 'in':
        return this.evaluateIn(condition as InCondition, row, context);
      case 'exists':
        return this.evaluateExists(condition as ExistsCondition, row, context);
      case 'predicate':
        return this.evaluatePredicate(condition as PredicateCondition, row, context);
      case 'pattern':
        return this.evaluatePattern(condition as PatternCondition, row, context);
      default:
        return false;
    }
  }

  /**
   * Evaluate comparison condition
   */
  private evaluateComparison(
    condition: ComparisonCondition,
    row: ExecutableRow,
    context: ExecutionContext,
  ): boolean {
    const left = this.evaluateExpression(condition.left, row, context);
    const right = this.evaluateExpression(condition.right, row, context);

    switch (condition.operator) {
      case '=':
        return left === right;
      case '!=':
        return left !== right;
      case '<':
        return (left as number) < (right as number);
      case '<=':
        return (left as number) <= (right as number);
      case '>':
        return (left as number) > (right as number);
      case '>=':
        return (left as number) >= (right as number);
      default:
        return false;
    }
  }

  /**
   * Evaluate logical condition
   */
  private evaluateLogical(
    condition: LogicalCondition,
    row: ExecutableRow,
    context: ExecutionContext,
  ): boolean {
    switch (condition.operator) {
      case 'and':
        return condition.operands.every((op) => this.evaluateCondition(op, row, context));
      case 'or':
        return condition.operands.some((op) => this.evaluateCondition(op, row, context));
      case 'not':
        return !this.evaluateCondition(condition.operands[0], row, context);
      default:
        return false;
    }
  }

  /**
   * Evaluate IN condition
   */
  private evaluateIn(
    condition: InCondition,
    row: ExecutableRow,
    context: ExecutionContext,
  ): boolean {
    const value = this.evaluateExpression(condition.expression, row, context);
    const values = condition.values.map((v) =>
      this.evaluateExpression(v, row, context),
    );
    const isIn = values.includes(value);
    return condition.negated ? !isIn : isIn;
  }

  /**
   * Evaluate EXISTS condition
   */
  private evaluateExists(
    condition: ExistsCondition,
    row: ExecutableRow,
    context: ExecutionContext,
  ): boolean {
    // Simplified EXISTS evaluation
    // In a full implementation, this would execute a subquery
    return true;
  }

  /**
   * Evaluate predicate condition
   */
  private evaluatePredicate(
    condition: PredicateCondition,
    row: ExecutableRow,
    context: ExecutionContext,
  ): boolean {
    const args = condition.arguments?.map((arg) =>
      this.evaluateExpression(arg, row, context),
    ) ?? [];

    switch (condition.name) {
      case 'isSource':
        return this.isSource(row, context);
      case 'isSink':
        return this.isSink(row, context);
      case 'isSanitizer':
        return this.isSanitizer(row, context);
      case 'hasAnnotation':
        return this.hasAnnotation(row, args[0] as string);
      case 'isPublic':
        return this.hasModifier(row, 'public');
      case 'isPrivate':
        return this.hasModifier(row, 'private');
      case 'isProtected':
        return this.hasModifier(row, 'protected');
      case 'isStatic':
        return this.hasModifier(row, 'static');
      case 'isFinal':
        return this.hasModifier(row, 'final');
      case 'isAbstract':
        return this.hasModifier(row, 'abstract');
      case 'hasParameter':
        return this.hasParameter(row, args[0] as string);
      case 'returnsValue':
        return this.returnsValue(row);
      case 'throwsException':
        return this.throwsException(row);
      case 'calls':
        return this.calls(row, args[0] as string);
      case 'inheritsFrom':
        return this.inheritsFrom(row, args[0] as string);
      case 'implements':
        return this.implementsInterface(row, args[0] as string);
      case 'hasChild':
        return row.children !== undefined && (row.children as number) > 0;
      case 'isLeaf':
        return row.children === undefined || (row.children as number) === 0;
      default:
        return false;
    }
  }

  /**
   * Check if row is a source
   */
  private isSource(row: ExecutableRow, context: ExecutionContext): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    if (metadata?.isSource) return true;

    // Check known source patterns
    const name = row.name as string | undefined;
    if (name) {
      const sourcePatterns = [
        /getParameter/i,
        /getHeader/i,
        /readLine/i,
        /getInput/i,
        /request\./i,
        /req\./i,
        /\.body/i,
        /\.query/i,
        /\.params/i,
      ];
      return sourcePatterns.some((p) => p.test(name));
    }

    return false;
  }

  /**
   * Check if row is a sink
   */
  private isSink(row: ExecutableRow, context: ExecutionContext): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    if (metadata?.isSink) return true;

    // Check known sink patterns
    const name = row.name as string | undefined;
    if (name) {
      const sinkPatterns = [
        /executeQuery/i,
        /execute\(/i,
        /\.exec\(/i,
        /eval\(/i,
        /innerHTML/i,
        /document\.write/i,
        /\.send\(/i,
        /response\.write/i,
        /res\.send/i,
      ];
      return sinkPatterns.some((p) => p.test(name));
    }

    return false;
  }

  /**
   * Check if row is a sanitizer
   */
  private isSanitizer(row: ExecutableRow, context: ExecutionContext): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    if (metadata?.isSanitizer) return true;

    // Check known sanitizer patterns
    const name = row.name as string | undefined;
    if (name) {
      const sanitizerPatterns = [
        /escape/i,
        /encode/i,
        /sanitize/i,
        /validate/i,
        /clean/i,
        /filter/i,
        /purify/i,
      ];
      return sanitizerPatterns.some((p) => p.test(name));
    }

    return false;
  }

  /**
   * Check if row has annotation
   */
  private hasAnnotation(row: ExecutableRow, annotation: string): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const annotations = metadata?.annotations as string[] | undefined;
    if (annotations) {
      return annotations.some((a) => a.includes(annotation));
    }
    return false;
  }

  /**
   * Check if row has modifier
   */
  private hasModifier(row: ExecutableRow, modifier: string): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const modifiers = metadata?.modifiers as string[] | undefined;
    if (modifiers) {
      return modifiers.includes(modifier);
    }
    return false;
  }

  /**
   * Check if function has parameter
   */
  private hasParameter(row: ExecutableRow, paramName: string): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const parameters = metadata?.parameters as Array<{ name: string }> | undefined;
    if (parameters) {
      return parameters.some((p) => p.name === paramName);
    }
    return false;
  }

  /**
   * Check if function returns a value
   */
  private returnsValue(row: ExecutableRow): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const returnType = metadata?.returnType as string | undefined;
    return returnType !== undefined && returnType !== 'void';
  }

  /**
   * Check if function throws exception
   */
  private throwsException(row: ExecutableRow): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const throws = metadata?.throws as string[] | undefined;
    return throws !== undefined && throws.length > 0;
  }

  /**
   * Check if function calls another function
   */
  private calls(row: ExecutableRow, calleeName: string): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const calls = metadata?.calls as string[] | undefined;
    if (calls) {
      return calls.some((c) => c.includes(calleeName));
    }
    return false;
  }

  /**
   * Check if class inherits from another
   */
  private inheritsFrom(row: ExecutableRow, parentName: string): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const extends_ = metadata?.extends as string | undefined;
    return extends_ === parentName;
  }

  /**
   * Check if class implements interface
   */
  private implementsInterface(row: ExecutableRow, interfaceName: string): boolean {
    const metadata = row.metadata as Record<string, unknown> | undefined;
    const implements_ = metadata?.implements as string[] | undefined;
    if (implements_) {
      return implements_.includes(interfaceName);
    }
    return false;
  }

  /**
   * Evaluate pattern condition
   */
  private evaluatePattern(
    condition: PatternCondition,
    row: ExecutableRow,
    context: ExecutionContext,
  ): boolean {
    const value = this.evaluateExpression(condition.expression, row, context);
    const strValue = String(value);

    if (condition.operator === 'like') {
      // Convert SQL LIKE to regex
      const pattern = condition.pattern as string;
      const regexPattern = pattern
        .replace(/%/g, '.*')
        .replace(/_/g, '.')
        .replace(/\[/g, '\\[')
        .replace(/]/g, '\\]');
      const regex = new RegExp(`^${regexPattern}$`, 'i');
      return regex.test(strValue);
    }

    if (condition.operator === 'matches') {
      const regex = condition.pattern as RegExp;
      return regex.test(strValue);
    }

    return false;
  }

  /**
   * Evaluate expression
   */
  private evaluateExpression(
    expression: MQLExpression,
    row: ExecutableRow,
    context: ExecutionContext,
  ): unknown {
    switch (expression.type) {
      case 'field':
        return row[(expression as FieldReference).name];

      case 'literal':
        return (expression as Literal).value;

      case 'function':
        return this.evaluateFunction(expression as FunctionCall, row, context);

      case 'binary':
        return this.evaluateBinary(expression as BinaryExpression, row, context);

      case 'property':
        return this.evaluateProperty(expression as PropertyAccess, row, context);

      case 'array':
        return this.evaluateArrayAccess(expression as ArrayAccess, row, context);

      case 'wildcard':
        return row;

      default:
        return undefined;
    }
  }

  /**
   * Evaluate function call
   */
  private evaluateFunction(
    func: FunctionCall,
    row: ExecutableRow,
    context: ExecutionContext,
  ): unknown {
    const args = func.arguments.map((arg) =>
      this.evaluateExpression(arg, row, context),
    );

    switch (func.name.toLowerCase()) {
      case 'count':
        return 1; // In group context, this would count rows
      case 'length':
      case 'len':
        return String(args[0]).length;
      case 'lower':
      case 'lowercase':
        return String(args[0]).toLowerCase();
      case 'upper':
      case 'uppercase':
        return String(args[0]).toUpperCase();
      case 'trim':
        return String(args[0]).trim();
      case 'substring':
      case 'substr':
        return String(args[0]).substring(
          args[1] as number,
          args[2] as number | undefined,
        );
      case 'concat':
        return args.map(String).join('');
      case 'coalesce':
        return args.find((a) => a !== null && a !== undefined) ?? null;
      case 'isnull':
        return args[0] === null || args[0] === undefined;
      case 'typeof':
        return typeof args[0];
      default:
        return undefined;
    }
  }

  /**
   * Evaluate binary expression
   */
  private evaluateBinary(
    expr: BinaryExpression,
    row: ExecutableRow,
    context: ExecutionContext,
  ): unknown {
    const left = this.evaluateExpression(expr.left, row, context) as number;
    const right = this.evaluateExpression(expr.right, row, context) as number;

    switch (expr.operator) {
      case '+':
        return left + right;
      case '-':
        return left - right;
      case '*':
        return left * right;
      case '/':
        return right !== 0 ? left / right : null;
      default:
        return undefined;
    }
  }

  /**
   * Evaluate property access
   */
  private evaluateProperty(
    expr: PropertyAccess,
    row: ExecutableRow,
    context: ExecutionContext,
  ): unknown {
    const obj = this.evaluateExpression(expr.object, row, context) as Record<
      string,
      unknown
    >;
    if (obj && typeof obj === 'object') {
      return obj[expr.property];
    }
    return undefined;
  }

  /**
   * Evaluate array access
   */
  private evaluateArrayAccess(
    expr: ArrayAccess,
    row: ExecutableRow,
    context: ExecutionContext,
  ): unknown {
    const arr = this.evaluateExpression(expr.array, row, context) as unknown[];
    const index = this.evaluateExpression(expr.index, row, context) as number;
    if (Array.isArray(arr)) {
      return arr[index];
    }
    return undefined;
  }

  /**
   * Execute project operation
   */
  private async executeProject(
    project: PlanProject,
    input: ExecutableRow[],
  ): Promise<ExecutableRow[]> {
    let results: ExecutableRow[];

    if (project.fields.length === 0 || project.fields.includes('*')) {
      results = input;
    } else {
      results = input.map((row) => {
        const projected: ExecutableRow = {};
        for (const field of project.fields) {
          projected[field] = row[field];
        }
        return projected;
      });
    }

    if (project.distinct) {
      const seen = new Set<string>();
      results = results.filter((row) => {
        const key = JSON.stringify(row);
        if (seen.has(key)) return false;
        seen.add(key);
        return true;
      });
    }

    return results;
  }

  /**
   * Execute sort operation
   */
  private async executeSort(
    sort: PlanSort,
    input: ExecutableRow[],
  ): Promise<ExecutableRow[]> {
    return [...input].sort((a, b) => {
      for (const { field, direction } of sort.fields) {
        const aVal = a[field];
        const bVal = b[field];

        let comparison = 0;
        if (aVal === bVal) {
          comparison = 0;
        } else if (aVal === null || aVal === undefined) {
          comparison = 1;
        } else if (bVal === null || bVal === undefined) {
          comparison = -1;
        } else if (typeof aVal === 'string' && typeof bVal === 'string') {
          comparison = aVal.localeCompare(bVal);
        } else {
          comparison = (aVal as number) < (bVal as number) ? -1 : 1;
        }

        if (comparison !== 0) {
          return direction === 'desc' ? -comparison : comparison;
        }
      }
      return 0;
    });
  }

  /**
   * Execute limit operation
   */
  private async executeLimit(
    limit: PlanLimit,
    input: ExecutableRow[],
  ): Promise<ExecutableRow[]> {
    const start = limit.offset ?? 0;
    const end = start + limit.count;
    return input.slice(start, end);
  }
}

/**
 * Execute query plan against CodeDB
 */
export async function execute(
  plan: QueryPlan,
  db: CodeDB,
  options?: Partial<MQLOptions>,
): Promise<QueryResult> {
  const executor = new MQLExecutor(options);
  return executor.execute(plan, db);
}
