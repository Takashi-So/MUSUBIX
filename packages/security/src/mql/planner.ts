/**
 * @fileoverview MQL Query Planner - Optimize query execution plans
 * @module @nahisaho/musubix-security/mql/planner
 * @trace TSK-020, REQ-SEC-MQL-003
 */

import type {
  MQLAst,
  FromClause,
  WhereClause,
  MQLCondition,
  MQLExpression,
  QueryPlan,
  QueryOperation,
  PlanScan,
  PlanFilter,
  PlanProject,
  PlanJoin,
  PlanSort,
  PlanLimit,
  LogicalCondition,
  ComparisonCondition,
  InCondition,
  ExistsCondition,
  PredicateCondition,
  PatternCondition,
  MQLOptions,
  DEFAULT_MQL_OPTIONS,
} from '../types/mql.js';

/**
 * Statistics for query planning
 */
interface SourceStats {
  readonly estimatedRows: number;
  readonly hasIndex: boolean;
  readonly indexedFields: string[];
}

/**
 * Default source statistics
 */
const DEFAULT_STATS: SourceStats = {
  estimatedRows: 1000,
  hasIndex: false,
  indexedFields: [],
};

/**
 * Query Planner
 */
export class MQLPlanner {
  private readonly options: MQLOptions;
  private sourceStats: Map<string, SourceStats> = new Map();

  constructor(options: Partial<MQLOptions> = {}) {
    this.options = { ...DEFAULT_MQL_OPTIONS, ...options };
    this.initializeDefaultStats();
  }

  /**
   * Initialize default source statistics
   */
  private initializeDefaultStats(): void {
    this.sourceStats.set('functions', {
      estimatedRows: 500,
      hasIndex: true,
      indexedFields: ['name', 'file', 'type'],
    });
    this.sourceStats.set('classes', {
      estimatedRows: 100,
      hasIndex: true,
      indexedFields: ['name', 'file'],
    });
    this.sourceStats.set('calls', {
      estimatedRows: 2000,
      hasIndex: true,
      indexedFields: ['callee', 'caller', 'file'],
    });
    this.sourceStats.set('variables', {
      estimatedRows: 3000,
      hasIndex: true,
      indexedFields: ['name', 'scope', 'file'],
    });
    this.sourceStats.set('dataflow', {
      estimatedRows: 5000,
      hasIndex: false,
      indexedFields: [],
    });
    this.sourceStats.set('controlflow', {
      estimatedRows: 4000,
      hasIndex: false,
      indexedFields: [],
    });
    this.sourceStats.set('ast', {
      estimatedRows: 10000,
      hasIndex: true,
      indexedFields: ['type', 'file'],
    });
    this.sourceStats.set('symbols', {
      estimatedRows: 1500,
      hasIndex: true,
      indexedFields: ['name', 'kind', 'scope'],
    });
  }

  /**
   * Plan query execution
   */
  plan(ast: MQLAst): QueryPlan {
    const operations: QueryOperation[] = [];
    let estimatedCost = 0;

    // 1. Scan operation
    const scanOp = this.planScan(ast.from);
    operations.push(scanOp);
    estimatedCost += scanOp.estimatedCost;

    // 2. Filter operation (WHERE clause)
    if (ast.where) {
      const filterOps = this.planFilter(ast.where);
      operations.push(...filterOps);
      for (const op of filterOps) {
        estimatedCost += op.estimatedCost;
      }
    }

    // 3. Project operation (SELECT clause)
    if (ast.select) {
      const projectOp = this.planProject(ast.select.fields, ast.select.distinct);
      operations.push(projectOp);
      estimatedCost += projectOp.estimatedCost;
    }

    // 4. Sort operation (ORDER BY clause)
    if (ast.orderBy) {
      const sortOp = this.planSort(ast.orderBy.fields);
      operations.push(sortOp);
      estimatedCost += sortOp.estimatedCost;
    }

    // 5. Limit operation
    if (ast.limit) {
      const limitOp = this.planLimit(ast.limit.count, ast.limit.offset);
      operations.push(limitOp);
      estimatedCost += limitOp.estimatedCost;
    }

    // Optimize if enabled
    const optimizedOperations = this.options.enableOptimizer
      ? this.optimize(operations)
      : operations;

    return {
      operations: optimizedOperations,
      estimatedCost,
      metadata: {
        sourceType: ast.from.source.type,
        hasFilter: !!ast.where,
        hasProjection: !!ast.select,
        hasSort: !!ast.orderBy,
        hasLimit: !!ast.limit,
      },
    };
  }

  /**
   * Plan scan operation
   */
  private planScan(from: FromClause): PlanScan {
    const sourceType = from.source.type;
    const stats = this.sourceStats.get(sourceType) ?? DEFAULT_STATS;

    let estimatedCost = stats.estimatedRows;

    // Adjust cost based on source type specifics
    if (sourceType === 'dataflow' && from.source.type === 'dataflow') {
      // Dataflow with specific source/sink is cheaper
      if (from.source.source || from.source.sink) {
        estimatedCost *= 0.3;
      }
    }

    if (sourceType === 'ast' && from.source.type === 'ast') {
      // AST with specific node type is cheaper
      if (from.source.nodeType) {
        estimatedCost *= 0.1;
      }
    }

    return {
      type: 'scan',
      source: from.source,
      alias: from.alias,
      estimatedCost: Math.ceil(estimatedCost),
    };
  }

  /**
   * Plan filter operations
   */
  private planFilter(where: WhereClause): PlanFilter[] {
    const filters: PlanFilter[] = [];
    const conditions = this.flattenConditions(where.condition);

    for (const condition of conditions) {
      const selectivity = this.estimateSelectivity(condition);
      filters.push({
        type: 'filter',
        condition,
        selectivity,
        estimatedCost: Math.ceil(100 * selectivity),
        useIndex: this.canUseIndex(condition),
      });
    }

    // Sort filters by selectivity (most selective first)
    filters.sort((a, b) => a.selectivity - b.selectivity);

    return filters;
  }

  /**
   * Flatten AND conditions for individual processing
   */
  private flattenConditions(condition: MQLCondition): MQLCondition[] {
    if (condition.type === 'logical' && condition.operator === 'and') {
      const results: MQLCondition[] = [];
      for (const operand of (condition as LogicalCondition).operands) {
        results.push(...this.flattenConditions(operand));
      }
      return results;
    }
    return [condition];
  }

  /**
   * Estimate selectivity of a condition (0 to 1)
   */
  private estimateSelectivity(condition: MQLCondition): number {
    switch (condition.type) {
      case 'comparison': {
        const comp = condition as ComparisonCondition;
        switch (comp.operator) {
          case '=':
            return 0.01; // Equality is very selective
          case '!=':
            return 0.99; // Not equals is not selective
          case '<':
          case '<=':
          case '>':
          case '>=':
            return 0.3; // Range is moderately selective
        }
        return 0.5;
      }

      case 'in': {
        const inCond = condition as InCondition;
        const baseSelectivity = 0.01 * inCond.values.length;
        return inCond.negated ? 1 - baseSelectivity : baseSelectivity;
      }

      case 'exists':
        return 0.5; // Exists depends on subquery

      case 'predicate':
        return this.estimatePredicateSelectivity(condition as PredicateCondition);

      case 'pattern': {
        const pattern = condition as PatternCondition;
        return pattern.operator === 'like' ? 0.1 : 0.2;
      }

      case 'logical': {
        const logical = condition as LogicalCondition;
        switch (logical.operator) {
          case 'and':
            return logical.operands.reduce(
              (acc, op) => acc * this.estimateSelectivity(op),
              1,
            );
          case 'or':
            return Math.min(
              1,
              logical.operands.reduce(
                (acc, op) => acc + this.estimateSelectivity(op),
                0,
              ),
            );
          case 'not':
            return 1 - this.estimateSelectivity(logical.operands[0]);
        }
        return 0.5;
      }

      default:
        return 0.5;
    }
  }

  /**
   * Estimate predicate selectivity
   */
  private estimatePredicateSelectivity(predicate: PredicateCondition): number {
    switch (predicate.name) {
      case 'isSource':
        return 0.05; // Sources are rare
      case 'isSink':
        return 0.05; // Sinks are rare
      case 'isSanitizer':
        return 0.02; // Sanitizers are very rare
      case 'hasAnnotation':
        return 0.1;
      case 'isPublic':
        return 0.6; // Many things are public
      case 'isPrivate':
        return 0.3;
      case 'isStatic':
        return 0.2;
      case 'hasParameter':
        return 0.8; // Most functions have parameters
      case 'returnsValue':
        return 0.7;
      case 'throwsException':
        return 0.1;
      case 'calls':
        return 0.3;
      case 'inheritsFrom':
        return 0.1;
      case 'implements':
        return 0.1;
      default:
        return 0.5;
    }
  }

  /**
   * Check if condition can use an index
   */
  private canUseIndex(condition: MQLCondition): boolean {
    if (condition.type === 'comparison') {
      const comp = condition as ComparisonCondition;
      if (comp.operator === '=' && comp.left.type === 'field') {
        // Check if field is indexed
        return true; // Simplified - actual implementation would check source stats
      }
    }
    if (condition.type === 'in') {
      const inCond = condition as InCondition;
      return inCond.expression.type === 'field' && !inCond.negated;
    }
    return false;
  }

  /**
   * Plan project operation
   */
  private planProject(
    fields: { expression: MQLExpression; alias?: string }[],
    distinct?: boolean,
  ): PlanProject {
    const fieldNames = fields.map((f) =>
      f.alias ?? (f.expression.type === 'field' ? f.expression.name : 'expr'),
    );

    return {
      type: 'project',
      fields: fieldNames,
      distinct: distinct ?? false,
      estimatedCost: distinct ? 50 : 10,
    };
  }

  /**
   * Plan sort operation
   */
  private planSort(
    fields: { expression: MQLExpression; direction: 'asc' | 'desc' }[],
  ): PlanSort {
    const sortFields = fields.map((f) => ({
      field: f.expression.type === 'field' ? f.expression.name : 'expr',
      direction: f.direction,
    }));

    return {
      type: 'sort',
      fields: sortFields,
      estimatedCost: 100, // Sort is relatively expensive
    };
  }

  /**
   * Plan limit operation
   */
  private planLimit(count: number, offset?: number): PlanLimit {
    return {
      type: 'limit',
      count,
      offset,
      estimatedCost: 1, // Limit is cheap
    };
  }

  /**
   * Optimize query plan
   */
  private optimize(operations: QueryOperation[]): QueryOperation[] {
    let optimized = [...operations];

    // Push filters before sorts
    optimized = this.pushFilterBeforeSort(optimized);

    // Merge consecutive filters
    optimized = this.mergeFilters(optimized);

    // Push limit into scan if possible
    optimized = this.pushLimitToScan(optimized);

    return optimized;
  }

  /**
   * Push filter operations before sort operations
   */
  private pushFilterBeforeSort(operations: QueryOperation[]): QueryOperation[] {
    const result: QueryOperation[] = [];
    const filters: PlanFilter[] = [];
    const others: QueryOperation[] = [];

    for (const op of operations) {
      if (op.type === 'filter') {
        filters.push(op as PlanFilter);
      } else {
        others.push(op);
      }
    }

    // Interleave: scan -> filters -> project/sort/limit
    for (const op of others) {
      if (op.type === 'scan') {
        result.push(op);
        result.push(...filters);
      } else {
        result.push(op);
      }
    }

    return result;
  }

  /**
   * Merge consecutive filter operations
   */
  private mergeFilters(operations: QueryOperation[]): QueryOperation[] {
    const result: QueryOperation[] = [];
    let pendingFilters: PlanFilter[] = [];

    for (const op of operations) {
      if (op.type === 'filter') {
        pendingFilters.push(op as PlanFilter);
      } else {
        if (pendingFilters.length > 1) {
          // Merge filters into single AND condition
          const conditions = pendingFilters.map((f) => f.condition);
          const mergedCondition: LogicalCondition = {
            type: 'logical',
            operator: 'and',
            operands: conditions,
          };
          const totalSelectivity = pendingFilters.reduce(
            (acc, f) => acc * f.selectivity,
            1,
          );
          result.push({
            type: 'filter',
            condition: mergedCondition,
            selectivity: totalSelectivity,
            estimatedCost: Math.ceil(100 * totalSelectivity),
            useIndex: pendingFilters.some((f) => f.useIndex),
          });
        } else if (pendingFilters.length === 1) {
          result.push(pendingFilters[0]);
        }
        pendingFilters = [];
        result.push(op);
      }
    }

    // Handle remaining filters
    if (pendingFilters.length > 0) {
      result.push(...pendingFilters);
    }

    return result;
  }

  /**
   * Push limit into scan operation if possible
   */
  private pushLimitToScan(operations: QueryOperation[]): QueryOperation[] {
    // Find limit operation
    const limitIndex = operations.findIndex((op) => op.type === 'limit');
    if (limitIndex === -1) return operations;

    const limit = operations[limitIndex] as PlanLimit;

    // Check if there's no sort between scan and limit
    const sortIndex = operations.findIndex((op) => op.type === 'sort');
    if (sortIndex !== -1 && sortIndex < limitIndex) {
      // Cannot push limit past sort
      return operations;
    }

    // Find scan and add hint
    const result = operations.map((op) => {
      if (op.type === 'scan') {
        return {
          ...op,
          hint: { earlyLimit: limit.count + (limit.offset ?? 0) },
        };
      }
      return op;
    });

    return result;
  }

  /**
   * Update source statistics
   */
  updateStats(sourceType: string, stats: SourceStats): void {
    this.sourceStats.set(sourceType, stats);
  }

  /**
   * Explain query plan
   */
  explain(plan: QueryPlan): string {
    const lines: string[] = ['Query Plan:', `  Estimated Cost: ${plan.estimatedCost}`, ''];

    for (let i = 0; i < plan.operations.length; i++) {
      const op = plan.operations[i];
      const indent = '  '.repeat(i + 1);

      switch (op.type) {
        case 'scan':
          lines.push(
            `${indent}SCAN ${op.source.type}${op.alias ? ` AS ${op.alias}` : ''} (cost: ${op.estimatedCost})`,
          );
          break;
        case 'filter':
          lines.push(
            `${indent}FILTER (selectivity: ${(op.selectivity * 100).toFixed(1)}%, cost: ${op.estimatedCost}${op.useIndex ? ', INDEX' : ''})`,
          );
          break;
        case 'project':
          lines.push(
            `${indent}PROJECT [${op.fields.join(', ')}]${op.distinct ? ' DISTINCT' : ''} (cost: ${op.estimatedCost})`,
          );
          break;
        case 'sort':
          lines.push(
            `${indent}SORT BY ${op.fields.map((f) => `${f.field} ${f.direction.toUpperCase()}`).join(', ')} (cost: ${op.estimatedCost})`,
          );
          break;
        case 'limit':
          lines.push(
            `${indent}LIMIT ${op.count}${op.offset ? ` OFFSET ${op.offset}` : ''} (cost: ${op.estimatedCost})`,
          );
          break;
        case 'join':
          lines.push(`${indent}JOIN ${op.joinType} ON ... (cost: ${op.estimatedCost})`);
          break;
      }
    }

    return lines.join('\n');
  }
}

/**
 * Create query plan
 */
export function createPlan(ast: MQLAst, options?: Partial<MQLOptions>): QueryPlan {
  const planner = new MQLPlanner(options);
  return planner.plan(ast);
}

/**
 * Explain query plan as string
 */
export function explainPlan(plan: QueryPlan): string {
  const planner = new MQLPlanner();
  return planner.explain(plan);
}
