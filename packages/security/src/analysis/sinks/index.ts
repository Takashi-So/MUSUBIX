/**
 * @fileoverview Taint sink definitions - Builtin sinks for interprocedural taint analysis
 * @module @nahisaho/musubix-security/analysis/sinks
 * @trace REQ-SEC-001 (EARS: テイント分析の高度化)
 */

export * from './sql-query.js';
export * from './command-exec.js';
export * from './file-operations.js';
export * from './html-output.js';
export * from './code-eval.js';
export * from './types.js';

import { SQL_QUERY_SINKS } from './sql-query.js';
import { COMMAND_EXEC_SINKS } from './command-exec.js';
import { FILE_OPERATION_SINKS } from './file-operations.js';
import { HTML_OUTPUT_SINKS } from './html-output.js';
import { CODE_EVAL_SINKS } from './code-eval.js';
import type { SinkDefinition } from './types.js';

/**
 * All built-in taint sinks aggregated
 * @trace REQ-SEC-001
 */
export const ALL_BUILTIN_SINKS: readonly SinkDefinition[] = [
  ...SQL_QUERY_SINKS,
  ...COMMAND_EXEC_SINKS,
  ...FILE_OPERATION_SINKS,
  ...HTML_OUTPUT_SINKS,
  ...CODE_EVAL_SINKS,
] as const;

/**
 * Get sinks by category
 */
export function getSinksByCategory(
  category: SinkDefinition['category']
): readonly SinkDefinition[] {
  return ALL_BUILTIN_SINKS.filter((s) => s.category === category);
}

/**
 * Get sinks by severity
 */
export function getSinksBySeverity(
  severity: SinkDefinition['severity']
): readonly SinkDefinition[] {
  return ALL_BUILTIN_SINKS.filter((s) => s.severity === severity);
}

/**
 * Get sinks by CWE ID
 */
export function getSinksByCWE(cweId: string): readonly SinkDefinition[] {
  return ALL_BUILTIN_SINKS.filter((s) => s.relatedCWE?.includes(cweId));
}
