/**
 * @fileoverview Taint source definitions - Builtin sources for interprocedural taint analysis
 * @module @nahisaho/musubix-security/analysis/sources
 * @trace REQ-SEC-001 (EARS: テイント分析の高度化)
 */

export * from './user-input.js';
export * from './http-request.js';
export * from './database.js';
export * from './file-system.js';
export * from './environment.js';
export * from './types.js';

import { USER_INPUT_SOURCES } from './user-input.js';
import { HTTP_REQUEST_SOURCES } from './http-request.js';
import { DATABASE_SOURCES } from './database.js';
import { FILE_SYSTEM_SOURCES } from './file-system.js';
import { ENVIRONMENT_SOURCES } from './environment.js';
import type { SourceDefinition } from './types.js';

/**
 * All built-in taint sources aggregated
 * @trace REQ-SEC-001
 */
export const ALL_BUILTIN_SOURCES: readonly SourceDefinition[] = [
  ...USER_INPUT_SOURCES,
  ...HTTP_REQUEST_SOURCES,
  ...DATABASE_SOURCES,
  ...FILE_SYSTEM_SOURCES,
  ...ENVIRONMENT_SOURCES,
] as const;

/**
 * Get sources by category
 */
export function getSourcesByCategory(
  category: SourceDefinition['category']
): readonly SourceDefinition[] {
  return ALL_BUILTIN_SOURCES.filter((s) => s.category === category);
}

/**
 * Get sources by framework
 */
export function getSourcesByFramework(
  framework: string
): readonly SourceDefinition[] {
  return ALL_BUILTIN_SOURCES.filter((s) => s.framework === framework);
}
