/**
 * @fileoverview Sanitizer definitions - Builtin sanitizers for taint analysis
 * @module @nahisaho/musubix-security/analysis/sanitizers
 * @trace REQ-SEC-001 (EARS: テイント分析の高度化)
 */

export * from './types.js';
export * from './sql-sanitizers.js';
export * from './html-sanitizers.js';
export * from './command-sanitizers.js';
export * from './path-sanitizers.js';
export * from './validation-sanitizers.js';

import { SQL_SANITIZERS } from './sql-sanitizers.js';
import { HTML_SANITIZERS } from './html-sanitizers.js';
import { COMMAND_SANITIZERS } from './command-sanitizers.js';
import { PATH_SANITIZERS } from './path-sanitizers.js';
import { VALIDATION_SANITIZERS } from './validation-sanitizers.js';
import type { SanitizerDefinition } from './types.js';
import type { TaintSinkCategory } from '../../types/taint.js';

/**
 * All built-in sanitizers aggregated
 * @trace REQ-SEC-001
 */
export const ALL_BUILTIN_SANITIZERS: readonly SanitizerDefinition[] = [
  ...SQL_SANITIZERS,
  ...HTML_SANITIZERS,
  ...COMMAND_SANITIZERS,
  ...PATH_SANITIZERS,
  ...VALIDATION_SANITIZERS,
] as const;

/**
 * Get sanitizers that protect against a specific sink category
 */
export function getSanitizersForSink(
  sinkCategory: TaintSinkCategory
): readonly SanitizerDefinition[] {
  return ALL_BUILTIN_SANITIZERS.filter((s) =>
    s.protects.includes(sinkCategory)
  );
}

/**
 * Get sanitizers by package name
 */
export function getSanitizersByPackage(
  packageName: string
): readonly SanitizerDefinition[] {
  return ALL_BUILTIN_SANITIZERS.filter((s) => s.package === packageName);
}

/**
 * Check if a function name matches any known sanitizer
 */
export function isSanitizer(
  functionName: string,
  sinkCategory?: TaintSinkCategory
): SanitizerDefinition | undefined {
  const sanitizers = sinkCategory
    ? getSanitizersForSink(sinkCategory)
    : ALL_BUILTIN_SANITIZERS;

  return sanitizers.find(
    (s) =>
      s.name === functionName ||
      s.aliases?.includes(functionName) ||
      (s.namePattern && new RegExp(s.namePattern).test(functionName))
  );
}

/**
 * Get all sink categories that a sanitizer protects against
 */
export function getProtectedCategories(
  sanitizerName: string
): TaintSinkCategory[] {
  const sanitizer = ALL_BUILTIN_SANITIZERS.find(
    (s) =>
      s.name === sanitizerName ||
      s.aliases?.includes(sanitizerName)
  );
  return sanitizer?.protects ?? [];
}
