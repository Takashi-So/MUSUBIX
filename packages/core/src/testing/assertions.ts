/**
 * Custom E2E Assertions
 *
 * @fileoverview Custom Vitest assertions for E2E testing
 * @module @musubix/core/testing/assertions
 * @requirement REQ-E2E-001
 */

import type { CliResult, PerformanceBudget } from './types.js';

/**
 * EARS pattern regex patterns
 * Each pattern requires proper structure, not just keywords
 */
const EARS_PATTERNS = {
  // THE [system] SHALL [action with meaningful content]
  ubiquitous: /\bTHE\s+\w+\s+SHALL\s+(?!NOT\b)\w+.*\w/i,
  // WHEN [trigger], THE [system] SHALL [action]
  eventDriven: /\bWHEN\s+.+,\s*THE\s+\w+\s+SHALL\s+\w+/i,
  // WHILE [condition], THE [system] SHALL [action]
  stateDriven: /\bWHILE\s+.+,\s*THE\s+\w+\s+SHALL\s+\w+/i,
  // THE [system] SHALL NOT [behavior]
  unwanted: /\bTHE\s+\w+\s+SHALL\s+NOT\s+\w+/i,
  // IF [condition], THEN THE [system] SHALL [action]
  optional: /\bIF\s+.+,\s*THEN\s+THE\s+\w+\s+SHALL\s+\w+/i,
};

/**
 * Check if text is valid EARS format
 * Requires proper structure, not just keywords
 */
export function isValidEars(text: string): boolean {
  // Check each EARS pattern
  for (const [, pattern] of Object.entries(EARS_PATTERNS)) {
    if (pattern.test(text)) return true;
  }

  return false;
}

/**
 * Extract EARS pattern from text
 */
export function getEarsPattern(text: string): string | null {
  const upperText = text.toUpperCase();

  if (upperText.includes('SHALL NOT')) {
    return 'unwanted';
  }
  if (upperText.includes('WHEN') && upperText.includes('SHALL')) {
    return 'event-driven';
  }
  if (upperText.includes('WHILE') && upperText.includes('SHALL')) {
    return 'state-driven';
  }
  if (upperText.includes('IF') && upperText.includes('THEN') && upperText.includes('SHALL')) {
    return 'optional';
  }
  if (upperText.includes('THE') && upperText.includes('SHALL')) {
    return 'ubiquitous';
  }

  return null;
}

/**
 * Check if CLI result has expected exit code
 */
export function hasExitCode(result: CliResult, code: number): boolean {
  return result.exitCode === code;
}

/**
 * Check if result is within performance budget
 */
export function isWithinBudget(result: CliResult, budget: PerformanceBudget): boolean {
  if (budget.maxDuration !== undefined && result.duration > budget.maxDuration) {
    return false;
  }
  return true;
}

/**
 * Check if output contains traceability ID
 */
export function hasTraceability(output: string, id: string): boolean {
  // Match various traceability formats
  const patterns = [
    new RegExp(`\\b${id}\\b`, 'i'),
    new RegExp(`@requirement\\s+${id}`, 'i'),
    new RegExp(`@design\\s+${id}`, 'i'),
    new RegExp(`traceability.*${id}`, 'i'),
  ];

  return patterns.some((pattern) => pattern.test(output));
}

/**
 * Check if output contains pattern reference
 */
export function containsPattern(output: string, pattern: string): boolean {
  return output.toLowerCase().includes(pattern.toLowerCase());
}

/**
 * Assertion result with details
 */
export interface AssertionResult {
  pass: boolean;
  message: string;
  actual?: unknown;
  expected?: unknown;
}

/**
 * Create assertion for valid EARS format
 */
export function assertValidEars(text: string): AssertionResult {
  const valid = isValidEars(text);
  const pattern = getEarsPattern(text);

  return {
    pass: valid,
    message: valid
      ? `Text is valid EARS format (${pattern})`
      : 'Text is not valid EARS format. Expected one of: THE...SHALL, WHEN...SHALL, WHILE...SHALL, SHALL NOT, IF...THEN...SHALL',
    actual: pattern,
    expected: 'EARS pattern',
  };
}

/**
 * Create assertion for exit code
 */
export function assertExitCode(result: CliResult, expected: number): AssertionResult {
  return {
    pass: result.exitCode === expected,
    message: result.exitCode === expected
      ? `Exit code is ${expected}`
      : `Expected exit code ${expected}, got ${result.exitCode}`,
    actual: result.exitCode,
    expected,
  };
}

/**
 * Create assertion for performance budget
 */
export function assertWithinBudget(
  result: CliResult,
  budget: PerformanceBudget
): AssertionResult {
  const withinDuration = budget.maxDuration === undefined || result.duration <= budget.maxDuration;

  const issues: string[] = [];
  if (!withinDuration) {
    issues.push(`duration ${result.duration}ms > ${budget.maxDuration}ms`);
  }

  return {
    pass: withinDuration,
    message: withinDuration
      ? `Performance is within budget (${result.duration}ms)`
      : `Performance exceeds budget: ${issues.join(', ')}`,
    actual: { duration: result.duration },
    expected: budget,
  };
}

/**
 * Create assertion for traceability
 */
export function assertHasTraceability(output: string, id: string): AssertionResult {
  const has = hasTraceability(output, id);

  return {
    pass: has,
    message: has
      ? `Output contains traceability to ${id}`
      : `Output does not contain traceability to ${id}`,
    actual: output.substring(0, 200),
    expected: id,
  };
}

/**
 * Create assertion for pattern
 */
export function assertContainsPattern(output: string, pattern: string): AssertionResult {
  const contains = containsPattern(output, pattern);

  return {
    pass: contains,
    message: contains
      ? `Output contains pattern "${pattern}"`
      : `Output does not contain pattern "${pattern}"`,
    actual: output.substring(0, 200),
    expected: pattern,
  };
}

/**
 * C4 model schema keywords
 */
const C4_KEYWORDS = ['context', 'container', 'component', 'code', 'relationship', 'boundary'];

/**
 * Check if output matches C4 schema
 */
export function matchesC4Schema(output: string): boolean {
  const lower = output.toLowerCase();
  // At least 2 C4 keywords should be present
  let matches = 0;
  for (const keyword of C4_KEYWORDS) {
    if (lower.includes(keyword)) matches++;
  }
  return matches >= 2;
}

/**
 * Create assertion for C4 schema
 */
export function assertMatchesC4Schema(output: string): AssertionResult {
  const matches = matchesC4Schema(output);

  return {
    pass: matches,
    message: matches
      ? 'Output matches C4 model schema'
      : 'Output does not match C4 model schema. Expected C4 keywords like: context, container, component',
    actual: output.substring(0, 200),
    expected: 'C4 model structure',
  };
}
