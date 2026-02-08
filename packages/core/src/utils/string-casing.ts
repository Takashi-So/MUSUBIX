/**
 * String casing conversion utilities.
 *
 * Shared module for converting between PascalCase, camelCase,
 * snake_case, and kebab-case.
 *
 * @packageDocumentation
 * @module string-casing
 */

/**
 * Convert a string to PascalCase.
 *
 * Handles UPPER_CASE, snake_case, kebab-case, camelCase, and mixed inputs.
 * Already-PascalCase strings are returned unchanged.
 *
 * Known suffixes (Service, Entity, Repository, etc.) are preserved
 * so that e.g. "BLOG_PLATFORMService" becomes "BlogPlatformService".
 */
export function toPascalCase(str: string): string {
  if (str === '') return '';

  // Already proper PascalCase (no underscores/hyphens, starts uppercase, not ALL_CAPS)
  if (/^[A-Z][a-zA-Z0-9]*$/.test(str) && str !== str.toUpperCase()) {
    return str;
  }

  const suffixes = [
    'Service',
    'Entity',
    'Repository',
    'Validator',
    'Controller',
    'Manager',
    'Component',
    'View',
    'Panel',
    'Helper',
    'Factory',
    'Builder',
  ];
  let preservedSuffix = '';
  let baseName = str;

  for (const suffix of suffixes) {
    if (str.endsWith(suffix) && str.length > suffix.length) {
      preservedSuffix = suffix;
      baseName = str.slice(0, -suffix.length);
      break;
    }
  }

  // Insert separators at camelCase boundaries before lowercasing
  const pascalBase = baseName
    .replace(/([a-z])([A-Z])/g, '$1_$2')
    .toLowerCase()
    .replace(/[-_\s]+(.)?/g, (_, c) => (c ? c.toUpperCase() : ''))
    .replace(/^./, (s) => s.toUpperCase());

  return pascalBase + preservedSuffix;
}

/**
 * Convert a string to camelCase.
 *
 * Converts the input to PascalCase first, then lowercases the first character.
 */
export function toCamelCase(str: string): string {
  if (str === '') return '';
  const pascal = toPascalCase(str);
  return pascal.charAt(0).toLowerCase() + pascal.slice(1);
}

/**
 * Convert a string to snake_case.
 *
 * Handles PascalCase, camelCase, kebab-case, and space-separated inputs.
 */
export function toSnakeCase(str: string): string {
  if (str === '') return '';
  return str
    .replace(/([a-z])([A-Z])/g, '$1_$2')
    .replace(/[-\s]+/g, '_')
    .toLowerCase();
}

/**
 * Convert a string to kebab-case.
 *
 * Handles PascalCase, camelCase, UPPER_CASE, snake_case,
 * and space-separated inputs. Consecutive uppercase letters
 * followed by a lowercase letter are split correctly
 * (e.g. "XMLParser" -> "xml-parser").
 */
export function toKebabCase(str: string): string {
  if (str === '') return '';
  return str
    .replace(/([a-z])([A-Z])/g, '$1-$2')
    .replace(/([A-Z])([A-Z][a-z])/g, '$1-$2')
    .replace(/[\s_]+/g, '-')
    .toLowerCase();
}
