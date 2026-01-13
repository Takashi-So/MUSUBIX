/**
 * Path Normalizer
 *
 * Normalizes file paths for consistent handling across different input formats.
 *
 * @packageDocumentation
 * @module utils/path-normalizer
 *
 * @see REQ-CLI-001 - initコマンドパス正規化
 * @see TSK-CLI-001 - パス正規化タスク
 */

import { isAbsolute, normalize, resolve } from 'path';

/**
 * Normalized path result
 */
export interface NormalizedPath {
  /** The normalized absolute path */
  absolutePath: string;
  /** Original input path */
  originalPath: string;
  /** Whether the original path was absolute */
  wasAbsolute: boolean;
  /** Whether trailing slash was removed */
  hadTrailingSlash: boolean;
}

/**
 * Path normalizer options
 */
export interface PathNormalizerOptions {
  /** Base directory for resolving relative paths (default: process.cwd()) */
  basePath?: string;
  /** Whether to allow paths outside basePath (default: true) */
  allowOutsideBase?: boolean;
}

/**
 * Normalize a path for consistent handling.
 *
 * Handles:
 * - Absolute paths (kept as-is after normalization)
 * - Relative paths (resolved against basePath)
 * - Trailing slashes (removed)
 * - Path separators (normalized to OS-specific)
 * - Empty paths (resolved to basePath)
 *
 * @param inputPath - The path to normalize
 * @param options - Normalization options
 * @returns Normalized path information
 *
 * @example
 * ```typescript
 * // Relative path
 * normalizePath('./my-project')
 * // => { absolutePath: '/current/dir/my-project', wasAbsolute: false, ... }
 *
 * // Absolute path
 * normalizePath('/absolute/path/to/project')
 * // => { absolutePath: '/absolute/path/to/project', wasAbsolute: true, ... }
 *
 * // Trailing slash removed
 * normalizePath('./my-project/')
 * // => { absolutePath: '/current/dir/my-project', hadTrailingSlash: true, ... }
 *
 * // Empty or '.' resolves to basePath
 * normalizePath('.')
 * // => { absolutePath: '/current/dir', wasAbsolute: false, ... }
 * ```
 */
export function normalizePath(
  inputPath: string,
  options: PathNormalizerOptions = {}
): NormalizedPath {
  const basePath = options.basePath ?? process.cwd();

  // Handle empty or whitespace-only paths
  const trimmedPath = inputPath.trim();
  if (trimmedPath === '' || trimmedPath === '.') {
    return {
      absolutePath: normalize(basePath),
      originalPath: inputPath,
      wasAbsolute: false,
      hadTrailingSlash: false,
    };
  }

  // Check for trailing slash before normalization
  const hadTrailingSlash = /[/\\]$/.test(trimmedPath);

  // Check if path is absolute
  const wasAbsolute = isAbsolute(trimmedPath);

  // Resolve the path
  let absolutePath: string;
  if (wasAbsolute) {
    // For absolute paths, just normalize (don't join with basePath)
    absolutePath = normalize(trimmedPath);
  } else {
    // For relative paths, resolve against basePath
    absolutePath = resolve(basePath, trimmedPath);
  }

  // Remove trailing slashes (normalize doesn't always do this)
  absolutePath = absolutePath.replace(/[/\\]+$/, '');

  return {
    absolutePath,
    originalPath: inputPath,
    wasAbsolute,
    hadTrailingSlash,
  };
}

/**
 * Simple path normalization - returns just the absolute path string.
 *
 * @param inputPath - The path to normalize
 * @param basePath - Base directory for relative paths (default: process.cwd())
 * @returns Normalized absolute path string
 *
 * @example
 * ```typescript
 * normalizePathSimple('./my-project')  // => '/current/dir/my-project'
 * normalizePathSimple('/abs/path')     // => '/abs/path'
 * ```
 */
export function normalizePathSimple(
  inputPath: string,
  basePath?: string
): string {
  return normalizePath(inputPath, { basePath }).absolutePath;
}

/**
 * Check if a path is within a base directory.
 *
 * @param targetPath - The path to check
 * @param basePath - The base directory
 * @returns true if targetPath is within basePath
 */
export function isPathWithinBase(targetPath: string, basePath: string): boolean {
  const normalizedTarget = normalizePath(targetPath, { basePath }).absolutePath;
  const normalizedBase = normalizePath(basePath).absolutePath;

  return (
    normalizedTarget === normalizedBase ||
    normalizedTarget.startsWith(normalizedBase + '/')
  );
}
