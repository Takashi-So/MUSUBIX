/**
 * @fileoverview File system utilities for security scanning
 * @module @nahisaho/musubix-security/infrastructure/file-scanner
 * @trace REQ-SEC-SCAN-004
 */

import { readdir, stat, readFile } from 'node:fs/promises';
import { join, relative, extname } from 'node:path';
import { minimatch } from 'minimatch';

/**
 * File information
 */
export interface FileInfo {
  /** Absolute file path */
  path: string;
  /** Relative path from root */
  relativePath: string;
  /** File size in bytes */
  size: number;
  /** File extension */
  extension: string;
  /** Last modified time */
  modifiedAt: Date;
}

/**
 * File scanner options
 */
export interface FileScannerOptions {
  /** File extensions to include */
  extensions?: string[];
  /** Glob patterns to exclude */
  excludePatterns?: string[];
  /** Maximum file size in bytes */
  maxFileSize?: number;
  /** Maximum depth to scan */
  maxDepth?: number;
  /** Follow symbolic links */
  followSymlinks?: boolean;
}

/**
 * Default exclude patterns
 */
export const DEFAULT_EXCLUDE_PATTERNS = [
  'node_modules/**',
  '.git/**',
  'dist/**',
  'build/**',
  'coverage/**',
  '.nyc_output/**',
  '*.min.js',
  '*.min.mjs',
  '*.bundle.js',
  '*.d.ts',
  '__tests__/**',
  '__mocks__/**',
  '*.test.ts',
  '*.test.js',
  '*.spec.ts',
  '*.spec.js',
  '.next/**',
  '.nuxt/**',
  'vendor/**',
];

/**
 * Default scannable extensions
 */
export const DEFAULT_EXTENSIONS = [
  '.ts',
  '.tsx',
  '.js',
  '.jsx',
  '.mjs',
  '.cjs',
  '.vue',
  '.svelte',
];

/**
 * File scanner for collecting files to analyze
 */
export class FileScanner {
  private options: Required<FileScannerOptions>;

  constructor(options: FileScannerOptions = {}) {
    this.options = {
      extensions: options.extensions ?? DEFAULT_EXTENSIONS,
      excludePatterns: options.excludePatterns ?? DEFAULT_EXCLUDE_PATTERNS,
      maxFileSize: options.maxFileSize ?? 5 * 1024 * 1024, // 5MB
      maxDepth: options.maxDepth ?? 50,
      followSymlinks: options.followSymlinks ?? false,
    };
  }

  /**
   * Scan a directory for files
   */
  async scan(rootPath: string): Promise<FileInfo[]> {
    const files: FileInfo[] = [];
    await this.scanDirectory(rootPath, rootPath, 0, files);
    return files;
  }

  /**
   * Recursively scan a directory
   */
  private async scanDirectory(
    currentPath: string,
    rootPath: string,
    depth: number,
    results: FileInfo[]
  ): Promise<void> {
    if (depth > this.options.maxDepth) {
      return;
    }

    try {
      const entries = await readdir(currentPath, { withFileTypes: true });

      for (const entry of entries) {
        const fullPath = join(currentPath, entry.name);
        const relativePath = relative(rootPath, fullPath);

        // Check exclude patterns
        if (this.isExcluded(relativePath)) {
          continue;
        }

        if (entry.isDirectory()) {
          await this.scanDirectory(fullPath, rootPath, depth + 1, results);
        } else if (entry.isFile() || (this.options.followSymlinks && entry.isSymbolicLink())) {
          const fileInfo = await this.getFileInfo(fullPath, rootPath);
          if (fileInfo && this.shouldInclude(fileInfo)) {
            results.push(fileInfo);
          }
        }
      }
    } catch (error) {
      // Skip directories we can't read
      console.warn(`Warning: Cannot read directory ${currentPath}: ${error}`);
    }
  }

  /**
   * Get file information
   */
  private async getFileInfo(filePath: string, rootPath: string): Promise<FileInfo | null> {
    try {
      const stats = await stat(filePath);
      return {
        path: filePath,
        relativePath: relative(rootPath, filePath),
        size: stats.size,
        extension: extname(filePath).toLowerCase(),
        modifiedAt: stats.mtime,
      };
    } catch {
      return null;
    }
  }

  /**
   * Check if a path should be excluded
   */
  private isExcluded(relativePath: string): boolean {
    return this.options.excludePatterns.some((pattern) =>
      minimatch(relativePath, pattern, { dot: true })
    );
  }

  /**
   * Check if a file should be included
   */
  private shouldInclude(fileInfo: FileInfo): boolean {
    // Check extension
    if (!this.options.extensions.includes(fileInfo.extension)) {
      return false;
    }

    // Check file size
    if (fileInfo.size > this.options.maxFileSize) {
      return false;
    }

    return true;
  }

  /**
   * Read file content
   */
  async readFile(filePath: string): Promise<string> {
    return readFile(filePath, 'utf-8');
  }

  /**
   * Read file content with error handling
   */
  async readFileSafe(filePath: string): Promise<string | null> {
    try {
      return await this.readFile(filePath);
    } catch {
      return null;
    }
  }

  /**
   * Check if a file exists and is readable
   */
  async isReadable(filePath: string): Promise<boolean> {
    try {
      await stat(filePath);
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Get file stats
   */
  async getStats(filePath: string): Promise<{ size: number; modifiedAt: Date } | null> {
    try {
      const stats = await stat(filePath);
      return {
        size: stats.size,
        modifiedAt: stats.mtime,
      };
    } catch {
      return null;
    }
  }
}

/**
 * Create a file scanner with custom options
 */
export function createFileScanner(options?: FileScannerOptions): FileScanner {
  return new FileScanner(options);
}
