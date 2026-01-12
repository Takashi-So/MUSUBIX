/**
 * Space Context - Space context management
 *
 * Implements: TSK-SPACES-001〜002, REQ-SPACES-001〜002, DES-SPACES-002
 */

import { readdir } from 'node:fs/promises';
import { join, relative, extname } from 'node:path';
import type {
  Space,
  ContextQuery,
  ContextSuggestion,
  RecentFile,
} from './types.js';

/**
 * Space Context configuration
 */
export interface SpaceContextConfig {
  /** Workspace root path */
  workspacePath: string;

  /** Max depth for file search */
  maxDepth?: number;

  /** File extensions to include */
  defaultExtensions?: string[];
}

/**
 * Space Context class - manages context for a space
 */
export class SpaceContext_ {
  private config: Required<SpaceContextConfig>;
  private recentFiles: Map<string, RecentFile> = new Map();

  constructor(config: SpaceContextConfig) {
    this.config = {
      maxDepth: 10,
      defaultExtensions: ['.ts', '.js', '.tsx', '.jsx', '.md', '.json', '.yml', '.yaml'],
      ...config,
    };
  }

  /**
   * Get files matching the space context
   */
  async getContextFiles(space: Space): Promise<string[]> {
    const files: string[] = [];

    // Add pinned files first
    if (space.context.pinnedFiles) {
      files.push(...space.context.pinnedFiles);
    }

    // Add explicitly included files
    for (const pattern of space.context.includedFiles) {
      const matched = await this.matchFiles(pattern, space.context.excludedFiles);
      files.push(...matched);
    }

    // Add recent files up to limit
    if (space.settings.trackRecentFiles && space.context.recentFiles) {
      const recentPaths = space.context.recentFiles
        .slice(0, space.settings.recentFilesLimit)
        .map((r) => r.path);
      files.push(...recentPaths);
    }

    // Deduplicate and limit
    const uniqueFiles = [...new Set(files)];
    return uniqueFiles.slice(0, space.settings.maxContextFiles);
  }

  /**
   * Suggest relevant files for a query
   */
  async suggestFiles(query: ContextQuery): Promise<ContextSuggestion[]> {
    const suggestions: ContextSuggestion[] = [];
    const queryLower = query.query.toLowerCase();

    // Search files
    const allFiles = await this.getAllFiles();

    for (const file of allFiles) {
      // Skip test files unless requested
      if (!query.includeTests && this.isTestFile(file)) {
        continue;
      }

      // Skip node_modules unless requested
      if (!query.includeNodeModules && file.includes('node_modules')) {
        continue;
      }

      // Filter by file type
      if (query.fileTypes && query.fileTypes.length > 0) {
        const ext = extname(file).slice(1);
        if (!query.fileTypes.includes(ext)) {
          continue;
        }
      }

      // Calculate relevance
      const relevance = this.calculateRelevance(file, queryLower);

      if (relevance > 0.1) {
        suggestions.push({
          type: 'file',
          value: file,
          relevance,
          reason: this.getRelevanceReason(file, queryLower),
        });
      }
    }

    // Sort by relevance and limit
    suggestions.sort((a, b) => b.relevance - a.relevance);
    return suggestions.slice(0, query.maxResults ?? 20);
  }

  /**
   * Track file access
   */
  trackFileAccess(path: string): void {
    const existing = this.recentFiles.get(path);

    if (existing) {
      existing.lastAccessed = new Date();
      existing.accessCount++;
    } else {
      this.recentFiles.set(path, {
        path,
        lastAccessed: new Date(),
        accessCount: 1,
      });
    }
  }

  /**
   * Get recent files
   */
  getRecentFiles(limit: number = 20): RecentFile[] {
    const files = Array.from(this.recentFiles.values());
    files.sort((a, b) => b.lastAccessed.getTime() - a.lastAccessed.getTime());
    return files.slice(0, limit);
  }

  /**
   * Find related files based on imports/dependencies
   */
  async findRelatedFiles(filePath: string): Promise<string[]> {
    const related: string[] = [];
    const dir = join(this.config.workspacePath, filePath, '..');

    try {
      // Look for files in same directory
      const dirFiles = await readdir(dir);
      for (const f of dirFiles) {
        const fullPath = relative(this.config.workspacePath, join(dir, f));
        if (fullPath !== filePath && this.isSourceFile(fullPath)) {
          related.push(fullPath);
        }
      }

      // Look for test file
      const testFile = this.getTestFilePath(filePath);
      if (testFile) {
        related.push(testFile);
      }
    } catch {
      // Directory doesn't exist
    }

    return related;
  }

  /**
   * Check if a file matches include/exclude patterns
   */
  async matchFiles(includePattern: string, excludePatterns: string[]): Promise<string[]> {
    const files: string[] = [];
    const allFiles = await this.getAllFiles();

    for (const file of allFiles) {
      // Check include pattern (simple glob matching)
      if (!this.matchesPattern(file, includePattern)) {
        continue;
      }

      // Check exclude patterns
      let excluded = false;
      for (const pattern of excludePatterns) {
        if (this.matchesPattern(file, pattern)) {
          excluded = true;
          break;
        }
      }

      if (!excluded) {
        files.push(file);
      }
    }

    return files;
  }

  /**
   * Get all files in workspace
   */
  private async getAllFiles(
    dir: string = this.config.workspacePath,
    depth: number = 0
  ): Promise<string[]> {
    if (depth > this.config.maxDepth) {
      return [];
    }

    const files: string[] = [];

    try {
      const entries = await readdir(dir, { withFileTypes: true });

      for (const entry of entries) {
        const fullPath = join(dir, entry.name);
        const relativePath = relative(this.config.workspacePath, fullPath);

        // Skip common directories
        if (entry.isDirectory()) {
          if (this.shouldSkipDirectory(entry.name)) {
            continue;
          }
          const subFiles = await this.getAllFiles(fullPath, depth + 1);
          files.push(...subFiles);
        } else if (entry.isFile()) {
          if (this.isSourceFile(relativePath)) {
            files.push(relativePath);
          }
        }
      }
    } catch {
      // Permission denied or other error
    }

    return files;
  }

  /**
   * Check if directory should be skipped
   */
  private shouldSkipDirectory(name: string): boolean {
    const skipDirs = [
      'node_modules',
      '.git',
      'dist',
      'build',
      'out',
      '.next',
      '.turbo',
      'coverage',
      '.nyc_output',
    ];
    return skipDirs.includes(name);
  }

  /**
   * Check if file is a source file
   */
  private isSourceFile(path: string): boolean {
    const ext = extname(path);
    return this.config.defaultExtensions.includes(ext);
  }

  /**
   * Check if file is a test file
   */
  private isTestFile(path: string): boolean {
    return (
      path.includes('.test.') ||
      path.includes('.spec.') ||
      path.includes('__tests__') ||
      path.includes('/test/')
    );
  }

  /**
   * Get corresponding test file path
   */
  private getTestFilePath(sourcePath: string): string | null {
    const ext = extname(sourcePath);
    const withoutExt = sourcePath.slice(0, -ext.length);
    return `${withoutExt}.test${ext}`;
  }

  /**
   * Simple glob pattern matching
   */
  private matchesPattern(path: string, pattern: string): boolean {
    // Convert glob pattern to regex
    const regexPattern = pattern
      .replace(/\./g, '\\.')
      .replace(/\*\*/g, '.*')
      .replace(/\*/g, '[^/]*')
      .replace(/\?/g, '.');

    const regex = new RegExp(`^${regexPattern}$`);
    return regex.test(path);
  }

  /**
   * Calculate relevance score for a file
   */
  private calculateRelevance(file: string, query: string): number {
    let score = 0;
    const fileLower = file.toLowerCase();

    // Exact filename match
    if (fileLower.includes(query)) {
      score += 0.5;
    }

    // Path segment match
    const segments = fileLower.split('/');
    for (const segment of segments) {
      if (segment.includes(query)) {
        score += 0.2;
      }
    }

    // Extension bonus
    if (fileLower.endsWith('.ts') || fileLower.endsWith('.tsx')) {
      score += 0.1;
    }

    // Penalty for deep paths
    score -= segments.length * 0.02;

    // Penalty for test files (unless query mentions test)
    if (this.isTestFile(file) && !query.includes('test')) {
      score -= 0.3;
    }

    return Math.max(0, Math.min(1, score));
  }

  /**
   * Get reason for relevance
   */
  private getRelevanceReason(file: string, query: string): string {
    const fileLower = file.toLowerCase();

    if (fileLower.includes(query)) {
      return `ファイル名に "${query}" を含む`;
    }

    const segments = fileLower.split('/');
    for (const segment of segments) {
      if (segment.includes(query)) {
        return `パスに "${query}" を含む`;
      }
    }

    return '関連ファイル';
  }
}

/**
 * Create a Space Context instance
 */
export function createSpaceContext(config: SpaceContextConfig): SpaceContext_ {
  return new SpaceContext_(config);
}
