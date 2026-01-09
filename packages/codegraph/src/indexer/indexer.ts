/**
 * @nahisaho/musubix-codegraph - Indexer
 *
 * Repository and directory indexing
 *
 * @see REQ-CG-IDX-001 - Repository indexing
 * @see REQ-CG-IDX-002 - Incremental indexing
 * @see DES-CG-004
 * @see TSK-CG-030
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import type {
  IndexResult,
  IndexError,
  IndexerOptions,
  IndexProgress,
} from '../types.js';
import { getLanguageFromExtension } from '../types.js';
import type { ASTParser } from '../parser/index.js';
import type { GraphEngine } from '../graph/index.js';

/**
 * Progress callback type
 */
export type ProgressCallback = (progress: IndexProgress) => void;

/**
 * Indexer for code repositories
 *
 * Scans directories, parses files, and builds the code graph.
 */
export class Indexer {
  private parser: ASTParser;
  private graph: GraphEngine;
  private options: Required<IndexerOptions>;
  private progressCallback: ProgressCallback | null = null;

  constructor(
    parser: ASTParser,
    graph: GraphEngine,
    options: Partial<IndexerOptions> = {}
  ) {
    this.parser = parser;
    this.graph = graph;
    this.options = {
      ignorePatterns: options.ignorePatterns ?? [
        '**/node_modules/**',
        '**/.git/**',
        '**/dist/**',
        '**/build/**',
        '**/coverage/**',
        '**/*.min.js',
        '**/*.bundle.js',
      ],
      maxFileSize: options.maxFileSize ?? 1024 * 1024, // 1MB
      parallelism: options.parallelism ?? 4,
    };
  }

  /**
   * Set progress callback
   */
  onProgress(callback: ProgressCallback): void {
    this.progressCallback = callback;
  }

  /**
   * Index a repository or directory
   */
  async indexRepository(repoPath: string): Promise<IndexResult> {
    const startTime = Date.now();
    const errors: IndexError[] = [];
    let entitiesIndexed = 0;
    let relationsIndexed = 0;
    let filesProcessed = 0;

    // Discover files
    const files = await this.discoverFiles(repoPath);
    const total = files.length;

    // Process files
    for (let i = 0; i < files.length; i++) {
      const file = files[i];

      try {
        const result = await this.parser.parseFile(file);

        if (result.errors.length > 0) {
          for (const error of result.errors) {
            errors.push({
              filePath: file,
              message: error.message,
              line: error.line,
            });
          }
        }

        // Add to graph
        await this.graph.addParseResults(result.entities, result.relations);

        entitiesIndexed += result.entities.length;
        relationsIndexed += result.relations.length;
        filesProcessed++;

        // Report progress
        if (this.progressCallback) {
          const progress: IndexProgress = {
            processed: i + 1,
            total,
            currentFile: file,
            percentage: Math.round(((i + 1) / total) * 100),
          };
          this.progressCallback(progress);
        }
      } catch (error) {
        errors.push({
          filePath: file,
          message: error instanceof Error ? error.message : String(error),
        });
      }
    }

    return {
      success: errors.length === 0,
      entitiesIndexed,
      relationsIndexed,
      filesProcessed,
      durationMs: Date.now() - startTime,
      errors,
    };
  }

  /**
   * Index a single file
   */
  async indexFile(filePath: string): Promise<IndexResult> {
    const startTime = Date.now();
    const errors: IndexError[] = [];

    try {
      const result = await this.parser.parseFile(filePath);

      if (result.errors.length > 0) {
        for (const error of result.errors) {
          errors.push({
            filePath,
            message: error.message,
            line: error.line,
          });
        }
      }

      await this.graph.addParseResults(result.entities, result.relations);

      return {
        success: errors.length === 0,
        entitiesIndexed: result.entities.length,
        relationsIndexed: result.relations.length,
        filesProcessed: 1,
        durationMs: Date.now() - startTime,
        errors,
      };
    } catch (error) {
      return {
        success: false,
        entitiesIndexed: 0,
        relationsIndexed: 0,
        filesProcessed: 0,
        durationMs: Date.now() - startTime,
        errors: [{
          filePath,
          message: error instanceof Error ? error.message : String(error),
        }],
      };
    }
  }

  /**
   * Discover all parseable files in directory
   */
  private async discoverFiles(dirPath: string): Promise<string[]> {
    const files: string[] = [];
    await this.walkDirectory(dirPath, files);
    return files;
  }

  /**
   * Recursively walk directory
   */
  private async walkDirectory(dirPath: string, files: string[]): Promise<void> {
    try {
      const entries = await fs.readdir(dirPath, { withFileTypes: true });

      for (const entry of entries) {
        const fullPath = path.join(dirPath, entry.name);

        // Check exclusions
        if (this.shouldExclude(fullPath)) {
          continue;
        }

        if (entry.isDirectory()) {
          await this.walkDirectory(fullPath, files);
        } else if (entry.isFile()) {
          const language = getLanguageFromExtension(fullPath);
          if (language) {
            files.push(fullPath);
          }
        }
      }
    } catch {
      // Skip directories we can't read
    }
  }

  /**
   * Check if path should be excluded
   */
  private shouldExclude(filePath: string): boolean {
    for (const pattern of this.options.ignorePatterns) {
      if (this.matchGlob(filePath, pattern)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Simple glob matching
   */
  private matchGlob(filePath: string, pattern: string): boolean {
    // Convert glob to regex
    const regexPattern = pattern
      .replace(/\*\*/g, '<<<DOUBLESTAR>>>')
      .replace(/\*/g, '[^/]*')
      .replace(/<<<DOUBLESTAR>>>/g, '.*')
      .replace(/\?/g, '.');

    const regex = new RegExp(regexPattern);
    return regex.test(filePath);
  }
}
