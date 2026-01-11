/**
 * @fileoverview CodeDB Builder - Build CodeDB from source files
 * @module @nahisaho/musubix-security/codedb/builder
 * @trace TSK-014, REQ-SEC-CODEDB-003
 */

import { CodeDB, type CodeDBOptions } from './database.js';
import {
  detectLanguage,
  getExtractor,
  registerExtractor,
  type SupportedLanguage,
} from '../extractors/index.js';
import type { BaseExtractor, ExtractionResult, ExtractorOptions } from '../extractors/base-extractor.js';

/**
 * Builder options
 */
export interface BuilderOptions extends CodeDBOptions {
  /** Languages to extract (default: auto-detect) */
  languages?: SupportedLanguage[];
  /** Extractor options */
  extractorOptions?: ExtractorOptions;
  /** Include patterns */
  include?: string[];
  /** Exclude patterns */
  exclude?: string[];
  /** Progress callback */
  onProgress?: (progress: BuildProgress) => void;
  /** Error callback */
  onError?: (error: BuildError) => void;
  /** Parallel processing */
  parallel?: boolean;
  /** Max concurrent extractions */
  maxConcurrent?: number;
}

/**
 * Build progress
 */
export interface BuildProgress {
  /** Current file being processed */
  currentFile: string;
  /** Files processed */
  processed: number;
  /** Total files */
  total: number;
  /** Percentage complete */
  percentage: number;
  /** Phase */
  phase: 'scanning' | 'parsing' | 'analyzing' | 'indexing' | 'complete';
}

/**
 * Build error
 */
export interface BuildError {
  /** File path */
  file: string;
  /** Error message */
  message: string;
  /** Error type */
  type: 'parse' | 'extract' | 'index' | 'unknown';
  /** Original error */
  originalError?: Error;
}

/**
 * Build result
 */
export interface BuildResult {
  /** Built database */
  database: CodeDB;
  /** Build duration (ms) */
  duration: number;
  /** Files processed */
  filesProcessed: number;
  /** Files with errors */
  filesWithErrors: number;
  /** Errors encountered */
  errors: BuildError[];
  /** Statistics */
  statistics: {
    astNodes: number;
    dfgNodes: number;
    cfgBlocks: number;
    symbols: number;
  };
}

/**
 * Source file input
 */
export interface SourceFile {
  /** File path */
  path: string;
  /** File content */
  content: string;
  /** Language (optional, auto-detected if not provided) */
  language?: SupportedLanguage;
}

/**
 * CodeDB Builder
 */
export class CodeDBBuilder {
  private options: BuilderOptions;
  private errors: BuildError[] = [];
  private extractors: Map<SupportedLanguage, BaseExtractor> = new Map();

  /**
   * Create a new builder
   */
  constructor(options: BuilderOptions = {}) {
    this.options = {
      parallel: false,
      maxConcurrent: 4,
      ...options,
    };
  }

  /**
   * Build CodeDB from source files
   */
  async build(files: SourceFile[]): Promise<BuildResult> {
    const startTime = Date.now();
    const database = new CodeDB(this.options);
    this.errors = [];

    // Filter files
    const filteredFiles = this.filterFiles(files);
    const total = filteredFiles.length;

    // Report scanning phase
    this.reportProgress({
      currentFile: '',
      processed: 0,
      total,
      percentage: 0,
      phase: 'scanning',
    });

    // Detect languages
    const languagesUsed = new Set<string>();

    // Process files
    if (this.options.parallel && total > 1) {
      await this.processFilesParallel(filteredFiles, database, languagesUsed);
    } else {
      await this.processFilesSequential(filteredFiles, database, languagesUsed);
    }

    // Update database metadata
    database.languages = Array.from(languagesUsed);

    // Indexing phase
    this.reportProgress({
      currentFile: '',
      processed: total,
      total,
      percentage: 100,
      phase: 'indexing',
    });

    // Build cross-file references
    await this.buildCrossReferences(database);

    // Complete
    this.reportProgress({
      currentFile: '',
      processed: total,
      total,
      percentage: 100,
      phase: 'complete',
    });

    const stats = database.getStatistics();

    return {
      database,
      duration: Date.now() - startTime,
      filesProcessed: total - this.errors.length,
      filesWithErrors: this.errors.length,
      errors: this.errors,
      statistics: {
        astNodes: stats.astNodes,
        dfgNodes: stats.dfgNodes,
        cfgBlocks: stats.cfgBlocks,
        symbols: stats.symbols,
      },
    };
  }

  /**
   * Process files sequentially
   */
  private async processFilesSequential(
    files: SourceFile[],
    database: CodeDB,
    languagesUsed: Set<string>,
  ): Promise<void> {
    const total = files.length;

    for (let i = 0; i < total; i++) {
      const file = files[i];
      this.reportProgress({
        currentFile: file.path,
        processed: i,
        total,
        percentage: Math.round((i / total) * 100),
        phase: 'parsing',
      });

      await this.processFile(file, database, languagesUsed);
    }
  }

  /**
   * Process files in parallel
   */
  private async processFilesParallel(
    files: SourceFile[],
    database: CodeDB,
    languagesUsed: Set<string>,
  ): Promise<void> {
    const total = files.length;
    const maxConcurrent = this.options.maxConcurrent ?? 4;
    let processed = 0;

    // Process in batches
    for (let i = 0; i < total; i += maxConcurrent) {
      const batch = files.slice(i, i + maxConcurrent);

      await Promise.all(
        batch.map(async (file) => {
          this.reportProgress({
            currentFile: file.path,
            processed,
            total,
            percentage: Math.round((processed / total) * 100),
            phase: 'parsing',
          });

          await this.processFile(file, database, languagesUsed);
          processed++;
        }),
      );
    }
  }

  /**
   * Process a single file
   */
  private async processFile(
    file: SourceFile,
    database: CodeDB,
    languagesUsed: Set<string>,
  ): Promise<void> {
    try {
      // Detect language
      const language = file.language ?? detectLanguage(file.path);
      if (!language) {
        return; // Skip unsupported file types
      }

      // Get or create extractor
      let extractor = this.extractors.get(language);
      if (!extractor) {
        extractor = getExtractor(language, this.options.extractorOptions);
        if (extractor) {
          this.extractors.set(language, extractor);
        }
      }

      if (!extractor) {
        return; // No extractor available for this language
      }

      languagesUsed.add(language);

      // Extract code information
      const result = await extractor.extract(file.content, file.path);

      // Store results in database
      this.storeExtractionResult(database, file.path, result);
    } catch (error) {
      const buildError: BuildError = {
        file: file.path,
        message: error instanceof Error ? error.message : String(error),
        type: 'extract',
        originalError: error instanceof Error ? error : undefined,
      };
      this.errors.push(buildError);
      this.options.onError?.(buildError);
    }
  }

  /**
   * Store extraction result in database
   */
  private storeExtractionResult(
    database: CodeDB,
    filePath: string,
    result: ExtractionResult,
  ): void {
    // Store AST
    database.addAST(filePath, result.ast);

    // Store CFG
    database.addCFG(filePath, result.cfg);

    // Store DFG
    database.addDFG(filePath, result.dfg);

    // Store symbol table
    database.addSymbolTable(filePath, result.symbols);

    // Store taint paths
    for (const path of result.taintPaths ?? []) {
      database.addTaintPath(path);
    }
  }

  /**
   * Build cross-file references
   */
  private async buildCrossReferences(database: CodeDB): Promise<void> {
    const globalSymbols = database.getGlobalSymbolTable();

    // Build call graph edges across files
    for (const filePath of database.files) {
      const ast = database.getAST(filePath);
      if (!ast) continue;

      // Find function calls
      this.findCallsAndBuildEdges(database, filePath, ast, globalSymbols);
    }

    // Build type hierarchy across files
    for (const [typeName, typeInfo] of database.getTypeStore().types) {
      if (typeInfo.supertypes) {
        for (const supertype of typeInfo.supertypes) {
          const supertypeInfo = database.getTypeStore().types.get(supertype);
          if (supertypeInfo) {
            // Type relationship exists
          }
        }
      }
    }
  }

  /**
   * Find function calls and build call graph edges
   */
  private findCallsAndBuildEdges(
    database: CodeDB,
    filePath: string,
    ast: ASTNode,
    globalSymbols: GlobalSymbolTable,
  ): void {
    const visit = (node: ASTNode) => {
      // Check for call expressions
      if (
        node.type === 'call_expression' ||
        node.type === 'method_invocation'
      ) {
        const calleeName = node.metadata?.callee ?? node.metadata?.methodName;
        if (calleeName && typeof calleeName === 'string') {
          // Try to resolve callee
          const callerFunction = this.findEnclosingFunction(ast, node);
          if (callerFunction) {
            const callerId = callerFunction.id;

            // Find callee definition
            const calleeFiles = database.findFilesBySymbol(calleeName);
            for (const calleeFile of calleeFiles) {
              const calleeId = `${calleeFile}#${calleeName}`;
              database.addCallEdge(
                callerId,
                filePath,
                calleeId,
                calleeFile,
                { line: node.location.startLine, column: node.location.startColumn },
              );
            }
          }
        }
      }

      for (const child of node.children) {
        visit(child);
      }
    };

    visit(ast);
  }

  /**
   * Find enclosing function for a node
   */
  private findEnclosingFunction(ast: ASTNode, targetNode: ASTNode): ASTNode | undefined {
    let current: ASTNode | undefined = targetNode;

    while (current) {
      if (
        current.type === 'function_declaration' ||
        current.type === 'method_declaration' ||
        current.type === 'func_literal' ||
        current.type === 'arrow_function' ||
        current.type === 'function_expression'
      ) {
        return current;
      }
      current = current.parent;
    }

    return undefined;
  }

  /**
   * Filter files based on include/exclude patterns
   */
  private filterFiles(files: SourceFile[]): SourceFile[] {
    return files.filter((file) => {
      // Check exclude patterns
      if (this.options.exclude) {
        for (const pattern of this.options.exclude) {
          if (this.matchPattern(file.path, pattern)) {
            return false;
          }
        }
      }

      // Check include patterns
      if (this.options.include) {
        for (const pattern of this.options.include) {
          if (this.matchPattern(file.path, pattern)) {
            return true;
          }
        }
        return false;
      }

      return true;
    });
  }

  /**
   * Match file path against pattern
   */
  private matchPattern(filePath: string, pattern: string): boolean {
    // Simple glob matching
    const regexPattern = pattern
      .replace(/\./g, '\\.')
      .replace(/\*/g, '.*')
      .replace(/\?/g, '.');
    return new RegExp(`^${regexPattern}$`).test(filePath);
  }

  /**
   * Report progress
   */
  private reportProgress(progress: BuildProgress): void {
    this.options.onProgress?.(progress);
  }
}

// Import GlobalSymbolTable type and ASTNode
import type { GlobalSymbolTable } from '../types/codedb.js';
import type { ASTNode } from '../extractors/base-extractor.js';

/**
 * Create a new CodeDB builder
 */
export function createBuilder(options?: BuilderOptions): CodeDBBuilder {
  return new CodeDBBuilder(options);
}

/**
 * Build CodeDB from source files (convenience function)
 */
export async function buildCodeDB(
  files: SourceFile[],
  options?: BuilderOptions,
): Promise<BuildResult> {
  const builder = new CodeDBBuilder(options);
  return builder.build(files);
}
