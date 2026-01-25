/**
 * Codemap Types
 *
 * Type definitions for codemap skill
 *
 * @see REQ-CM-001 - Repository Structure Analysis
 * @see REQ-CM-002 - Module Analysis
 * @see REQ-CM-003 - Codemap Generation
 * @see REQ-CM-004 - Codemap Diff Threshold & Report
 */

/**
 * Module type
 */
export type ModuleType =
  | 'frontend'
  | 'backend'
  | 'database'
  | 'integration'
  | 'worker'
  | 'shared'
  | 'unknown';

/**
 * Framework detection result
 */
export interface FrameworkInfo {
  readonly name: string;
  readonly version?: string;
  readonly patterns: string[];
}

/**
 * Repository structure
 *
 * @see REQ-CM-001 - Repository Structure Analysis
 */
export interface RepositoryStructure {
  readonly name: string;
  readonly root: string;
  readonly workspaces: string[];
  readonly directories: DirectoryInfo[];
  readonly entryPoints: EntryPoint[];
  readonly frameworks: FrameworkInfo[];
  readonly monorepo: boolean;
}

/**
 * Directory info
 */
export interface DirectoryInfo {
  readonly path: string;
  readonly purpose: string;
  readonly fileCount: number;
  readonly languages: string[];
}

/**
 * Entry point
 */
export interface EntryPoint {
  readonly path: string;
  readonly type: 'main' | 'cli' | 'server' | 'test' | 'build';
  readonly description?: string;
}

/**
 * Export info
 */
export interface ExportInfo {
  readonly name: string;
  readonly type: 'function' | 'class' | 'interface' | 'type' | 'const' | 'default';
  readonly file: string;
  readonly line?: number;
}

/**
 * Import info
 */
export interface ImportInfo {
  readonly module: string;
  readonly isExternal: boolean;
  readonly importedNames: string[];
  readonly file: string;
}

/**
 * Route info
 */
export interface RouteInfo {
  readonly path: string;
  readonly method: 'GET' | 'POST' | 'PUT' | 'DELETE' | 'PATCH' | 'ALL';
  readonly handler: string;
  readonly file: string;
}

/**
 * Database model info
 */
export interface DatabaseModelInfo {
  readonly name: string;
  readonly type: 'table' | 'collection' | 'entity';
  readonly file: string;
  readonly fields?: string[];
}

/**
 * Worker info
 */
export interface WorkerInfo {
  readonly name: string;
  readonly type: 'cron' | 'queue' | 'websocket' | 'other';
  readonly file: string;
  readonly schedule?: string;
}

/**
 * Module analysis result
 *
 * @see REQ-CM-002 - Module Analysis
 */
export interface ModuleAnalysis {
  readonly path: string;
  readonly type: ModuleType;
  readonly exports: ExportInfo[];
  readonly imports: ImportInfo[];
  readonly routes: RouteInfo[];
  readonly databaseModels: DatabaseModelInfo[];
  readonly workers: WorkerInfo[];
  readonly dependencies: string[];
  readonly devDependencies: string[];
}

/**
 * Codemap document
 *
 * @see REQ-CM-003 - Codemap Generation
 */
export interface CodemapDocument {
  readonly name: string;
  readonly path: string;
  readonly content: string;
  readonly generatedAt: Date;
}

/**
 * Codemap diff result
 *
 * @see REQ-CM-004 - Codemap Diff Threshold & Report
 */
export interface CodemapDiff {
  readonly documentName: string;
  readonly previousHash: string;
  readonly currentHash: string;
  readonly diffPercent: number;
  readonly additions: number;
  readonly deletions: number;
  readonly requiresApproval: boolean;
}

/**
 * Codemap generation result
 */
export interface CodemapGenerationResult {
  readonly documents: CodemapDocument[];
  readonly diffs: CodemapDiff[];
  readonly totalDiffPercent: number;
  readonly generatedAt: Date;
}

/**
 * Codemap configuration
 */
export interface CodemapConfig {
  readonly projectRoot: string;
  readonly outputDir: string;
  readonly diffThresholdPercent: number;
  readonly includePatterns: string[];
  readonly excludePatterns: string[];
}

/**
 * Default codemap configuration
 */
export const DEFAULT_CODEMAP_CONFIG: CodemapConfig = {
  projectRoot: '.',
  outputDir: 'docs/CODEMAPS',
  diffThresholdPercent: 30,
  includePatterns: ['**/*.ts', '**/*.tsx', '**/*.js', '**/*.jsx'],
  excludePatterns: [
    '**/node_modules/**',
    '**/dist/**',
    '**/build/**',
    '**/*.test.ts',
    '**/*.spec.ts',
  ],
};

/**
 * Codemap manager interface
 */
export interface CodemapManager {
  /**
   * Analyze repository structure
   *
   * @returns Repository structure
   */
  analyzeRepository(): Promise<RepositoryStructure>;

  /**
   * Analyze a module
   *
   * @param modulePath - Path to module
   * @returns Module analysis
   */
  analyzeModule(modulePath: string): Promise<ModuleAnalysis>;

  /**
   * Generate codemap documents
   *
   * @returns Generation result
   */
  generateCodemap(): Promise<CodemapGenerationResult>;

  /**
   * Calculate diff between existing and new codemap
   *
   * @param newContent - New content
   * @param existingContent - Existing content
   * @returns Diff information
   */
  calculateDiff(newContent: string, existingContent: string): CodemapDiff;

  /**
   * Save codemap documents
   *
   * @param result - Generation result
   * @returns Saved file paths
   */
  saveCodemap(result: CodemapGenerationResult): Promise<string[]>;

  /**
   * Get configuration
   */
  getConfig(): CodemapConfig;
}
