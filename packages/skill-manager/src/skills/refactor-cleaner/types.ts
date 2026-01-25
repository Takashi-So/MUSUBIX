/**
 * Refactor Cleaner Types
 *
 * Type definitions for refactor cleaner skill
 *
 * @see REQ-RC-001 - Dead Code Detection
 * @see REQ-RC-002 - Safe Deletion
 * @see REQ-RC-003 - Deletion Log
 * @see REQ-RC-004 - Risk Classification & Report
 */

/**
 * Dead code type
 */
export type DeadCodeType =
  | 'unused-file'
  | 'unused-export'
  | 'unused-dependency'
  | 'unused-variable'
  | 'unused-function'
  | 'unused-import';

/**
 * Risk level for deletion
 *
 * @see REQ-RC-004 - Risk Classification
 */
export type RiskLevel = 'safe' | 'caution' | 'danger';

/**
 * Dead code item
 *
 * @see REQ-RC-001 - Dead Code Detection
 */
export interface DeadCodeItem {
  readonly id: string;
  readonly type: DeadCodeType;
  readonly path: string;
  readonly name?: string;
  readonly line?: number;
  readonly riskLevel: RiskLevel;
  readonly reason: string;
  readonly detectedBy: 'knip' | 'depcheck' | 'ts-prune' | 'custom';
}

/**
 * Reference check result
 *
 * @see REQ-RC-002 - Safe Deletion
 */
export interface ReferenceCheckResult {
  readonly item: DeadCodeItem;
  readonly hasDynamicImport: boolean;
  readonly hasTestReference: boolean;
  readonly hasDocReference: boolean;
  readonly isPublicApi: boolean;
  readonly isSafeToDelete: boolean;
  readonly warnings: string[];
}

/**
 * Deletion log entry
 *
 * @see REQ-RC-003 - Deletion Log
 */
export interface DeletionLogEntry {
  readonly timestamp: Date;
  readonly item: DeadCodeItem;
  readonly gitSha: string;
  readonly deletedBy: string;
  readonly reason: string;
  readonly canRestore: boolean;
}

/**
 * Dead code analysis report
 *
 * @see REQ-RC-004 - Risk Classification & Report
 */
export interface DeadCodeAnalysisReport {
  readonly id: string;
  readonly analyzedAt: Date;
  readonly totalItems: number;
  readonly byRisk: {
    readonly safe: DeadCodeItem[];
    readonly caution: DeadCodeItem[];
    readonly danger: DeadCodeItem[];
  };
  readonly byType: Record<DeadCodeType, number>;
  readonly estimatedSavings: {
    readonly files: number;
    readonly lines: number;
    readonly dependencies: number;
  };
}

/**
 * Deletion result
 */
export interface DeletionResult {
  readonly success: boolean;
  readonly deletedItems: DeadCodeItem[];
  readonly skippedItems: DeadCodeItem[];
  readonly errors: string[];
  readonly gitSha?: string;
}

/**
 * Refactor cleaner configuration
 */
export interface RefactorCleanerConfig {
  readonly projectRoot: string;
  readonly deletionLogPath: string;
  readonly reportPath: string;
  readonly useKnip: boolean;
  readonly useDepcheck: boolean;
  readonly useTsPrune: boolean;
  readonly autoDeleteSafe: boolean;
  readonly excludePatterns: string[];
}

/**
 * Default refactor cleaner configuration
 */
export const DEFAULT_REFACTOR_CLEANER_CONFIG: RefactorCleanerConfig = {
  projectRoot: '.',
  deletionLogPath: 'docs/DELETION_LOG.md',
  reportPath: '.reports/dead-code-analysis.md',
  useKnip: true,
  useDepcheck: true,
  useTsPrune: true,
  autoDeleteSafe: false,
  excludePatterns: ['**/node_modules/**', '**/dist/**', '**/*.test.ts'],
};

/**
 * Refactor cleaner manager interface
 */
export interface RefactorCleanerManager {
  /**
   * Detect dead code
   *
   * @returns Array of dead code items
   */
  detectDeadCode(): Promise<DeadCodeItem[]>;

  /**
   * Check if item is safe to delete
   *
   * @param item - Dead code item to check
   * @returns Reference check result
   */
  checkReferences(item: DeadCodeItem): Promise<ReferenceCheckResult>;

  /**
   * Delete items safely
   *
   * @param items - Items to delete
   * @param force - Skip safety checks
   * @returns Deletion result
   */
  deleteItems(items: DeadCodeItem[], force?: boolean): Promise<DeletionResult>;

  /**
   * Generate analysis report
   *
   * @param items - Dead code items
   * @returns Analysis report
   */
  generateReport(items: DeadCodeItem[]): DeadCodeAnalysisReport;

  /**
   * Log deletion
   *
   * @param entry - Deletion log entry
   */
  logDeletion(entry: DeletionLogEntry): Promise<void>;

  /**
   * Get deletion log
   *
   * @returns Array of deletion log entries
   */
  getDeletionLog(): Promise<DeletionLogEntry[]>;

  /**
   * Classify risk level
   *
   * @param item - Dead code item
   * @returns Risk level
   */
  classifyRisk(item: DeadCodeItem): RiskLevel;

  /**
   * Get configuration
   */
  getConfig(): RefactorCleanerConfig;
}
