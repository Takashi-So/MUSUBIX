/**
 * @fileoverview Refactor Cleaner Bridge Types for Agent Skills Integration
 * @traceability REQ-RC-001, REQ-RC-002, REQ-RC-003, REQ-RC-004
 */

// ============================================================================
// Dead Code Detection Types
// ============================================================================

/**
 * Dead code item risk level
 */
export type RiskLevel = 'safe' | 'caution' | 'danger';

/**
 * Dead code item type
 */
export type DeadCodeType = 
  | 'unused-file'
  | 'unused-export'
  | 'unused-dependency'
  | 'unused-type'
  | 'unused-variable'
  | 'unused-import';

/**
 * Dead code item
 */
export interface DeadCodeItem {
  /** Unique identifier */
  id: string;
  /** Item type */
  type: DeadCodeType;
  /** File path */
  path: string;
  /** Item name (export name, dependency name, etc.) */
  name: string;
  /** Line number (if applicable) */
  line?: number;
  /** Risk level */
  riskLevel: RiskLevel;
  /** Reason for classification */
  reason: string;
  /** Estimated size reduction (bytes) */
  estimatedSize?: number;
  /** Detection source (knip, depcheck, ts-prune) */
  detectedBy: string;
  /** Additional context */
  context?: Record<string, unknown>;
}

/**
 * Dead code analysis result
 */
export interface DeadCodeAnalysisResult {
  /** Analysis timestamp */
  analyzedAt: string;
  /** Analyzed paths */
  analyzedPaths: string[];
  /** All detected items */
  items: DeadCodeItem[];
  /** Summary by risk level */
  summary: {
    safe: number;
    caution: number;
    danger: number;
    total: number;
    estimatedTotalSize: number;
  };
  /** Tool versions used */
  toolVersions?: {
    knip?: string;
    depcheck?: string;
    tsPrune?: string;
  };
}

// ============================================================================
// Safety Check Types
// ============================================================================

/**
 * Safety check result
 */
export interface SafetyCheckResult {
  /** Item checked */
  item: DeadCodeItem;
  /** Is safe to delete */
  isSafe: boolean;
  /** Blocking reasons (if not safe) */
  blockingReasons: string[];
  /** Dynamic import references found */
  dynamicImportRefs: string[];
  /** Test references found */
  testRefs: string[];
  /** Documentation references found */
  docRefs: string[];
  /** Config references found */
  configRefs: string[];
}

/**
 * Batch safety check result
 */
export interface BatchSafetyCheckResult {
  /** Items safe to delete */
  safeItems: DeadCodeItem[];
  /** Items requiring caution */
  cautionItems: Array<{ item: DeadCodeItem; reasons: string[] }>;
  /** Items that should not be auto-deleted */
  dangerItems: Array<{ item: DeadCodeItem; reasons: string[] }>;
}

// ============================================================================
// Deletion Types
// ============================================================================

/**
 * Deletion action
 */
export interface DeletionAction {
  /** Action type */
  type: 'delete-file' | 'remove-export' | 'remove-import' | 'remove-dependency';
  /** Target path */
  path: string;
  /** Target name (if applicable) */
  name?: string;
  /** Git SHA before deletion */
  gitSha?: string;
  /** Backup created */
  backupPath?: string;
}

/**
 * Deletion log entry
 */
export interface DeletionLogEntry {
  /** Entry ID */
  id: string;
  /** Deletion timestamp */
  deletedAt: string;
  /** Deleted items */
  items: DeadCodeItem[];
  /** Actions taken */
  actions: DeletionAction[];
  /** Summary */
  summary: {
    filesDeleted: number;
    exportsRemoved: number;
    dependenciesRemoved: number;
    estimatedReduction: number;
  };
  /** Restoration info */
  restoration: {
    gitSha: string;
    command: string;
  };
}

// ============================================================================
// Report Types
// ============================================================================

/**
 * Dead code report format
 */
export type ReportFormat = 'markdown' | 'json' | 'text';

/**
 * Generated report
 */
export interface DeadCodeReport {
  /** Report format */
  format: ReportFormat;
  /** Report content */
  content: string;
  /** Generated at */
  generatedAt: string;
}

// ============================================================================
// Bridge Configuration
// ============================================================================

/**
 * Refactor cleaner bridge configuration
 */
export interface RefactorCleanerBridgeConfig {
  /** Report output path */
  reportOutputPath: string;
  /** Deletion log path */
  deletionLogPath: string;
  /** Patterns to ignore */
  ignorePatterns: string[];
  /** Auto-delete safe items */
  autoDeleteSafe: boolean;
  /** Confirm before caution items */
  confirmCaution: boolean;
  /** Never auto-delete danger items */
  neverDeleteDanger: boolean;
}

/**
 * Default configuration
 */
export const DEFAULT_REFACTOR_CLEANER_CONFIG: RefactorCleanerBridgeConfig = {
  reportOutputPath: '.reports/dead-code-analysis.md',
  deletionLogPath: 'docs/DELETION_LOG.md',
  ignorePatterns: [
    '**/index.ts',
    '**/index.js',
    '**/bin/**',
    '**/*.d.ts',
    '**/migrations/**',
    '**/__mocks__/**',
    '**/fixtures/**',
    '**/*.config.*',
  ],
  autoDeleteSafe: false,
  confirmCaution: true,
  neverDeleteDanger: true,
};

// ============================================================================
// Bridge Interface
// ============================================================================

/**
 * Refactor cleaner bridge interface
 */
export interface RefactorCleanerBridge {
  /**
   * Analyze dead code
   * @param rootPath Root path to analyze
   * @param options Analysis options
   * @returns Analysis result
   */
  analyze(rootPath: string, options?: {
    includeDeps?: boolean;
    tools?: Array<'knip' | 'depcheck' | 'ts-prune'>;
  }): Promise<DeadCodeAnalysisResult>;

  /**
   * Check if items are safe to delete
   * @param items Items to check
   * @param rootPath Root path
   * @returns Safety check results
   */
  checkSafety(items: DeadCodeItem[], rootPath: string): Promise<BatchSafetyCheckResult>;

  /**
   * Delete items
   * @param items Items to delete
   * @param rootPath Root path
   * @param options Deletion options
   * @returns Deletion log entry
   */
  deleteItems(
    items: DeadCodeItem[],
    rootPath: string,
    options?: { dryRun?: boolean; backup?: boolean }
  ): Promise<DeletionLogEntry>;

  /**
   * Generate report
   * @param result Analysis result
   * @param format Report format
   * @returns Generated report
   */
  generateReport(result: DeadCodeAnalysisResult, format?: ReportFormat): DeadCodeReport;

  /**
   * Append to deletion log
   * @param entry Deletion log entry
   */
  appendDeletionLog(entry: DeletionLogEntry): Promise<void>;

  /**
   * Get configuration
   */
  getConfig(): RefactorCleanerBridgeConfig;

  /**
   * Update configuration
   * @param config Partial config to update
   */
  updateConfig(config: Partial<RefactorCleanerBridgeConfig>): void;

  /**
   * Classify item risk level
   * @param item Dead code item
   * @param safetyCheck Safety check result
   * @returns Updated risk level
   */
  classifyRisk(item: DeadCodeItem, safetyCheck: SafetyCheckResult): RiskLevel;
}
