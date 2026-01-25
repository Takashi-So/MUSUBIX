/**
 * Refactor Cleaner Implementation
 *
 * Dead code detection, safe deletion, and cleanup management
 *
 * @see REQ-RC-001 - Dead Code Detection
 * @see REQ-RC-002 - Safe Deletion
 * @see REQ-RC-003 - Deletion Log
 * @see REQ-RC-004 - Risk Classification & Report
 */

import type {
  RefactorCleanerManager,
  RefactorCleanerConfig,
  DeadCodeItem,
  DeadCodeType,
  ReferenceCheckResult,
  DeletionResult,
  DeadCodeAnalysisReport,
  DeletionLogEntry,
  RiskLevel,
} from './types.js';
import { DEFAULT_REFACTOR_CLEANER_CONFIG } from './types.js';
import { randomUUID } from 'crypto';

/**
 * Create refactor cleaner manager
 *
 * @param config - Configuration options
 * @returns RefactorCleanerManager instance
 */
export function createRefactorCleanerManager(
  config: Partial<RefactorCleanerConfig> = {},
): RefactorCleanerManager {
  const fullConfig: RefactorCleanerConfig = {
    ...DEFAULT_REFACTOR_CLEANER_CONFIG,
    ...config,
  };

  const deletionLog: DeletionLogEntry[] = [];

  /**
   * Classify risk level based on dead code item
   * @see REQ-RC-004
   */
  const classifyRisk = (item: DeadCodeItem): RiskLevel => {
    // Public APIs are dangerous to delete
    if (item.type === 'unused-export') {
      return 'danger';
    }

    // Unused files need caution
    if (item.type === 'unused-file') {
      return 'caution';
    }

    // Unused dependencies are generally safe
    if (item.type === 'unused-dependency') {
      return 'safe';
    }

    // Unused imports are safe
    if (item.type === 'unused-import') {
      return 'safe';
    }

    // Unused variables and functions need more analysis
    if (item.type === 'unused-variable' || item.type === 'unused-function') {
      return 'caution';
    }

    return 'caution';
  };

  /**
   * Detect dead code using configured tools
   * @see REQ-RC-001
   */
  const detectDeadCode = async (): Promise<DeadCodeItem[]> => {
    const items: DeadCodeItem[] = [];

    // Note: In real implementation, would run:
    // - knip (if useKnip)
    // - depcheck (if useDepcheck)
    // - ts-prune (if useTsPrune)
    // For now, return empty array (placeholder for integration)

    // Example of how items would be structured:
    // items.push({
    //   id: randomUUID(),
    //   type: 'unused-file',
    //   path: 'src/old-module.ts',
    //   riskLevel: 'caution',
    //   reason: 'No imports found',
    //   detectedBy: 'knip',
    // });

    return items;
  };

  /**
   * Check references for safe deletion
   * @see REQ-RC-002
   */
  const checkReferences = async (item: DeadCodeItem): Promise<ReferenceCheckResult> => {
    const warnings: string[] = [];

    // Check for dynamic imports (require(), import())
    const hasDynamicImport = false; // Would scan for dynamic imports

    // Check for test references
    const hasTestReference = item.path.includes('.test.') || item.path.includes('.spec.');

    // Check for documentation references
    const hasDocReference = false; // Would scan docs

    // Check if public API (exported from index)
    const isPublicApi = item.type === 'unused-export';

    if (hasDynamicImport) {
      warnings.push('May have dynamic imports');
    }
    if (isPublicApi) {
      warnings.push('Public API - may break external consumers');
    }

    const isSafeToDelete =
      !hasDynamicImport && !isPublicApi && item.riskLevel === 'safe';

    return {
      item,
      hasDynamicImport,
      hasTestReference,
      hasDocReference,
      isPublicApi,
      isSafeToDelete,
      warnings,
    };
  };

  /**
   * Delete items safely
   * @see REQ-RC-002
   */
  const deleteItems = async (
    items: DeadCodeItem[],
    force = false,
  ): Promise<DeletionResult> => {
    const deletedItems: DeadCodeItem[] = [];
    const skippedItems: DeadCodeItem[] = [];
    const errors: string[] = [];

    for (const item of items) {
      if (!force) {
        const check = await checkReferences(item);
        if (!check.isSafeToDelete) {
          skippedItems.push(item);
          continue;
        }
      }

      try {
        // In real implementation, would:
        // 1. Git add/commit before deletion
        // 2. Delete the file/code
        // 3. Update imports
        deletedItems.push(item);
      } catch (error) {
        errors.push(`Failed to delete ${item.path}: ${String(error)}`);
        skippedItems.push(item);
      }
    }

    return {
      success: errors.length === 0,
      deletedItems,
      skippedItems,
      errors,
      gitSha: deletedItems.length > 0 ? 'HEAD' : undefined,
    };
  };

  /**
   * Generate analysis report
   * @see REQ-RC-004
   */
  const generateReport = (items: DeadCodeItem[]): DeadCodeAnalysisReport => {
    const byRisk = {
      safe: items.filter((i) => i.riskLevel === 'safe'),
      caution: items.filter((i) => i.riskLevel === 'caution'),
      danger: items.filter((i) => i.riskLevel === 'danger'),
    };

    const byType = items.reduce(
      (acc, item) => {
        acc[item.type] = (acc[item.type] || 0) + 1;
        return acc;
      },
      {} as Record<DeadCodeType, number>,
    );

    return {
      id: randomUUID(),
      analyzedAt: new Date(),
      totalItems: items.length,
      byRisk,
      byType,
      estimatedSavings: {
        files: items.filter((i) => i.type === 'unused-file').length,
        lines: 0, // Would calculate from file sizes
        dependencies: items.filter((i) => i.type === 'unused-dependency').length,
      },
    };
  };

  /**
   * Log deletion
   * @see REQ-RC-003
   */
  const logDeletion = async (entry: DeletionLogEntry): Promise<void> => {
    deletionLog.push(entry);
    // In real implementation, would append to DELETION_LOG.md
  };

  /**
   * Get deletion log
   * @see REQ-RC-003
   */
  const getDeletionLog = async (): Promise<DeletionLogEntry[]> => {
    return [...deletionLog];
  };

  return {
    detectDeadCode,
    checkReferences,
    deleteItems,
    generateReport,
    logDeletion,
    getDeletionLog,
    classifyRisk,
    getConfig: () => fullConfig,
  };
}

/**
 * Format dead code analysis report as Markdown
 *
 * @param report - Analysis report
 * @returns Markdown string
 */
export function formatDeadCodeReportMarkdown(report: DeadCodeAnalysisReport): string {
  const lines: string[] = [
    '# Dead Code Analysis Report',
    '',
    `**Analyzed:** ${report.analyzedAt.toISOString()}`,
    `**Total Items:** ${report.totalItems}`,
    '',
    '## Risk Summary',
    '',
    '| Risk Level | Count | Percentage |',
    '|------------|-------|------------|',
    `| 🟢 Safe | ${report.byRisk.safe.length} | ${((report.byRisk.safe.length / report.totalItems) * 100).toFixed(1)}% |`,
    `| 🟡 Caution | ${report.byRisk.caution.length} | ${((report.byRisk.caution.length / report.totalItems) * 100).toFixed(1)}% |`,
    `| 🔴 Danger | ${report.byRisk.danger.length} | ${((report.byRisk.danger.length / report.totalItems) * 100).toFixed(1)}% |`,
    '',
    '## By Type',
    '',
    '| Type | Count |',
    '|------|-------|',
  ];

  for (const [type, count] of Object.entries(report.byType)) {
    lines.push(`| ${type} | ${count} |`);
  }

  lines.push('', '## Estimated Savings', '');
  lines.push(`- **Files:** ${report.estimatedSavings.files}`);
  lines.push(`- **Dependencies:** ${report.estimatedSavings.dependencies}`);

  if (report.byRisk.safe.length > 0) {
    lines.push('', '## Safe to Delete', '');
    for (const item of report.byRisk.safe) {
      lines.push(`- \`${item.path}\` - ${item.reason}`);
    }
  }

  if (report.byRisk.caution.length > 0) {
    lines.push('', '## Needs Review (Caution)', '');
    for (const item of report.byRisk.caution) {
      lines.push(`- \`${item.path}\` - ${item.reason}`);
    }
  }

  if (report.byRisk.danger.length > 0) {
    lines.push('', '## ⚠️ Dangerous to Delete', '');
    for (const item of report.byRisk.danger) {
      lines.push(`- \`${item.path}\` - ${item.reason}`);
    }
  }

  return lines.join('\n');
}

/**
 * Format deletion log as Markdown
 *
 * @param entries - Deletion log entries
 * @returns Markdown string
 */
export function formatDeletionLogMarkdown(entries: DeletionLogEntry[]): string {
  const lines: string[] = [
    '# Deletion Log',
    '',
    '| Date | Item | Git SHA | Reason | Restorable |',
    '|------|------|---------|--------|------------|',
  ];

  for (const entry of entries) {
    lines.push(
      `| ${entry.timestamp.toISOString().split('T')[0]} | \`${entry.item.path}\` | ${entry.gitSha.slice(0, 7)} | ${entry.reason} | ${entry.canRestore ? '✅' : '❌'} |`,
    );
  }

  return lines.join('\n');
}
