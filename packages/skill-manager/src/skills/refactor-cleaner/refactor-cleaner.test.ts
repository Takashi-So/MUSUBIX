/**
 * Refactor Cleaner Tests
 *
 * @see REQ-RC-001〜004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createRefactorCleanerManager,
  formatDeadCodeReportMarkdown,
  formatDeletionLogMarkdown,
  type RefactorCleanerConfig,
  type DeadCodeItem,
  type DeadCodeAnalysisReport,
  type DeletionLogEntry,
  type DeadCodeType,
} from '../refactor-cleaner/index.js';

describe('RefactorCleanerManager', () => {
  let manager: ReturnType<typeof createRefactorCleanerManager>;

  beforeEach(() => {
    manager = createRefactorCleanerManager();
  });

  describe('createRefactorCleanerManager', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
      const config = manager.getConfig();
      expect(config.useKnip).toBe(true);
      expect(config.useDepcheck).toBe(true);
    });

    it('should create manager with custom config', () => {
      const customConfig: Partial<RefactorCleanerConfig> = {
        useKnip: false,
        autoDeleteSafe: true,
      };
      const customManager = createRefactorCleanerManager(customConfig);
      const config = customManager.getConfig();
      expect(config.useKnip).toBe(false);
      expect(config.autoDeleteSafe).toBe(true);
    });
  });

  describe('detectDeadCode', () => {
    it('should detect dead code', async () => {
      const items = await manager.detectDeadCode();

      expect(items).toBeInstanceOf(Array);
      // In mock implementation, returns empty array
    });
  });

  describe('classifyRisk', () => {
    it('should classify unused-export as danger', () => {
      const item: DeadCodeItem = {
        id: '1',
        type: 'unused-export',
        path: 'src/api.ts',
        riskLevel: 'danger',
        reason: 'No imports found',
        detectedBy: 'knip',
      };

      const risk = manager.classifyRisk(item);
      expect(risk).toBe('danger');
    });

    it('should classify unused-import as safe', () => {
      const item: DeadCodeItem = {
        id: '2',
        type: 'unused-import',
        path: 'src/index.ts',
        riskLevel: 'safe',
        reason: 'Import not used',
        detectedBy: 'ts-prune',
      };

      const risk = manager.classifyRisk(item);
      expect(risk).toBe('safe');
    });

    it('should classify unused-file as caution', () => {
      const item: DeadCodeItem = {
        id: '3',
        type: 'unused-file',
        path: 'src/old.ts',
        riskLevel: 'caution',
        reason: 'No references',
        detectedBy: 'knip',
      };

      const risk = manager.classifyRisk(item);
      expect(risk).toBe('caution');
    });
  });

  describe('checkReferences', () => {
    it('should check references for item', async () => {
      const item: DeadCodeItem = {
        id: '1',
        type: 'unused-import',
        path: 'src/index.ts',
        riskLevel: 'safe',
        reason: 'Unused',
        detectedBy: 'ts-prune',
      };

      const result = await manager.checkReferences(item);

      expect(result.item).toBe(item);
      expect(result.isSafeToDelete).toBeDefined();
      expect(result.warnings).toBeInstanceOf(Array);
    });

    it('should mark public API as unsafe to delete', async () => {
      const item: DeadCodeItem = {
        id: '2',
        type: 'unused-export',
        path: 'src/api.ts',
        name: 'publicFn',
        riskLevel: 'danger',
        reason: 'Export unused internally',
        detectedBy: 'knip',
      };

      const result = await manager.checkReferences(item);

      expect(result.isPublicApi).toBe(true);
      expect(result.isSafeToDelete).toBe(false);
      expect(result.warnings.length).toBeGreaterThan(0);
    });
  });

  describe('deleteItems', () => {
    it('should delete safe items', async () => {
      const items: DeadCodeItem[] = [
        {
          id: '1',
          type: 'unused-import',
          path: 'src/index.ts',
          riskLevel: 'safe',
          reason: 'Unused',
          detectedBy: 'ts-prune',
        },
      ];

      const result = await manager.deleteItems(items);

      expect(result.success).toBeDefined();
      expect(result.deletedItems).toBeInstanceOf(Array);
      expect(result.skippedItems).toBeInstanceOf(Array);
    });

    it('should skip dangerous items without force', async () => {
      const items: DeadCodeItem[] = [
        {
          id: '1',
          type: 'unused-export',
          path: 'src/api.ts',
          riskLevel: 'danger',
          reason: 'Public API',
          detectedBy: 'knip',
        },
      ];

      const result = await manager.deleteItems(items, false);

      expect(result.skippedItems.length).toBeGreaterThan(0);
    });
  });

  describe('generateReport', () => {
    it('should generate analysis report', () => {
      const items: DeadCodeItem[] = [
        { id: '1', type: 'unused-import', path: 'a.ts', riskLevel: 'safe', reason: 'r', detectedBy: 'knip' },
        { id: '2', type: 'unused-file', path: 'b.ts', riskLevel: 'caution', reason: 'r', detectedBy: 'knip' },
        { id: '3', type: 'unused-export', path: 'c.ts', riskLevel: 'danger', reason: 'r', detectedBy: 'knip' },
      ];

      const report = manager.generateReport(items);

      expect(report.totalItems).toBe(3);
      expect(report.byRisk.safe.length).toBe(1);
      expect(report.byRisk.caution.length).toBe(1);
      expect(report.byRisk.danger.length).toBe(1);
    });
  });

  describe('logDeletion', () => {
    it('should log deletion entry', async () => {
      const entry: DeletionLogEntry = {
        timestamp: new Date(),
        item: {
          id: '1',
          type: 'unused-import',
          path: 'src/old.ts',
          riskLevel: 'safe',
          reason: 'Unused',
          detectedBy: 'knip',
        },
        gitSha: 'abc123',
        deletedBy: 'user',
        reason: 'Cleanup',
        canRestore: true,
      };

      await manager.logDeletion(entry);

      const log = await manager.getDeletionLog();
      expect(log.length).toBeGreaterThan(0);
    });
  });
});

describe('Format functions', () => {
  it('should format dead code report as markdown', () => {
    const byType: Record<DeadCodeType, number> = {
      'unused-import': 1,
      'unused-file': 0,
      'unused-export': 0,
      'unused-dependency': 0,
      'unused-variable': 0,
      'unused-function': 0,
    };

    const report: DeadCodeAnalysisReport = {
      id: 'report-1',
      analyzedAt: new Date(),
      totalItems: 10,
      byRisk: {
        safe: [
          { id: '1', type: 'unused-import', path: 'a.ts', riskLevel: 'safe', reason: 'Unused', detectedBy: 'knip' },
        ],
        caution: [],
        danger: [],
      },
      byType,
      estimatedSavings: { files: 0, lines: 100, dependencies: 0 },
    };

    const markdown = formatDeadCodeReportMarkdown(report);
    expect(markdown).toContain('# Dead Code Analysis Report');
    expect(markdown).toContain('Safe');
    expect(markdown).toContain('a.ts');
  });

  it('should format deletion log as markdown', () => {
    const entries: DeletionLogEntry[] = [
      {
        timestamp: new Date(),
        item: {
          id: '1',
          type: 'unused-file',
          path: 'old.ts',
          riskLevel: 'safe',
          reason: 'Deprecated',
          detectedBy: 'knip',
        },
        gitSha: 'abc1234567890',
        deletedBy: 'bot',
        reason: 'Cleanup sprint',
        canRestore: true,
      },
    ];

    const markdown = formatDeletionLogMarkdown(entries);
    expect(markdown).toContain('# Deletion Log');
    expect(markdown).toContain('old.ts');
    expect(markdown).toContain('abc1234');
  });
});
