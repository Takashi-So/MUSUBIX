/**
 * @fileoverview Refactor Cleaner Bridge Implementation for Agent Skills Integration
 * @traceability REQ-RC-001, REQ-RC-002, REQ-RC-003, REQ-RC-004
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { spawn } from 'child_process';
import type {
  RefactorCleanerBridge,
  RefactorCleanerBridgeConfig,
  DeadCodeItem,
  DeadCodeAnalysisResult,
  SafetyCheckResult,
  BatchSafetyCheckResult,
  DeletionAction,
  DeletionLogEntry,
  DeadCodeReport,
  ReportFormat,
  RiskLevel,
} from './refactor-cleaner-types.js';
import {
  DEFAULT_REFACTOR_CLEANER_CONFIG,
} from './refactor-cleaner-types.js';

/**
 * Create a Refactor Cleaner Bridge for Agent Skills integration
 * @param config Bridge configuration
 * @returns RefactorCleanerBridge instance
 */
export function createRefactorCleanerBridge(
  config: Partial<RefactorCleanerBridgeConfig> = {}
): RefactorCleanerBridge {
  let currentConfig: RefactorCleanerBridgeConfig = {
    ...DEFAULT_REFACTOR_CLEANER_CONFIG,
    ...config,
  };

  return {
    async analyze(rootPath: string, options = {}): Promise<DeadCodeAnalysisResult> {
      const tools = options.tools || ['knip'];
      const items: DeadCodeItem[] = [];

      for (const tool of tools) {
        try {
          const toolItems = await runDeadCodeTool(tool, rootPath, currentConfig);
          items.push(...toolItems);
        } catch (error) {
          // Tool not available, skip
          console.warn(`Tool ${tool} not available: ${error}`);
        }
      }

      // Deduplicate items by path + name
      const uniqueItems = deduplicateItems(items);

      // Classify risk levels
      const classifiedItems = uniqueItems.map(item => ({
        ...item,
        riskLevel: initialRiskClassification(item, currentConfig),
      }));

      const summary = {
        safe: classifiedItems.filter(i => i.riskLevel === 'safe').length,
        caution: classifiedItems.filter(i => i.riskLevel === 'caution').length,
        danger: classifiedItems.filter(i => i.riskLevel === 'danger').length,
        total: classifiedItems.length,
        estimatedTotalSize: classifiedItems.reduce((sum, i) => sum + (i.estimatedSize || 0), 0),
      };

      return {
        analyzedAt: new Date().toISOString(),
        analyzedPaths: [rootPath],
        items: classifiedItems,
        summary,
      };
    },

    async checkSafety(items: DeadCodeItem[], rootPath: string): Promise<BatchSafetyCheckResult> {
      const safeItems: DeadCodeItem[] = [];
      const cautionItems: Array<{ item: DeadCodeItem; reasons: string[] }> = [];
      const dangerItems: Array<{ item: DeadCodeItem; reasons: string[] }> = [];

      for (const item of items) {
        const check = await performSafetyCheck(item, rootPath);

        if (check.isSafe) {
          safeItems.push(item);
        } else if (check.blockingReasons.some(r => r.includes('public') || r.includes('entry'))) {
          dangerItems.push({ item, reasons: check.blockingReasons });
        } else {
          cautionItems.push({ item, reasons: check.blockingReasons });
        }
      }

      return { safeItems, cautionItems, dangerItems };
    },

    async deleteItems(
      items: DeadCodeItem[],
      rootPath: string,
      options = {}
    ): Promise<DeletionLogEntry> {
      const { dryRun = false } = options;
      const actions: DeletionAction[] = [];
      const deletedItems: DeadCodeItem[] = [];

      // Get current git SHA
      let gitSha = 'unknown';
      try {
        gitSha = await runCommand('git', ['rev-parse', 'HEAD'], rootPath);
        gitSha = gitSha.trim();
      } catch {
        // Not a git repo
      }

      for (const item of items) {
        if (dryRun) {
          actions.push({
            type: item.type === 'unused-file' ? 'delete-file' : 'remove-export',
            path: item.path,
            name: item.name,
            gitSha,
          });
          deletedItems.push(item);
          continue;
        }

        try {
          if (item.type === 'unused-file') {
            await fs.unlink(path.join(rootPath, item.path));
            actions.push({
              type: 'delete-file',
              path: item.path,
              gitSha,
            });
          } else if (item.type === 'unused-dependency') {
            // Would need package manager integration
            actions.push({
              type: 'remove-dependency',
              path: 'package.json',
              name: item.name,
              gitSha,
            });
          }
          // Other types would need AST manipulation
          deletedItems.push(item);
        } catch (error) {
          console.error(`Failed to delete ${item.path}: ${error}`);
        }
      }

      const entry: DeletionLogEntry = {
        id: `DEL-${Date.now()}`,
        deletedAt: new Date().toISOString(),
        items: deletedItems,
        actions,
        summary: {
          filesDeleted: actions.filter(a => a.type === 'delete-file').length,
          exportsRemoved: actions.filter(a => a.type === 'remove-export').length,
          dependenciesRemoved: actions.filter(a => a.type === 'remove-dependency').length,
          estimatedReduction: deletedItems.reduce((sum, i) => sum + (i.estimatedSize || 0), 0),
        },
        restoration: {
          gitSha,
          command: `git checkout ${gitSha} -- ${deletedItems.map(i => i.path).join(' ')}`,
        },
      };

      return entry;
    },

    generateReport(result: DeadCodeAnalysisResult, format: ReportFormat = 'markdown'): DeadCodeReport {
      let content: string;

      switch (format) {
        case 'json':
          content = JSON.stringify(result, null, 2);
          break;
        case 'text':
          content = formatAsText(result);
          break;
        case 'markdown':
        default:
          content = formatAsMarkdown(result);
          break;
      }

      return {
        format,
        content,
        generatedAt: new Date().toISOString(),
      };
    },

    async appendDeletionLog(entry: DeletionLogEntry): Promise<void> {
      const logPath = currentConfig.deletionLogPath;
      
      let existingContent = '';
      try {
        existingContent = await fs.readFile(logPath, 'utf-8');
      } catch {
        existingContent = '# Deletion Log\n\n';
      }

      const newEntry = formatDeletionLogEntry(entry);
      const updatedContent = existingContent + '\n' + newEntry;

      await fs.mkdir(path.dirname(logPath), { recursive: true });
      await fs.writeFile(logPath, updatedContent, 'utf-8');
    },

    getConfig(): RefactorCleanerBridgeConfig {
      return { ...currentConfig };
    },

    updateConfig(config: Partial<RefactorCleanerBridgeConfig>): void {
      currentConfig = { ...currentConfig, ...config };
    },

    classifyRisk(_item: DeadCodeItem, safetyCheck: SafetyCheckResult): RiskLevel {
      if (!safetyCheck.isSafe) {
        // Check for danger indicators
        const hasDangerIndicators = safetyCheck.blockingReasons.some(r =>
          r.includes('public') ||
          r.includes('API') ||
          r.includes('entry') ||
          r.includes('export')
        );

        if (hasDangerIndicators) {
          return 'danger';
        }

        // Check for caution indicators
        const hasCautionIndicators =
          safetyCheck.dynamicImportRefs.length > 0 ||
          safetyCheck.testRefs.length > 0;

        if (hasCautionIndicators) {
          return 'caution';
        }

        return 'caution';
      }

      return 'safe';
    },
  };
}

// ============================================================================
// Helper Functions
// ============================================================================

async function runDeadCodeTool(
  tool: 'knip' | 'depcheck' | 'ts-prune',
  rootPath: string,
  config: RefactorCleanerBridgeConfig
): Promise<DeadCodeItem[]> {
  const items: DeadCodeItem[] = [];

  switch (tool) {
    case 'knip': {
      try {
        const output = await runCommand('npx', ['knip', '--reporter', 'json'], rootPath);
        const result = JSON.parse(output);

        // Parse knip JSON output
        if (result.files) {
          for (const file of result.files) {
            items.push({
              id: `knip-file-${file}`,
              type: 'unused-file',
              path: file,
              name: path.basename(file),
              riskLevel: 'safe',
              reason: 'Unused file detected by knip',
              detectedBy: 'knip',
            });
          }
        }

        if (result.exports) {
          for (const [file, exports] of Object.entries(result.exports as Record<string, string[]>)) {
            for (const exp of exports) {
              items.push({
                id: `knip-export-${file}-${exp}`,
                type: 'unused-export',
                path: file,
                name: exp,
                riskLevel: 'caution',
                reason: 'Unused export detected by knip',
                detectedBy: 'knip',
              });
            }
          }
        }

        if (result.dependencies) {
          for (const dep of result.dependencies) {
            items.push({
              id: `knip-dep-${dep}`,
              type: 'unused-dependency',
              path: 'package.json',
              name: dep,
              riskLevel: 'caution',
              reason: 'Unused dependency detected by knip',
              detectedBy: 'knip',
            });
          }
        }
      } catch {
        // knip not available or failed
      }
      break;
    }

    case 'depcheck': {
      try {
        const output = await runCommand('npx', ['depcheck', '--json'], rootPath);
        const result = JSON.parse(output);

        if (result.dependencies) {
          for (const dep of result.dependencies) {
            items.push({
              id: `depcheck-dep-${dep}`,
              type: 'unused-dependency',
              path: 'package.json',
              name: dep,
              riskLevel: 'caution',
              reason: 'Unused dependency detected by depcheck',
              detectedBy: 'depcheck',
            });
          }
        }

        if (result.devDependencies) {
          for (const dep of result.devDependencies) {
            items.push({
              id: `depcheck-devdep-${dep}`,
              type: 'unused-dependency',
              path: 'package.json',
              name: dep,
              riskLevel: 'safe',
              reason: 'Unused devDependency detected by depcheck',
              detectedBy: 'depcheck',
            });
          }
        }
      } catch {
        // depcheck not available or failed
      }
      break;
    }

    case 'ts-prune': {
      try {
        const output = await runCommand('npx', ['ts-prune'], rootPath);
        const lines = output.split('\n').filter(l => l.trim());

        for (const line of lines) {
          // ts-prune output format: "path/to/file.ts:42 - exportName"
          const match = line.match(/^(.+):(\d+)\s+-\s+(.+)$/);
          if (match) {
            const [, filePath, lineNum, exportName] = match;
            items.push({
              id: `ts-prune-${filePath}-${exportName}`,
              type: 'unused-export',
              path: filePath,
              name: exportName.trim(),
              line: parseInt(lineNum, 10),
              riskLevel: 'caution',
              reason: 'Unused export detected by ts-prune',
              detectedBy: 'ts-prune',
            });
          }
        }
      } catch {
        // ts-prune not available or failed
      }
      break;
    }
  }

  // Filter out ignored patterns
  return items.filter(item => !isIgnored(item.path, config.ignorePatterns));
}

function runCommand(cmd: string, args: string[], cwd: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const proc = spawn(cmd, args, { cwd, shell: true });
    let stdout = '';
    let stderr = '';

    proc.stdout.on('data', (data) => {
      stdout += data.toString();
    });

    proc.stderr.on('data', (data) => {
      stderr += data.toString();
    });

    proc.on('close', (code) => {
      if (code === 0 || stdout) {
        resolve(stdout);
      } else {
        reject(new Error(stderr || `Command failed with code ${code}`));
      }
    });

    proc.on('error', (err) => {
      reject(err);
    });
  });
}

function isIgnored(filePath: string, patterns: string[]): boolean {
  for (const pattern of patterns) {
    // Simple glob matching
    const regex = new RegExp(
      pattern
        .replace(/\*\*/g, '.*')
        .replace(/\*/g, '[^/]*')
        .replace(/\./g, '\\.')
    );
    if (regex.test(filePath)) {
      return true;
    }
  }
  return false;
}

function deduplicateItems(items: DeadCodeItem[]): DeadCodeItem[] {
  const seen = new Set<string>();
  return items.filter(item => {
    const key = `${item.type}:${item.path}:${item.name}`;
    if (seen.has(key)) {
      return false;
    }
    seen.add(key);
    return true;
  });
}

function initialRiskClassification(
  item: DeadCodeItem,
  _config: RefactorCleanerBridgeConfig
): RiskLevel {
  // Entry points are always danger
  if (item.path.includes('/bin/') || item.path.includes('/cli/')) {
    return 'danger';
  }

  // Index files are danger
  if (item.name === 'index' || item.path.endsWith('/index.ts') || item.path.endsWith('/index.js')) {
    return 'danger';
  }

  // Type definitions are caution
  if (item.path.endsWith('.d.ts')) {
    return 'caution';
  }

  // Unused files with no references are safe
  if (item.type === 'unused-file') {
    return 'safe';
  }

  // Unused devDependencies are safe
  if (item.type === 'unused-dependency' && item.reason.includes('devDependency')) {
    return 'safe';
  }

  return 'caution';
}

async function performSafetyCheck(
  item: DeadCodeItem,
  rootPath: string
): Promise<SafetyCheckResult> {
  const result: SafetyCheckResult = {
    item,
    isSafe: true,
    blockingReasons: [],
    dynamicImportRefs: [],
    testRefs: [],
    docRefs: [],
    configRefs: [],
  };

  const itemName = item.name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

  try {
    // Check dynamic imports
    const dynamicCheck = await runCommand(
      'grep',
      ['-rn', `import.*${itemName}`, '--include=*.ts', '--include=*.js'],
      rootPath
    ).catch(() => '');

    if (dynamicCheck.includes('import(') || dynamicCheck.includes('require(')) {
      result.dynamicImportRefs.push(dynamicCheck.trim());
      result.isSafe = false;
      result.blockingReasons.push('Found in dynamic import');
    }

    // Check test files
    const testCheck = await runCommand(
      'grep',
      ['-rn', itemName, '--include=*.test.ts', '--include=*.spec.ts'],
      rootPath
    ).catch(() => '');

    if (testCheck.trim()) {
      result.testRefs.push(testCheck.trim());
      result.isSafe = false;
      result.blockingReasons.push('Referenced in test files');
    }

    // Check documentation
    const docCheck = await runCommand(
      'grep',
      ['-rn', itemName, '--include=*.md'],
      rootPath
    ).catch(() => '');

    if (docCheck.trim()) {
      result.docRefs.push(docCheck.trim());
      result.blockingReasons.push('Referenced in documentation');
    }

    // Check config files
    const configCheck = await runCommand(
      'grep',
      ['-rn', itemName, '--include=*.config.*', '--include=*.json'],
      rootPath
    ).catch(() => '');

    if (configCheck.trim()) {
      result.configRefs.push(configCheck.trim());
      result.isSafe = false;
      result.blockingReasons.push('Referenced in config files');
    }
  } catch {
    // grep not available or failed
  }

  return result;
}

function formatAsMarkdown(result: DeadCodeAnalysisResult): string {
  const lines: string[] = [];

  lines.push('# Dead Code Analysis Report');
  lines.push('');
  lines.push(`**Generated**: ${result.analyzedAt}`);
  lines.push(`**Analyzed paths**: ${result.analyzedPaths.join(', ')}`);
  lines.push('');
  lines.push('## Summary');
  lines.push('');
  lines.push('| Category | Count | Estimated Size |');
  lines.push('|----------|-------|----------------|');
  lines.push(`| 🟢 SAFE | ${result.summary.safe} | - |`);
  lines.push(`| 🟡 CAUTION | ${result.summary.caution} | - |`);
  lines.push(`| 🔴 DANGER | ${result.summary.danger} | - |`);
  lines.push(`| **Total** | ${result.summary.total} | ~${formatBytes(result.summary.estimatedTotalSize)} |`);
  lines.push('');

  // Group by risk level
  const safeItems = result.items.filter(i => i.riskLevel === 'safe');
  const cautionItems = result.items.filter(i => i.riskLevel === 'caution');
  const dangerItems = result.items.filter(i => i.riskLevel === 'danger');

  if (safeItems.length > 0) {
    lines.push('## 🟢 SAFE (Auto-deletable)');
    lines.push('');
    for (const item of safeItems) {
      lines.push(`- \`${item.path}\`${item.name !== path.basename(item.path) ? ` - ${item.name}` : ''}`);
      lines.push(`  - ${item.reason}`);
    }
    lines.push('');
  }

  if (cautionItems.length > 0) {
    lines.push('## 🟡 CAUTION (Review Required)');
    lines.push('');
    for (const item of cautionItems) {
      lines.push(`- \`${item.path}\`${item.name !== path.basename(item.path) ? ` - ${item.name}` : ''}`);
      lines.push(`  - ${item.reason}`);
    }
    lines.push('');
  }

  if (dangerItems.length > 0) {
    lines.push('## 🔴 DANGER (Manual Review Only)');
    lines.push('');
    for (const item of dangerItems) {
      lines.push(`- \`${item.path}\`${item.name !== path.basename(item.path) ? ` - ${item.name}` : ''}`);
      lines.push(`  - ${item.reason}`);
    }
    lines.push('');
  }

  return lines.join('\n');
}

function formatAsText(result: DeadCodeAnalysisResult): string {
  const lines: string[] = [];

  lines.push('Dead Code Analysis Report');
  lines.push('=========================');
  lines.push(`Generated: ${result.analyzedAt}`);
  lines.push('');
  lines.push('Summary:');
  lines.push(`  SAFE:    ${result.summary.safe}`);
  lines.push(`  CAUTION: ${result.summary.caution}`);
  lines.push(`  DANGER:  ${result.summary.danger}`);
  lines.push(`  Total:   ${result.summary.total}`);
  lines.push('');

  for (const item of result.items) {
    const icon = item.riskLevel === 'safe' ? '✓' : item.riskLevel === 'caution' ? '!' : '✗';
    lines.push(`[${icon}] ${item.path} - ${item.name}`);
  }

  return lines.join('\n');
}

function formatDeletionLogEntry(entry: DeletionLogEntry): string {
  const lines: string[] = [];

  lines.push(`## [${entry.deletedAt.split('T')[0]}] Cleanup Session`);
  lines.push('');
  lines.push('### Summary');
  lines.push(`- **Files deleted**: ${entry.summary.filesDeleted}`);
  lines.push(`- **Exports removed**: ${entry.summary.exportsRemoved}`);
  lines.push(`- **Dependencies removed**: ${entry.summary.dependenciesRemoved}`);
  lines.push(`- **Estimated reduction**: ~${formatBytes(entry.summary.estimatedReduction)}`);
  lines.push('');
  lines.push('### Deleted Items');
  lines.push('');

  if (entry.items.filter(i => i.type === 'unused-file').length > 0) {
    lines.push('#### Files');
    lines.push('');
    lines.push('| File | Reason | Git SHA |');
    lines.push('|------|--------|---------|');
    for (const item of entry.items.filter(i => i.type === 'unused-file')) {
      lines.push(`| \`${item.path}\` | ${item.reason} | ${entry.restoration.gitSha.substring(0, 7)} |`);
    }
    lines.push('');
  }

  lines.push('### Restoration');
  lines.push('');
  lines.push('```bash');
  lines.push(entry.restoration.command);
  lines.push('```');
  lines.push('');

  return lines.join('\n');
}

function formatBytes(bytes: number): string {
  if (bytes === 0) return '0 B';
  const k = 1024;
  const sizes = ['B', 'KB', 'MB', 'GB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  return `${parseFloat((bytes / Math.pow(k, i)).toFixed(1))} ${sizes[i]}`;
}

/**
 * Parse knip output from text format (fallback)
 */
export function parseKnipTextOutput(output: string): DeadCodeItem[] {
  const items: DeadCodeItem[] = [];
  const lines = output.split('\n');

  for (const line of lines) {
    // Parse various knip output formats
    if (line.includes('Unused files')) {
      // Section header
      continue;
    }

    if (line.trim().startsWith('-') || line.trim().startsWith('•')) {
      const filePath = line.replace(/^[-•\s]+/, '').trim();
      if (filePath && !filePath.includes(':')) {
        items.push({
          id: `knip-file-${filePath}`,
          type: 'unused-file',
          path: filePath,
          name: path.basename(filePath),
          riskLevel: 'safe',
          reason: 'Unused file detected by knip',
          detectedBy: 'knip',
        });
      }
    }
  }

  return items;
}
