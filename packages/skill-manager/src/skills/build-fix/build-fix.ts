/**
 * Build Fix Implementation
 *
 * REQ-BF-001: Build Error Analysis
 * REQ-BF-002: Iterative Fix Strategy
 * REQ-BF-003: Fix Report
 *
 * @packageDocumentation
 */

import { exec } from 'child_process';
import { promisify } from 'util';
import {
  type BuildError,
  type BuildErrorCategory,
  type BuildErrorPriority,
  type BuildFixConfig,
  type BuildFixManager,
  type BuildOutput,
  type FixAttempt,
  type FixReport,
  type FixStrategy,
  DEFAULT_BUILD_FIX_CONFIG,
} from './types.js';

const execAsync = promisify(exec);

/**
 * Generate error ID
 */
function generateErrorId(category: BuildErrorCategory, index: number): string {
  return `${category}-${(index + 1).toString().padStart(3, '0')}`;
}

/**
 * Generate report ID
 */
function generateReportId(): string {
  const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
  return `fix-report-${timestamp}`;
}

/**
 * Determine error category from message
 */
function categorizeError(message: string, code?: string): BuildErrorCategory {
  // TypeScript errors
  if (code?.startsWith('TS') || /TS\d{4,5}/.test(message)) {
    if (/cannot find|not found|does not exist/i.test(message)) {
      return 'import-error';
    }
    return 'type-error';
  }

  // Syntax errors
  if (/syntax|unexpected|unterminated/i.test(message)) {
    return 'syntax-error';
  }

  // Import/module errors
  if (/module|import|require|cannot find module/i.test(message)) {
    return 'import-error';
  }

  // ESLint errors
  if (/eslint|@typescript-eslint/i.test(message)) {
    return 'lint-error';
  }

  // Config errors
  if (/config|tsconfig|webpack|vite/i.test(message)) {
    return 'config-error';
  }

  // Dependency errors
  if (/peer dep|version|incompatible/i.test(message)) {
    return 'dependency-error';
  }

  return 'unknown';
}

/**
 * Determine error priority
 */
function determineErrorPriority(
  category: BuildErrorCategory
): BuildErrorPriority {
  switch (category) {
    case 'type-error':
    case 'import-error':
    case 'syntax-error':
      return 'high';
    case 'lint-error':
    case 'config-error':
      return 'medium';
    case 'dependency-error':
    case 'unknown':
      return 'low';
  }
}

/**
 * Create build fix manager
 *
 * @param config - Configuration options
 * @returns BuildFixManager instance
 */
export function createBuildFixManager(
  config: Partial<BuildFixConfig> = {}
): BuildFixManager {
  const fullConfig: BuildFixConfig = {
    ...DEFAULT_BUILD_FIX_CONFIG,
    ...config,
  };

  const fixedFiles = new Set<string>();

  return {
    analyzeErrors(output: string): BuildError[] {
      const errors: BuildError[] = [];
      const lines = output.split('\n');

      // TypeScript error pattern: file(line,col): error TSxxxx: message
      const tsErrorRegex =
        /^(.+?)\((\d+),(\d+)\):\s*error\s+(TS\d+):\s*(.+)$/;

      // Generic error pattern: file:line:col: error message
      const genericErrorRegex = /^(.+?):(\d+):(\d+):\s*(?:error|Error):\s*(.+)$/;

      // Simple error pattern: error: message or Error: message
      const simpleErrorRegex = /^(?:error|Error):\s*(.+)$/;

      for (const line of lines) {
        let match: RegExpMatchArray | null;

        if ((match = line.match(tsErrorRegex))) {
          const [, file, lineNum, col, code, message] = match;
          const category = categorizeError(message, code);
          errors.push({
            id: generateErrorId(category, errors.length),
            category,
            priority: determineErrorPriority(category),
            code,
            message,
            file,
            line: parseInt(lineNum, 10),
            column: parseInt(col, 10),
          });
        } else if ((match = line.match(genericErrorRegex))) {
          const [, file, lineNum, col, message] = match;
          const category = categorizeError(message);
          errors.push({
            id: generateErrorId(category, errors.length),
            category,
            priority: determineErrorPriority(category),
            message,
            file,
            line: parseInt(lineNum, 10),
            column: parseInt(col, 10),
          });
        } else if ((match = line.match(simpleErrorRegex))) {
          const [, message] = match;
          const category = categorizeError(message);
          errors.push({
            id: generateErrorId(category, errors.length),
            category,
            priority: determineErrorPriority(category),
            message,
          });
        }
      }

      return errors;
    },

    async runBuild(): Promise<BuildOutput> {
      const startTime = Date.now();

      try {
        const { stdout, stderr } = await execAsync(fullConfig.buildCommand, {
          cwd: fullConfig.projectRoot,
          timeout: 300000, // 5 minutes
        });

        const output = stdout + stderr;
        const errors = this.analyzeErrors(output);

        return {
          success: errors.length === 0,
          stdout,
          stderr,
          errors,
          duration: Date.now() - startTime,
        };
      } catch (error) {
        const duration = Date.now() - startTime;
        const errorObj = error as Error & { stdout?: string; stderr?: string };
        const output =
          error instanceof Error
            ? (errorObj.stdout || '') +
              (errorObj.stderr || '') +
              error.message
            : String(error);
        const errors = this.analyzeErrors(output);

        return {
          success: false,
          stdout: '',
          stderr: output,
          errors: errors.length > 0 ? errors : [{
            id: 'unknown-001',
            category: 'unknown',
            priority: 'high',
            message: output.slice(0, 500),
          }],
          duration,
        };
      }
    },

    generateFixStrategy(error: BuildError): FixStrategy {
      const steps: string[] = [];
      let estimatedImpact: 'high' | 'medium' | 'low' = 'low';
      let requiresUserApproval = false;

      switch (error.category) {
        case 'type-error':
          steps.push(`ファイル ${error.file || 'unknown'} を開く`);
          steps.push(`行 ${error.line || 'unknown'} を確認`);
          steps.push('型定義を確認または追加');
          steps.push('型アサーションまたは型ガードを検討');
          estimatedImpact = 'high';
          break;

        case 'import-error':
          steps.push('インポートパスを確認');
          steps.push('モジュールが存在するか確認');
          steps.push('必要に応じて npm install を実行');
          steps.push('tsconfig.json の paths を確認');
          estimatedImpact = 'high';
          break;

        case 'syntax-error':
          steps.push(`ファイル ${error.file || 'unknown'} を開く`);
          steps.push(`行 ${error.line || 'unknown'} の構文を確認`);
          steps.push('括弧、セミコロン、クォートの対応を確認');
          estimatedImpact = 'high';
          break;

        case 'lint-error':
          steps.push('ESLint ルールを確認');
          steps.push('npm run lint:fix を試行');
          steps.push('必要に応じて eslint-disable コメントを追加');
          estimatedImpact = 'medium';
          break;

        case 'config-error':
          steps.push('設定ファイルの構文を確認');
          steps.push('必要なフィールドが存在するか確認');
          steps.push('公式ドキュメントと比較');
          estimatedImpact = 'medium';
          requiresUserApproval = true;
          break;

        case 'dependency-error':
          steps.push('package.json を確認');
          steps.push('npm ls でバージョン競合を確認');
          steps.push('node_modules を削除して再インストール');
          estimatedImpact = 'low';
          requiresUserApproval = true;
          break;

        default:
          steps.push('エラーメッセージを詳細に確認');
          steps.push('関連するファイルを調査');
          requiresUserApproval = true;
      }

      return {
        errorId: error.id,
        steps,
        estimatedImpact,
        requiresUserApproval,
      };
    },

    async applyFix(strategy: FixStrategy): Promise<boolean> {
      // This is a stub - actual implementation would modify files
      // For safety, this should require explicit approval in production
      console.log(`Applying fix strategy for error ${strategy.errorId}`);
      console.log(`Steps: ${strategy.steps.join(' → ')}`);
      return false; // Return false to indicate manual intervention needed
    },

    async runIterativeFix(): Promise<FixReport> {
      const id = generateReportId();
      const startedAt = new Date();
      const attempts: FixAttempt[] = [];
      let iteration = 0;
      let errorsFixed = 0;

      // Initial build
      let buildOutput = await this.runBuild();
      let previousErrorCount = buildOutput.errors.length;

      while (
        !buildOutput.success &&
        iteration < fullConfig.maxIterations &&
        buildOutput.errors.length > 0
      ) {
        iteration++;

        // Get most impactful error
        const [mostImpactful] = this.getMostImpactfulErrors(
          buildOutput.errors,
          1
        );
        if (!mostImpactful) break;

        const strategy = this.generateFixStrategy(mostImpactful);

        // Skip if requires approval and auto-fix is disabled
        if (strategy.requiresUserApproval && !fullConfig.autoFix) {
          break;
        }

        const fixSuccess = await this.applyFix(strategy);

        // Track modified files
        if (mostImpactful.file) {
          fixedFiles.add(mostImpactful.file);
        }

        // Re-run build
        buildOutput = await this.runBuild();
        const newErrorsIntroduced = Math.max(
          0,
          buildOutput.errors.length - (previousErrorCount - 1)
        );

        attempts.push({
          iteration,
          error: mostImpactful,
          fix: strategy.steps.join(' → '),
          success: fixSuccess && buildOutput.errors.length < previousErrorCount,
          newErrorsIntroduced,
          timestamp: new Date(),
        });

        if (buildOutput.errors.length < previousErrorCount) {
          errorsFixed++;
        }

        previousErrorCount = buildOutput.errors.length;
      }

      const warnings: string[] = [];
      if (iteration >= fullConfig.maxIterations) {
        warnings.push(`最大反復回数 (${fullConfig.maxIterations}) に達しました`);
      }
      if (buildOutput.errors.length > 0) {
        warnings.push(`${buildOutput.errors.length}個のエラーが残存しています`);
      }

      return {
        id,
        startedAt,
        completedAt: new Date(),
        totalIterations: iteration,
        errorsFixed,
        errorsRemaining: buildOutput.errors.length,
        filesModified: Array.from(fixedFiles),
        warnings,
        attempts,
      };
    },

    getMostImpactfulErrors(errors: BuildError[], limit: number = 5): BuildError[] {
      const priorityOrder: Record<BuildErrorPriority, number> = {
        high: 0,
        medium: 1,
        low: 2,
      };

      return [...errors]
        .sort((a, b) => priorityOrder[a.priority] - priorityOrder[b.priority])
        .slice(0, limit);
    },

    getConfig(): BuildFixConfig {
      return fullConfig;
    },
  };
}

/**
 * Format fix report as markdown
 *
 * @param report - Fix report
 * @returns Markdown string
 */
export function formatFixReportMarkdown(report: FixReport): string {
  const duration =
    (report.completedAt.getTime() - report.startedAt.getTime()) / 1000;

  const filesSection =
    report.filesModified.length > 0
      ? report.filesModified.map((f) => `  - ${f}`).join('\n')
      : '  (なし)';

  const warningsSection =
    report.warnings.length > 0
      ? report.warnings.map((w) => `  ⚠️ ${w}`).join('\n')
      : '  (なし)';

  return `Build Fix Report
================

修正したエラー数: ${report.errorsFixed}
残存エラー数: ${report.errorsRemaining}
反復回数: ${report.totalIterations}
所要時間: ${duration.toFixed(1)}s

変更したファイル:
${filesSection}

警告:
${warningsSection}`;
}

/**
 * Format build errors as markdown
 *
 * @param errors - Array of build errors
 * @returns Markdown string
 */
export function formatBuildErrorsMarkdown(errors: BuildError[]): string {
  if (errors.length === 0) {
    return '✅ ビルドエラーなし';
  }

  const grouped: Record<BuildErrorCategory, BuildError[]> = {
    'type-error': [],
    'import-error': [],
    'syntax-error': [],
    'lint-error': [],
    'config-error': [],
    'dependency-error': [],
    'unknown': [],
  };

  for (const error of errors) {
    grouped[error.category].push(error);
  }

  const sections: string[] = [];

  const categoryLabels: Record<BuildErrorCategory, string> = {
    'type-error': 'Type Errors',
    'import-error': 'Import Errors',
    'syntax-error': 'Syntax Errors',
    'lint-error': 'Lint Errors',
    'config-error': 'Config Errors',
    'dependency-error': 'Dependency Errors',
    'unknown': 'Other Errors',
  };

  for (const [category, categoryErrors] of Object.entries(grouped)) {
    if (categoryErrors.length === 0) continue;

    const label = categoryLabels[category as BuildErrorCategory];
    const errorList = categoryErrors
      .map((e) => {
        const location = e.file ? `${e.file}:${e.line || '?'}` : '(unknown)';
        return `  - [${e.priority.toUpperCase()}] ${location}: ${e.message}`;
      })
      .join('\n');

    sections.push(`### ${label} (${categoryErrors.length})\n${errorList}`);
  }

  return `Build Errors (${errors.length} total)\n${'='.repeat(30)}\n\n${sections.join('\n\n')}`;
}
