/**
 * Verification Loop Implementation
 *
 * REQ-VL-001: Multi-Phase Verification
 * REQ-VL-002: Verification Report
 * REQ-VL-003: Continuous Verification
 * REQ-VL-004: Verification Modes (quick/full)
 * REQ-VL-005: Stop Hook監査
 *
 * @packageDocumentation
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { exec } from 'child_process';
import { promisify } from 'util';
import {
  type ContinuousVerificationSuggestion,
  DEFAULT_VERIFICATION_LOOP_CONFIG,
  type DiffPhaseResult,
  type PhaseResult,
  type PhaseStatus,
  type StopHookAuditItem,
  type StopHookAuditReport,
  type TestPhaseResult,
  type VerificationIssue,
  type VerificationLoopConfig,
  type VerificationLoopManager,
  type VerificationMode,
  type VerificationPhase,
  type VerificationReport,
} from './types.js';

const execAsync = promisify(exec);

/**
 * Generate report ID
 */
function generateReportId(): string {
  const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
  return `verify-${timestamp}`;
}

/**
 * Create verification loop manager
 *
 * @param config - Configuration options
 * @returns VerificationLoopManager instance
 */
export function createVerificationLoopManager(
  config: Partial<VerificationLoopConfig> = {}
): VerificationLoopManager {
  const fullConfig: VerificationLoopConfig = {
    ...DEFAULT_VERIFICATION_LOOP_CONFIG,
    ...config,
  };

  /**
   * Run a command and capture result
   */
  async function runCommand(
    command: string,
    phase: VerificationPhase
  ): Promise<PhaseResult> {
    const startTime = Date.now();

    try {
      const { stdout, stderr } = await execAsync(command, {
        cwd: fullConfig.projectRoot,
        timeout: 300000, // 5 minutes
      });

      const duration = Date.now() - startTime;
      const output = stdout + stderr;

      // Parse warnings/errors from output
      const errorCount = (output.match(/error/gi) || []).length;
      const warningCount = (output.match(/warning/gi) || []).length;

      return {
        phase,
        status: 'pass' as PhaseStatus,
        duration,
        errors: errorCount,
        warnings: warningCount,
        details: output.slice(0, 1000),
      };
    } catch (error) {
      const duration = Date.now() - startTime;
      const errorMessage =
        error instanceof Error ? error.message : String(error);

      return {
        phase,
        status: 'fail' as PhaseStatus,
        duration,
        errors: 1,
        details: errorMessage.slice(0, 1000),
      };
    }
  }

  /**
   * Run test phase with coverage
   */
  async function runTestPhase(): Promise<TestPhaseResult> {
    const startTime = Date.now();

    try {
      const { stdout, stderr } = await execAsync(fullConfig.testCommand, {
        cwd: fullConfig.projectRoot,
        timeout: 600000, // 10 minutes
      });

      const duration = Date.now() - startTime;
      const output = stdout + stderr;

      // Parse test results (generic pattern)
      const passedMatch = output.match(/(\d+)\s*(?:passed|passing)/i);
      const totalMatch = output.match(/(\d+)\s*(?:tests?|specs?)/i);
      const coverageMatch = output.match(/(\d+(?:\.\d+)?)\s*%\s*coverage/i);

      const passed = passedMatch ? parseInt(passedMatch[1], 10) : 0;
      const total = totalMatch ? parseInt(totalMatch[1], 10) : passed;
      const coverage = coverageMatch ? parseFloat(coverageMatch[1]) : undefined;

      return {
        phase: 'test',
        status: passed === total ? 'pass' : 'fail',
        duration,
        passed,
        total,
        coverage,
        details: output.slice(0, 1000),
      };
    } catch (error) {
      const duration = Date.now() - startTime;
      return {
        phase: 'test',
        status: 'fail',
        duration,
        passed: 0,
        total: 0,
        details:
          error instanceof Error ? error.message.slice(0, 1000) : 'Unknown error',
      };
    }
  }

  /**
   * Run diff phase
   */
  async function runDiffPhase(): Promise<DiffPhaseResult> {
    const startTime = Date.now();

    try {
      const { stdout } = await execAsync('git diff --stat', {
        cwd: fullConfig.projectRoot,
      });

      const duration = Date.now() - startTime;

      // Parse git diff stat
      const lines = stdout.trim().split('\n');
      const statsLine = lines[lines.length - 1] || '';
      const filesMatch = statsLine.match(/(\d+)\s*files?\s*changed/i);
      const addMatch = statsLine.match(/(\d+)\s*insertions?/i);
      const delMatch = statsLine.match(/(\d+)\s*deletions?/i);

      return {
        phase: 'diff',
        status: 'pass',
        duration,
        filesChanged: filesMatch ? parseInt(filesMatch[1], 10) : 0,
        additions: addMatch ? parseInt(addMatch[1], 10) : 0,
        deletions: delMatch ? parseInt(delMatch[1], 10) : 0,
        details: stdout.slice(0, 1000),
      };
    } catch (error) {
      const duration = Date.now() - startTime;
      return {
        phase: 'diff',
        status: 'pass', // Diff not being available isn't a failure
        duration,
        filesChanged: 0,
        additions: 0,
        deletions: 0,
        details: 'Git diff not available',
      };
    }
  }

  /**
   * Extract issues from phase results
   */
  function extractIssues(phases: PhaseResult[]): VerificationIssue[] {
    const issues: VerificationIssue[] = [];
    let issueId = 1;

    for (const phase of phases) {
      if (phase.status === 'fail') {
        issues.push({
          id: `issue-${issueId++}`,
          phase: phase.phase,
          severity: 'error',
          message: phase.details || `${phase.phase} failed`,
        });
      } else if (phase.warnings && phase.warnings > 0) {
        issues.push({
          id: `issue-${issueId++}`,
          phase: phase.phase,
          severity: 'warning',
          message: `${phase.warnings} warnings in ${phase.phase}`,
        });
      }
    }

    return issues;
  }

  return {
    async runVerification(
      mode: VerificationMode = 'full'
    ): Promise<VerificationReport> {
      const id = generateReportId();
      const startedAt = new Date();
      const phases: PhaseResult[] = [];

      if (mode === 'quick') {
        // Quick mode: type-check, quick test, diff
        phases.push(await runCommand(fullConfig.typeCheckCommand, 'type-check'));
        phases.push(await runTestPhase());
        phases.push(await runDiffPhase());
      } else {
        // Full mode: all phases
        phases.push(await runCommand(fullConfig.buildCommand, 'build'));
        phases.push(await runCommand(fullConfig.typeCheckCommand, 'type-check'));
        phases.push(await runCommand(fullConfig.lintCommand, 'lint'));
        phases.push(await runTestPhase());

        if (fullConfig.securityCommand) {
          phases.push(await runCommand(fullConfig.securityCommand, 'security'));
        }

        phases.push(await runDiffPhase());
      }

      const completedAt = new Date();
      const totalDuration = completedAt.getTime() - startedAt.getTime();
      const issues = extractIssues(phases);
      const hasFailure = phases.some((p) => p.status === 'fail');

      return {
        id,
        mode,
        startedAt,
        completedAt,
        totalDuration,
        phases,
        overall: hasFailure ? 'not-ready' : 'ready',
        issues,
      };
    },

    async runPhase(phase: VerificationPhase): Promise<PhaseResult> {
      switch (phase) {
        case 'build':
          return runCommand(fullConfig.buildCommand, 'build');
        case 'type-check':
          return runCommand(fullConfig.typeCheckCommand, 'type-check');
        case 'lint':
          return runCommand(fullConfig.lintCommand, 'lint');
        case 'test':
          return runTestPhase();
        case 'security':
          if (fullConfig.securityCommand) {
            return runCommand(fullConfig.securityCommand, 'security');
          }
          return {
            phase: 'security',
            status: 'skipped',
            duration: 0,
            details: 'No security command configured',
          };
        case 'diff':
          return runDiffPhase();
        default:
          throw new Error(`Unknown phase: ${phase}`);
      }
    },

    async runStopHookAudit(editedFiles: string[]): Promise<StopHookAuditReport> {
      const timestamp = new Date();
      const items: StopHookAuditItem[] = [];

      const jsPatterns = ['.ts', '.tsx', '.js', '.jsx'];

      for (const file of editedFiles) {
        const ext = path.extname(file);
        if (!jsPatterns.includes(ext)) continue;

        try {
          const content = await fs.readFile(file, 'utf-8');
          const lines = content.split('\n');

          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            const lineNum = i + 1;

            // Check for console.log
            if (/console\.(log|debug|info)\s*\(/.test(line)) {
              items.push({
                type: 'console-log',
                file,
                line: lineNum,
                content: line.trim().slice(0, 100),
              });
            }

            // Check for debugger
            if (/\bdebugger\b/.test(line)) {
              items.push({
                type: 'debugger',
                file,
                line: lineNum,
                content: line.trim().slice(0, 100),
              });
            }

            // Check for TODO/FIXME
            if (/\b(TODO|FIXME)\b/i.test(line)) {
              items.push({
                type: 'todo-fixme',
                file,
                line: lineNum,
                content: line.trim().slice(0, 100),
              });
            }
          }
        } catch {
          // File not accessible, skip
        }
      }

      // Check for uncommitted changes
      try {
        const { stdout } = await execAsync('git status --porcelain', {
          cwd: fullConfig.projectRoot,
        });

        if (stdout.trim()) {
          items.push({
            type: 'uncommitted',
            file: fullConfig.projectRoot,
            content: `${stdout.trim().split('\n').length} uncommitted changes`,
          });
        }
      } catch {
        // Git not available
      }

      return {
        timestamp,
        editedFiles,
        items,
        hasIssues: items.length > 0,
      };
    },

    checkContinuousVerification(
      sessionStartTime: Date,
      changedFileCount: number
    ): ContinuousVerificationSuggestion | null {
      const now = new Date();
      const elapsedMinutes =
        (now.getTime() - sessionStartTime.getTime()) / 1000 / 60;

      // Time-based trigger
      if (elapsedMinutes >= fullConfig.continuousIntervalMinutes) {
        return {
          reason: 'time-based',
          elapsedMinutes: Math.floor(elapsedMinutes),
          recommendation: `${Math.floor(elapsedMinutes)}分経過しました。/verify quickで検証を実行することを推奨します。`,
        };
      }

      // Change-based trigger
      if (changedFileCount >= fullConfig.continuousChangeThreshold) {
        return {
          reason: 'change-based',
          changedFiles: changedFileCount,
          recommendation: `${changedFileCount}ファイルが変更されました。/verify quickで検証を実行することを推奨します。`,
        };
      }

      return null;
    },

    formatReportMarkdown(report: VerificationReport): string {
      const phaseLines = report.phases.map((p) => {
        const status = p.status === 'pass' ? 'PASS' : p.status.toUpperCase();
        let details = '';

        if ('passed' in p && 'total' in p) {
          const testResult = p as TestPhaseResult;
          details = ` (${testResult.passed}/${testResult.total} passed`;
          if (testResult.coverage !== undefined) {
            details += `, ${testResult.coverage.toFixed(1)}% coverage`;
          }
          details += ')';
        } else if ('filesChanged' in p) {
          const diffResult = p as DiffPhaseResult;
          details = ` (${diffResult.filesChanged} files changed)`;
        } else if (p.errors) {
          details = ` (${p.errors} errors)`;
        }

        return `${p.phase.padEnd(12)} [${status}]${details}`;
      });

      const issueLines =
        report.issues.length > 0
          ? report.issues.map((i, idx) => `${idx + 1}. ${i.message}`).join('\n')
          : 'None';

      return `VERIFICATION REPORT
==================

${phaseLines.join('\n')}

Overall:   [${report.overall.toUpperCase()}] for PR

Issues to Fix:
${issueLines}

Duration: ${(report.totalDuration / 1000).toFixed(1)}s`;
    },

    getConfig(): VerificationLoopConfig {
      return fullConfig;
    },
  };
}

/**
 * Format stop hook audit report as markdown
 *
 * @param report - Audit report
 * @returns Markdown string
 */
export function formatStopHookAuditMarkdown(report: StopHookAuditReport): string {
  if (!report.hasIssues) {
    return '✅ Stop Hook監査: 問題なし';
  }

  const groupedItems: Record<string, StopHookAuditItem[]> = {};
  for (const item of report.items) {
    if (!groupedItems[item.type]) {
      groupedItems[item.type] = [];
    }
    groupedItems[item.type].push(item);
  }

  const sections: string[] = [];

  if (groupedItems['console-log']) {
    sections.push(
      `⚠️ console.log残存 (${groupedItems['console-log'].length}件):\n` +
        groupedItems['console-log']
          .map((i) => `  - ${i.file}:${i.line}`)
          .join('\n')
    );
  }

  if (groupedItems['debugger']) {
    sections.push(
      `⚠️ debugger残存 (${groupedItems['debugger'].length}件):\n` +
        groupedItems['debugger']
          .map((i) => `  - ${i.file}:${i.line}`)
          .join('\n')
    );
  }

  if (groupedItems['todo-fixme']) {
    sections.push(
      `📝 TODO/FIXME (${groupedItems['todo-fixme'].length}件):\n` +
        groupedItems['todo-fixme']
          .map((i) => `  - ${i.file}:${i.line}: ${i.content}`)
          .join('\n')
    );
  }

  if (groupedItems['uncommitted']) {
    sections.push(
      `📦 未コミット変更:\n` +
        groupedItems['uncommitted'].map((i) => `  - ${i.content}`).join('\n')
    );
  }

  return `Stop Hook監査レポート\n${'='.repeat(20)}\n\n${sections.join('\n\n')}`;
}
