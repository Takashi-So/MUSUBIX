/**
 * @fileoverview E2E Runner Bridge Implementation for Agent Skills Integration
 * @traceability REQ-E2E-001, REQ-E2E-002, REQ-E2E-003
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { spawn } from 'child_process';
import type {
  E2ERunnerBridge,
  E2ERunnerBridgeConfig,
  UserFlow,
  FlowStep,
  GeneratedTestFile,
  TestGenerationResult,
  TestExecutionOptions,
  TestExecutionResult,
  TestSuiteResult,
  TestResult,
  E2EReport,
  E2EReportFormat,
} from './e2e-runner-types.js';
import {
  DEFAULT_E2E_RUNNER_CONFIG,
} from './e2e-runner-types.js';

/**
 * Create an E2E Runner Bridge for Agent Skills integration
 * @param config Bridge configuration
 * @returns E2ERunnerBridge instance
 */
export function createE2ERunnerBridge(
  config: Partial<E2ERunnerBridgeConfig> = {}
): E2ERunnerBridge {
  let currentConfig: E2ERunnerBridgeConfig = {
    ...DEFAULT_E2E_RUNNER_CONFIG,
    ...config,
  };

  return {
    generateTest(flow: UserFlow): TestGenerationResult {
      const files: GeneratedTestFile[] = [];

      // Generate test file
      const testContent = generateTestFile(flow, currentConfig);
      files.push({
        path: `${toKebabCase(flow.name)}.spec.ts`,
        content: testContent,
        flowName: flow.name,
      });

      // Generate fixture if needed
      if (flow.setup || flow.teardown) {
        const fixtureContent = generateFixtureFile(flow);
        files.push({
          path: `fixtures/${toKebabCase(flow.name)}.json`,
          content: fixtureContent,
          flowName: flow.name,
        });
      }

      return {
        files,
        generatedAt: new Date().toISOString(),
        flowsProcessed: 1,
      };
    },

    generateTests(flows: UserFlow[]): TestGenerationResult {
      const allFiles: GeneratedTestFile[] = [];

      for (const flow of flows) {
        const result = this.generateTest(flow);
        allFiles.push(...result.files);
      }

      return {
        files: allFiles,
        generatedAt: new Date().toISOString(),
        flowsProcessed: flows.length,
      };
    },

    async runTests(options: TestExecutionOptions = {}): Promise<TestExecutionResult> {
      const args = buildPlaywrightArgs(options, currentConfig);
      const startTime = Date.now();

      try {
        const output = await runPlaywright(args, currentConfig);
        return parsePlaywrightOutput(output, startTime, options, currentConfig);
      } catch (error) {
        // Return error result
        return {
          id: `E2E-${Date.now()}`,
          executedAt: new Date().toISOString(),
          duration: Date.now() - startTime,
          environment: {
            ci: !!process.env.CI,
            browser: options.browser || currentConfig.defaultBrowser,
            workers: options.workers || currentConfig.workers,
          },
          suites: [],
          summary: {
            total: 0,
            passed: 0,
            failed: 1,
            skipped: 0,
            timedOut: 0,
            flaky: 0,
          },
          reports: {},
        };
      }
    },

    async runTestFile(testFile: string, options: TestExecutionOptions = {}): Promise<TestExecutionResult> {
      return this.runTests({ ...options, filter: testFile });
    },

    generateReport(result: TestExecutionResult, format: E2EReportFormat = 'markdown'): E2EReport {
      let content: string;

      switch (format) {
        case 'json':
          content = JSON.stringify(result, null, 2);
          break;
        case 'text':
          content = formatAsText(result);
          break;
        case 'html':
          content = formatAsHtml(result);
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
        resultId: result.id,
      };
    },

    async writeTestFiles(result: TestGenerationResult): Promise<void> {
      for (const file of result.files) {
        const fullPath = path.join(currentConfig.testDir, file.path);
        await fs.mkdir(path.dirname(fullPath), { recursive: true });
        await fs.writeFile(fullPath, file.content, 'utf-8');
      }
    },

    getConfig(): E2ERunnerBridgeConfig {
      return { ...currentConfig };
    },

    updateConfig(config: Partial<E2ERunnerBridgeConfig>): void {
      currentConfig = { ...currentConfig, ...config };
    },

    async checkPlaywrightInstalled(): Promise<boolean> {
      try {
        await runCommand('npx', ['playwright', '--version']);
        return true;
      } catch {
        return false;
      }
    },

    generatePlaywrightConfig(): string {
      return generatePlaywrightConfigFile(currentConfig);
    },
  };
}

// ============================================================================
// Test Generation Helpers
// ============================================================================

function generateTestFile(flow: UserFlow, _config: E2ERunnerBridgeConfig): string {
  const lines: string[] = [];

  lines.push(`import { test, expect } from '@playwright/test';`);
  lines.push('');
  lines.push(`test.describe('${flow.name}', () => {`);

  // beforeEach hook
  if (flow.setup && flow.setup.length > 0) {
    lines.push('  test.beforeEach(async ({ page }) => {');
    for (const step of flow.setup) {
      lines.push(`    ${generateStepCode(step)}`);
    }
    lines.push('  });');
    lines.push('');
  }

  // Main test
  lines.push(`  test('should complete ${toKebabCase(flow.name)} flow', async ({ page }) => {`);
  lines.push(`    await page.goto('${flow.startUrl}');`);
  lines.push('');

  for (let i = 0; i < flow.steps.length; i++) {
    const step = flow.steps[i];
    lines.push(`    // Step ${i + 1}: ${step.description || step.name}`);
    lines.push(`    ${generateStepCode(step)}`);
    lines.push('');
  }

  lines.push('  });');

  // afterEach hook
  if (flow.teardown && flow.teardown.length > 0) {
    lines.push('');
    lines.push('  test.afterEach(async ({ page }) => {');
    for (const step of flow.teardown) {
      lines.push(`    ${generateStepCode(step)}`);
    }
    lines.push('  });');
  }

  lines.push('});');

  return lines.join('\n');
}

function generateStepCode(step: FlowStep): string {
  switch (step.action) {
    case 'click':
      return `await page.locator('${step.target}').click();`;

    case 'fill':
      return `await page.locator('${step.target}').fill('${step.value || ''}');`;

    case 'navigate':
      return `await page.goto('${step.target}');`;

    case 'wait':
      if (step.timeout) {
        return `await page.waitForTimeout(${step.timeout});`;
      }
      return `await page.locator('${step.target}').waitFor();`;

    case 'assert':
      if (step.expected) {
        return `await expect(page.locator('${step.target}')).toContainText('${step.expected}');`;
      }
      return `await expect(page.locator('${step.target}')).toBeVisible();`;

    case 'custom':
      return step.value || '// Custom action';

    default:
      return `// Unknown action: ${step.action}`;
  }
}

function generateFixtureFile(flow: UserFlow): string {
  const fixture: Record<string, unknown> = {
    flowName: flow.name,
    startUrl: flow.startUrl,
    metadata: {
      tags: flow.tags || [],
      description: flow.description || '',
    },
  };

  return JSON.stringify(fixture, null, 2);
}

// ============================================================================
// Test Execution Helpers
// ============================================================================

function buildPlaywrightArgs(
  options: TestExecutionOptions,
  _config: E2ERunnerBridgeConfig
): string[] {
  const args = ['playwright', 'test'];

  if (options.browser) {
    args.push('--project', options.browser);
  }

  if (options.headed) {
    args.push('--headed');
  }

  if (options.debug) {
    args.push('--debug');
  }

  if (options.trace) {
    args.push('--trace', typeof options.trace === 'string' ? options.trace : 'on');
  }

  if (options.workers !== undefined) {
    args.push('--workers', options.workers.toString());
  }

  if (options.retries !== undefined) {
    args.push('--retries', options.retries.toString());
  }

  if (options.timeout !== undefined) {
    args.push('--timeout', options.timeout.toString());
  }

  if (options.filter) {
    args.push(options.filter);
  }

  // Add JSON reporter for parsing
  args.push('--reporter', 'json');

  return args;
}

function runPlaywright(args: string[], _config: E2ERunnerBridgeConfig): Promise<string> {
  return runCommand('npx', args);
}

function parsePlaywrightOutput(
  output: string,
  startTime: number,
  options: TestExecutionOptions,
  config: E2ERunnerBridgeConfig
): TestExecutionResult {
  const duration = Date.now() - startTime;

  // Try to parse JSON output
  try {
    const jsonResult = JSON.parse(output);

    const suites: TestSuiteResult[] = [];
    let total = 0;
    let passed = 0;
    let failed = 0;
    let skipped = 0;
    let timedOut = 0;
    let flaky = 0;

    if (jsonResult.suites) {
      for (const suite of jsonResult.suites) {
        const tests: TestResult[] = [];

        for (const spec of suite.specs || []) {
          for (const test of spec.tests || []) {
            total++;
            const status = test.status || 'passed';

            if (status === 'passed') passed++;
            else if (status === 'failed') failed++;
            else if (status === 'skipped') skipped++;
            else if (status === 'timedOut') timedOut++;

            if (test.results?.length > 1) flaky++;

            tests.push({
              title: test.title || spec.title,
              file: suite.file || '',
              status,
              duration: test.results?.[0]?.duration || 0,
              error: test.results?.[0]?.error?.message,
              stack: test.results?.[0]?.error?.stack,
              retry: (test.results?.length || 1) - 1,
            });
          }
        }

        suites.push({
          name: suite.title || path.basename(suite.file || 'unknown'),
          file: suite.file || '',
          tests,
          duration: tests.reduce((sum, t) => sum + t.duration, 0),
        });
      }
    }

    return {
      id: `E2E-${Date.now()}`,
      executedAt: new Date().toISOString(),
      duration,
      environment: {
        ci: !!process.env.CI,
        browser: options.browser || config.defaultBrowser,
        workers: options.workers || config.workers,
      },
      suites,
      summary: { total, passed, failed, skipped, timedOut, flaky },
      reports: {},
    };
  } catch {
    // Fallback for non-JSON output
    return {
      id: `E2E-${Date.now()}`,
      executedAt: new Date().toISOString(),
      duration,
      environment: {
        ci: !!process.env.CI,
        browser: options.browser || config.defaultBrowser,
        workers: options.workers || config.workers,
      },
      suites: [],
      summary: {
        total: 0,
        passed: 0,
        failed: 0,
        skipped: 0,
        timedOut: 0,
        flaky: 0,
      },
      reports: {},
    };
  }
}

// ============================================================================
// Report Formatting Helpers
// ============================================================================

function formatAsMarkdown(result: TestExecutionResult): string {
  const lines: string[] = [];

  lines.push('# E2E Test Report');
  lines.push('');
  lines.push(`**Date**: ${result.executedAt}`);
  lines.push(`**Duration**: ${(result.duration / 1000).toFixed(2)}s`);
  lines.push(`**Environment**: ${result.environment.ci ? 'CI' : 'Local'}`);
  lines.push('');

  // Summary table
  lines.push('## Summary');
  lines.push('');
  lines.push('| Status | Count |');
  lines.push('|--------|-------|');
  lines.push(`| ✅ Passed | ${result.summary.passed} |`);
  lines.push(`| ❌ Failed | ${result.summary.failed} |`);
  lines.push(`| ⏭️ Skipped | ${result.summary.skipped} |`);
  lines.push(`| ⏱️ Timed Out | ${result.summary.timedOut} |`);
  lines.push(`| **Total** | ${result.summary.total} |`);
  lines.push('');

  // Browser coverage
  lines.push('## Browser Coverage');
  lines.push('');
  lines.push(`- ${result.environment.browser}: ✅ ${result.summary.passed}/${result.summary.total} passed`);
  lines.push('');

  // Failed tests
  if (result.summary.failed > 0) {
    lines.push('## Failed Tests');
    lines.push('');
    for (const suite of result.suites) {
      for (const test of suite.tests.filter(t => t.status === 'failed')) {
        lines.push(`### ${test.title}`);
        lines.push('');
        lines.push(`- **File**: ${test.file}`);
        if (test.error) {
          lines.push(`- **Error**: ${test.error}`);
        }
        if (test.screenshotPath) {
          lines.push(`- **Screenshot**: ${test.screenshotPath}`);
        }
        lines.push('');
      }
    }
  }

  // Flaky tests
  if (result.summary.flaky > 0) {
    lines.push('## Flaky Tests');
    lines.push('');
    for (const suite of result.suites) {
      for (const test of suite.tests.filter(t => t.retry && t.retry > 0)) {
        lines.push(`- ${test.title}: ${(test.retry ?? 0) + 1} attempts`);
      }
    }
    lines.push('');
  }

  return lines.join('\n');
}

function formatAsText(result: TestExecutionResult): string {
  const lines: string[] = [];

  lines.push('E2E TEST REPORT');
  lines.push('===============');
  lines.push('');
  lines.push(`Date: ${result.executedAt}`);
  lines.push(`Duration: ${(result.duration / 1000).toFixed(2)}s`);
  lines.push(`Environment: ${result.environment.ci ? 'CI' : 'Local'}`);
  lines.push('');
  lines.push('Summary:');
  lines.push(`  Total:     ${result.summary.total}`);
  lines.push(`  Passed:    ${result.summary.passed}`);
  lines.push(`  Failed:    ${result.summary.failed}`);
  lines.push(`  Skipped:   ${result.summary.skipped}`);
  lines.push(`  Timed Out: ${result.summary.timedOut}`);
  lines.push('');

  if (result.summary.failed > 0) {
    lines.push('Failed Tests:');
    for (const suite of result.suites) {
      for (const test of suite.tests.filter(t => t.status === 'failed')) {
        lines.push(`  - ${test.title}`);
        if (test.error) {
          lines.push(`    Error: ${test.error}`);
        }
      }
    }
  }

  return lines.join('\n');
}

function formatAsHtml(result: TestExecutionResult): string {
  // Simple HTML report
  return `<!DOCTYPE html>
<html>
<head>
  <title>E2E Test Report</title>
  <style>
    body { font-family: system-ui, sans-serif; margin: 20px; }
    .passed { color: green; }
    .failed { color: red; }
    .skipped { color: gray; }
    table { border-collapse: collapse; width: 100%; }
    th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
    th { background-color: #f5f5f5; }
  </style>
</head>
<body>
  <h1>E2E Test Report</h1>
  <p><strong>Date:</strong> ${result.executedAt}</p>
  <p><strong>Duration:</strong> ${(result.duration / 1000).toFixed(2)}s</p>
  
  <h2>Summary</h2>
  <table>
    <tr><th>Status</th><th>Count</th></tr>
    <tr class="passed"><td>✅ Passed</td><td>${result.summary.passed}</td></tr>
    <tr class="failed"><td>❌ Failed</td><td>${result.summary.failed}</td></tr>
    <tr class="skipped"><td>⏭️ Skipped</td><td>${result.summary.skipped}</td></tr>
    <tr><td><strong>Total</strong></td><td>${result.summary.total}</td></tr>
  </table>
</body>
</html>`;
}

// ============================================================================
// Config Generation
// ============================================================================

function generatePlaywrightConfigFile(config: E2ERunnerBridgeConfig): string {
  return `import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: '${config.testDir}',
  fullyParallel: ${config.parallel},
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? ${config.retries} : 0,
  workers: process.env.CI ? 1 : ${config.workers},
  reporter: [
    ['html'],
    ['json', { outputFile: 'test-results.json' }],
  ],
  use: {
    baseURL: '${config.baseUrl}',
    trace: 'retain-on-failure',
    screenshot: 'only-on-failure',
  },
  timeout: ${config.defaultTimeout},
  projects: [
    {
      name: 'chromium',
      use: { ...devices['Desktop Chrome'] },
    },
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
  ],
});
`;
}

// ============================================================================
// Utility Functions
// ============================================================================

function toKebabCase(str: string): string {
  return str
    .replace(/([a-z])([A-Z])/g, '$1-$2')
    .replace(/[\s_]+/g, '-')
    .toLowerCase();
}

function runCommand(cmd: string, args: string[]): Promise<string> {
  return new Promise((resolve, reject) => {
    const proc = spawn(cmd, args, { shell: true });
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

/**
 * Parse user flow from Markdown description
 */
export function parseFlowFromMarkdown(markdown: string): UserFlow | null {
  const lines = markdown.split('\n');
  let name = '';
  let description = '';
  let startUrl = '/';
  const steps: FlowStep[] = [];

  for (const line of lines) {
    // Extract flow name from heading
    const headingMatch = line.match(/^#+\s+(.+)$/);
    if (headingMatch) {
      name = headingMatch[1];
      continue;
    }

    // Extract description
    if (line.startsWith('Description:') || line.startsWith('**Description**:')) {
      description = line.split(':').slice(1).join(':').trim();
      continue;
    }

    // Extract start URL
    if (line.includes('Start URL:') || line.includes('**URL**:')) {
      startUrl = line.split(':').slice(1).join(':').trim();
      continue;
    }

    // Extract steps from numbered list
    const stepMatch = line.match(/^\d+\.\s+(.+)$/);
    if (stepMatch) {
      const stepText = stepMatch[1];

      // Parse step action
      if (stepText.toLowerCase().includes('click')) {
        const selectorMatch = stepText.match(/['"]([^'"]+)['"]/);
        steps.push({
          name: stepText,
          action: 'click',
          target: selectorMatch ? selectorMatch[1] : '',
        });
      } else if (stepText.toLowerCase().includes('fill') || stepText.toLowerCase().includes('enter') || stepText.toLowerCase().includes('type')) {
        const parts = stepText.match(/['"]([^'"]+)['"]/g) || [];
        steps.push({
          name: stepText,
          action: 'fill',
          target: parts[0]?.replace(/['"]/g, '') || '',
          value: parts[1]?.replace(/['"]/g, '') || '',
        });
      } else if (stepText.toLowerCase().includes('navigate') || stepText.toLowerCase().includes('go to')) {
        const urlMatch = stepText.match(/['"]([^'"]+)['"]/);
        steps.push({
          name: stepText,
          action: 'navigate',
          target: urlMatch ? urlMatch[1] : '/',
        });
      } else if (stepText.toLowerCase().includes('verify') || stepText.toLowerCase().includes('expect') || stepText.toLowerCase().includes('should')) {
        const selectorMatch = stepText.match(/['"]([^'"]+)['"]/);
        steps.push({
          name: stepText,
          action: 'assert',
          target: selectorMatch ? selectorMatch[1] : '',
        });
      }
    }
  }

  if (!name) return null;

  return { name, description, startUrl, steps };
}
