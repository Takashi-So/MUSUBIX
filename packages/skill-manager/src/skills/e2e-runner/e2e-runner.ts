/**
 * E2E Runner Implementation
 *
 * E2E test generation, execution, and reporting
 *
 * @see REQ-E2E-001 - E2E Test Generation
 * @see REQ-E2E-002 - E2E Test Execution
 * @see REQ-E2E-003 - E2E Test Report
 */

import type {
  E2ERunnerManager,
  E2ERunnerConfig,
  E2ETestCase,
  E2ETestStep,
  UserFlowDefinition,
  E2ETestResult,
  E2ESuiteResult,
  E2ETestReport,
} from './types.js';
import { DEFAULT_E2E_RUNNER_CONFIG } from './types.js';
import { randomUUID } from 'crypto';

/**
 * Create E2E runner manager
 *
 * @param config - Configuration options
 * @returns E2ERunnerManager instance
 */
export function createE2ERunnerManager(
  config: Partial<E2ERunnerConfig> = {},
): E2ERunnerManager {
  const fullConfig: E2ERunnerConfig = {
    ...DEFAULT_E2E_RUNNER_CONFIG,
    ...config,
  };

  /**
   * Generate test steps from flow definition
   */
  const generateSteps = (flow: UserFlowDefinition): E2ETestStep[] => {
    return flow.steps.map((step, index) => {
      // Parse step string to extract action and details
      const action = step.toLowerCase();
      let selector: string | undefined;
      let value: string | undefined;
      let assertion: string | undefined;

      if (action.includes('click')) {
        selector = extractSelector(step);
      } else if (action.includes('fill') || action.includes('type')) {
        selector = extractSelector(step);
        value = extractValue(step);
      } else if (action.includes('expect') || action.includes('verify')) {
        assertion = step;
      }

      return {
        order: index + 1,
        action: step,
        selector,
        value,
        assertion,
        screenshot: action.includes('verify'),
      };
    });
  };

  /**
   * Extract selector from step description
   */
  const extractSelector = (step: string): string => {
    // Simple extraction - in real impl would be smarter
    const match = step.match(/"([^"]+)"|'([^']+)'|\[([^\]]+)\]/);
    return match ? (match[1] || match[2] || match[3]) : 'button';
  };

  /**
   * Extract value from step description
   */
  const extractValue = (step: string): string => {
    const match = step.match(/with "([^"]+)"|value "([^"]+)"/);
    return match ? (match[1] || match[2]) : '';
  };

  /**
   * Generate E2E tests from user flow
   * @see REQ-E2E-001
   */
  const generateTests = (flow: UserFlowDefinition): E2ETestCase[] => {
    const testCase: E2ETestCase = {
      id: `e2e-${flow.id}`,
      name: `E2E: ${flow.name}`,
      description: flow.description,
      flowType: flow.type,
      steps: generateSteps(flow),
      tags: [flow.type, 'e2e', 'auto-generated'],
      timeout: fullConfig.timeout,
      retries: fullConfig.retries,
    };

    return [testCase];
  };

  /**
   * Generate tests from multiple flows
   * @see REQ-E2E-001
   */
  const generateTestsFromFlows = (flows: UserFlowDefinition[]): E2ETestCase[] => {
    return flows.flatMap(generateTests);
  };

  /**
   * Execute E2E test
   * @see REQ-E2E-002
   */
  const executeTest = async (testCase: E2ETestCase): Promise<E2ETestResult> => {
    const startedAt = new Date();
    const screenshots: string[] = [];
    const logs: string[] = [];

    try {
      // In real implementation, would:
      // 1. Launch browser (Playwright/Cypress)
      // 2. Navigate to baseUrl
      // 3. Execute each step
      // 4. Capture screenshots/videos
      // 5. Collect results

      logs.push(`Starting test: ${testCase.name}`);

      for (const step of testCase.steps) {
        logs.push(`Step ${step.order}: ${step.action}`);
        // Simulate step execution
        await new Promise((resolve) => setTimeout(resolve, 10));

        if (step.screenshot) {
          const screenshotPath = `${fullConfig.outputDir}/${testCase.id}-step-${step.order}.png`;
          screenshots.push(screenshotPath);
        }
      }

      logs.push('Test completed successfully');

      return {
        testId: testCase.id,
        status: 'passed',
        duration: Date.now() - startedAt.getTime(),
        startedAt,
        finishedAt: new Date(),
        screenshots,
        logs,
      };
    } catch (error) {
      return {
        testId: testCase.id,
        status: 'failed',
        duration: Date.now() - startedAt.getTime(),
        startedAt,
        finishedAt: new Date(),
        error: String(error),
        screenshots,
        logs,
      };
    }
  };

  /**
   * Execute test suite
   * @see REQ-E2E-002
   */
  const executeSuite = async (
    tests: E2ETestCase[],
    suiteName: string,
  ): Promise<E2ESuiteResult> => {
    const results: E2ETestResult[] = [];
    const startTime = Date.now();

    for (const test of tests) {
      const result = await executeTest(test);
      results.push(result);
    }

    const passed = results.filter((r) => r.status === 'passed').length;
    const failed = results.filter((r) => r.status === 'failed').length;
    const skipped = results.filter((r) => r.status === 'skipped').length;

    return {
      suiteId: randomUUID(),
      name: suiteName,
      framework: fullConfig.framework,
      totalTests: tests.length,
      passed,
      failed,
      skipped,
      duration: Date.now() - startTime,
      results,
    };
  };

  /**
   * Generate test report
   * @see REQ-E2E-003
   */
  const generateReport = (suites: E2ESuiteResult[]): E2ETestReport => {
    const totalTests = suites.reduce((sum, s) => sum + s.totalTests, 0);
    const passed = suites.reduce((sum, s) => sum + s.passed, 0);
    const failed = suites.reduce((sum, s) => sum + s.failed, 0);
    const skipped = suites.reduce((sum, s) => sum + s.skipped, 0);
    const totalDuration = suites.reduce((sum, s) => sum + s.duration, 0);

    const failedTests = suites.flatMap((s) =>
      s.results.filter((r) => r.status === 'failed'),
    );

    const screenshots = suites.flatMap((s) =>
      s.results.flatMap((r) => r.screenshots),
    );

    return {
      id: randomUUID(),
      generatedAt: new Date(),
      suites,
      summary: {
        totalSuites: suites.length,
        totalTests,
        passed,
        failed,
        skipped,
        passRate: totalTests > 0 ? (passed / totalTests) * 100 : 0,
        totalDuration,
      },
      failedTests,
      screenshots,
    };
  };

  return {
    generateTests,
    generateTestsFromFlows,
    executeTest,
    executeSuite,
    generateReport,
    getConfig: () => fullConfig,
  };
}

/**
 * Format E2E test report as Markdown
 *
 * @param report - Test report
 * @returns Markdown string
 */
export function formatE2EReportMarkdown(report: E2ETestReport): string {
  const { summary } = report;

  const lines: string[] = [
    '# E2E Test Report',
    '',
    `**Generated:** ${report.generatedAt.toISOString()}`,
    '',
    '## Summary',
    '',
    '| Metric | Value |',
    '|--------|-------|',
    `| Total Suites | ${summary.totalSuites} |`,
    `| Total Tests | ${summary.totalTests} |`,
    `| ✅ Passed | ${summary.passed} |`,
    `| ❌ Failed | ${summary.failed} |`,
    `| ⏭️ Skipped | ${summary.skipped} |`,
    `| Pass Rate | ${summary.passRate.toFixed(1)}% |`,
    `| Duration | ${(summary.totalDuration / 1000).toFixed(2)}s |`,
    '',
  ];

  if (report.failedTests.length > 0) {
    lines.push('## Failed Tests', '');
    for (const test of report.failedTests) {
      lines.push(`### ❌ ${test.testId}`);
      lines.push('');
      lines.push(`**Error:** ${test.error || 'Unknown error'}`);
      lines.push(`**Duration:** ${test.duration}ms`);
      lines.push('');
    }
  }

  lines.push('## Suite Results', '');
  for (const suite of report.suites) {
    const icon =
      suite.failed > 0 ? '❌' : suite.skipped > 0 ? '⏭️' : '✅';
    lines.push(
      `### ${icon} ${suite.name} (${suite.framework})`,
    );
    lines.push('');
    lines.push(`- **Tests:** ${suite.totalTests}`);
    lines.push(`- **Passed:** ${suite.passed}`);
    lines.push(`- **Failed:** ${suite.failed}`);
    lines.push(`- **Duration:** ${(suite.duration / 1000).toFixed(2)}s`);
    lines.push('');
  }

  return lines.join('\n');
}

/**
 * Generate E2E test code for Playwright
 *
 * @param testCase - Test case
 * @returns Playwright test code
 */
export function generatePlaywrightCode(testCase: E2ETestCase): string {
  const lines: string[] = [
    `import { test, expect } from '@playwright/test';`,
    '',
    `test('${testCase.name}', async ({ page }) => {`,
    `  // ${testCase.description}`,
    '',
  ];

  for (const step of testCase.steps) {
    if (step.selector && step.action.toLowerCase().includes('click')) {
      lines.push(`  await page.click('${step.selector}');`);
    } else if (step.selector && step.value) {
      lines.push(`  await page.fill('${step.selector}', '${step.value}');`);
    } else if (step.assertion) {
      lines.push(`  // Assertion: ${step.assertion}`);
    }

    if (step.screenshot) {
      lines.push(`  await page.screenshot({ path: 'screenshot-step-${step.order}.png' });`);
    }
  }

  lines.push('});');

  return lines.join('\n');
}
