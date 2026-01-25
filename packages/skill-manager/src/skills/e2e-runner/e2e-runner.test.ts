/**
 * E2E Runner Tests
 *
 * @see REQ-E2E-001〜003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createE2ERunnerManager,
  formatE2EReportMarkdown,
  generatePlaywrightCode,
  type E2ERunnerConfig,
  type UserFlowDefinition,
  type E2ETestCase,
  type E2ETestReport,
} from '../e2e-runner/index.js';

describe('E2ERunnerManager', () => {
  let manager: ReturnType<typeof createE2ERunnerManager>;

  beforeEach(() => {
    manager = createE2ERunnerManager();
  });

  describe('createE2ERunnerManager', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
      const config = manager.getConfig();
      expect(config.framework).toBe('playwright');
      expect(config.headless).toBe(true);
    });

    it('should create manager with custom config', () => {
      const customConfig: Partial<E2ERunnerConfig> = {
        framework: 'cypress',
        headless: false,
        timeout: 60000,
      };
      const customManager = createE2ERunnerManager(customConfig);
      const config = customManager.getConfig();
      expect(config.framework).toBe('cypress');
      expect(config.headless).toBe(false);
      expect(config.timeout).toBe(60000);
    });
  });

  describe('generateTests', () => {
    it('should generate tests from user flow', () => {
      const flow: UserFlowDefinition = {
        id: 'login-flow',
        name: 'User Login',
        type: 'authentication',
        description: 'Test user login flow',
        preconditions: ['User exists'],
        steps: [
          'Navigate to login page',
          'Fill email field with "user@example.com"',
          'Fill password field with "password"',
          'Click "Login" button',
          'Verify redirect to dashboard',
        ],
        expectedOutcome: 'User is logged in and redirected',
      };

      const tests = manager.generateTests(flow);

      expect(tests.length).toBe(1);
      expect(tests[0].name).toContain('User Login');
      expect(tests[0].flowType).toBe('authentication');
      expect(tests[0].steps.length).toBe(5);
    });
  });

  describe('generateTestsFromFlows', () => {
    it('should generate tests from multiple flows', () => {
      const flows: UserFlowDefinition[] = [
        {
          id: 'flow-1',
          name: 'Flow 1',
          type: 'navigation',
          description: 'Test 1',
          preconditions: [],
          steps: ['Step 1'],
          expectedOutcome: 'Done',
        },
        {
          id: 'flow-2',
          name: 'Flow 2',
          type: 'form-submission',
          description: 'Test 2',
          preconditions: [],
          steps: ['Step 1', 'Step 2'],
          expectedOutcome: 'Done',
        },
      ];

      const tests = manager.generateTestsFromFlows(flows);

      expect(tests.length).toBe(2);
    });
  });

  describe('executeTest', () => {
    it('should execute test and return result', async () => {
      const testCase: E2ETestCase = {
        id: 'test-1',
        name: 'Sample Test',
        description: 'A sample test',
        flowType: 'navigation',
        steps: [
          { order: 1, action: 'Navigate to home' },
          { order: 2, action: 'Click button', selector: 'button' },
        ],
        tags: ['smoke'],
        timeout: 30000,
        retries: 2,
      };

      const result = await manager.executeTest(testCase);

      expect(result.testId).toBe('test-1');
      expect(result.status).toBeDefined();
      expect(result.duration).toBeGreaterThanOrEqual(0);
    });
  });

  describe('executeSuite', () => {
    it('should execute test suite', async () => {
      const tests: E2ETestCase[] = [
        {
          id: 'test-1',
          name: 'Test 1',
          description: 'First test',
          flowType: 'navigation',
          steps: [{ order: 1, action: 'Step 1' }],
          tags: [],
          timeout: 30000,
          retries: 0,
        },
        {
          id: 'test-2',
          name: 'Test 2',
          description: 'Second test',
          flowType: 'navigation',
          steps: [{ order: 1, action: 'Step 1' }],
          tags: [],
          timeout: 30000,
          retries: 0,
        },
      ];

      const result = await manager.executeSuite(tests, 'Test Suite');

      expect(result.name).toBe('Test Suite');
      expect(result.totalTests).toBe(2);
      expect(result.results.length).toBe(2);
    });
  });

  describe('generateReport', () => {
    it('should generate test report', async () => {
      const tests: E2ETestCase[] = [
        {
          id: 'test-1',
          name: 'Test 1',
          description: 'Test',
          flowType: 'navigation',
          steps: [],
          tags: [],
          timeout: 30000,
          retries: 0,
        },
      ];

      const suiteResult = await manager.executeSuite(tests, 'Suite');
      const report = manager.generateReport([suiteResult]);

      expect(report.id).toBeDefined();
      expect(report.generatedAt).toBeInstanceOf(Date);
      expect(report.summary.totalTests).toBe(1);
      expect(report.summary.passRate).toBeDefined();
    });
  });
});

describe('Format functions', () => {
  it('should format E2E report as markdown', () => {
    const report: E2ETestReport = {
      id: 'report-1',
      generatedAt: new Date(),
      suites: [
        {
          suiteId: 'suite-1',
          name: 'Main Suite',
          framework: 'playwright',
          totalTests: 10,
          passed: 8,
          failed: 1,
          skipped: 1,
          duration: 5000,
          results: [],
        },
      ],
      summary: {
        totalSuites: 1,
        totalTests: 10,
        passed: 8,
        failed: 1,
        skipped: 1,
        passRate: 80,
        totalDuration: 5000,
      },
      failedTests: [],
      screenshots: [],
    };

    const markdown = formatE2EReportMarkdown(report);
    expect(markdown).toContain('# E2E Test Report');
    expect(markdown).toContain('Main Suite');
    expect(markdown).toContain('80');
  });

  it('should generate Playwright code', () => {
    const testCase: E2ETestCase = {
      id: 'test-1',
      name: 'Login Test',
      description: 'Test login functionality',
      flowType: 'authentication',
      steps: [
        { order: 1, action: 'Click "Login" button', selector: 'button.login' },
        { order: 2, action: 'Fill email with "test@example.com"', selector: 'input[name=email]', value: 'test@example.com' },
      ],
      tags: [],
      timeout: 30000,
      retries: 0,
    };

    const code = generatePlaywrightCode(testCase);
    expect(code).toContain("import { test, expect } from '@playwright/test'");
    expect(code).toContain('Login Test');
    expect(code).toContain('page.click');
  });
});
