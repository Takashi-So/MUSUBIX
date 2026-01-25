/**
 * @fileoverview E2E Runner Bridge Tests
 * @traceability REQ-E2E-001, REQ-E2E-002, REQ-E2E-003
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import { createE2ERunnerBridge, parseFlowFromMarkdown } from './e2e-runner-bridge.js';
import type { UserFlow, E2ERunnerBridgeConfig } from './e2e-runner-types.js';
import { DEFAULT_E2E_RUNNER_CONFIG } from './e2e-runner-types.js';

describe('E2ERunnerBridge', () => {
  describe('createE2ERunnerBridge', () => {
    it('should create bridge with default config', () => {
      const bridge = createE2ERunnerBridge();
      const config = bridge.getConfig();
      
      expect(config.testDir).toBe(DEFAULT_E2E_RUNNER_CONFIG.testDir);
      expect(config.defaultBrowser).toBe(DEFAULT_E2E_RUNNER_CONFIG.defaultBrowser);
      expect(config.workers).toBe(DEFAULT_E2E_RUNNER_CONFIG.workers);
    });

    it('should create bridge with custom config', () => {
      const customConfig: Partial<E2ERunnerBridgeConfig> = {
        testDir: './custom-tests',
        defaultBrowser: 'firefox',
        workers: 4,
      };
      
      const bridge = createE2ERunnerBridge(customConfig);
      const config = bridge.getConfig();
      
      expect(config.testDir).toBe('./custom-tests');
      expect(config.defaultBrowser).toBe('firefox');
      expect(config.workers).toBe(4);
    });

    it('should update config', () => {
      const bridge = createE2ERunnerBridge();
      
      bridge.updateConfig({ workers: 8 });
      const config = bridge.getConfig();
      
      expect(config.workers).toBe(8);
    });
  });

  describe('generateTest', () => {
    it('should generate test file from user flow', () => {
      const bridge = createE2ERunnerBridge();
      
      const flow: UserFlow = {
        name: 'Login Flow',
        description: 'User login test',
        startUrl: '/login',
        steps: [
          { name: 'Enter username', action: 'fill', target: '#username', value: 'testuser' },
          { name: 'Enter password', action: 'fill', target: '#password', value: 'password123' },
          { name: 'Click login', action: 'click', target: '#login-btn' },
          { name: 'Verify redirect', action: 'assert', target: 'h1', expected: 'Dashboard' },
        ],
      };

      const result = bridge.generateTest(flow);

      expect(result.flowsProcessed).toBe(1);
      expect(result.files.length).toBeGreaterThanOrEqual(1);
      
      const testFile = result.files[0];
      expect(testFile.path).toBe('login-flow.spec.ts');
      expect(testFile.content).toContain("import { test, expect } from '@playwright/test'");
      expect(testFile.content).toContain("test.describe('Login Flow'");
      expect(testFile.content).toContain("await page.goto('/login')");
      expect(testFile.content).toContain("await page.locator('#username').fill('testuser')");
      expect(testFile.content).toContain("await page.locator('#login-btn').click()");
    });

    it('should generate test with setup steps', () => {
      const bridge = createE2ERunnerBridge();
      
      const flow: UserFlow = {
        name: 'Authenticated Test',
        startUrl: '/dashboard',
        setup: [
          { name: 'Navigate to login', action: 'navigate', target: '/login' },
          { name: 'Quick login', action: 'fill', target: '#username', value: 'admin' },
        ],
        steps: [
          { name: 'Check dashboard', action: 'assert', target: '#welcome' },
        ],
      };

      const result = bridge.generateTest(flow);
      const testFile = result.files[0];

      expect(testFile.content).toContain('test.beforeEach');
      expect(result.files.some(f => f.path.includes('fixtures/'))).toBe(true);
    });

    it('should generate multiple tests', () => {
      const bridge = createE2ERunnerBridge();
      
      const flows: UserFlow[] = [
        { name: 'Flow A', startUrl: '/a', steps: [{ name: 's1', action: 'click', target: '#a' }] },
        { name: 'Flow B', startUrl: '/b', steps: [{ name: 's2', action: 'click', target: '#b' }] },
      ];

      const result = bridge.generateTests(flows);

      expect(result.flowsProcessed).toBe(2);
      expect(result.files.some(f => f.path === 'flow-a.spec.ts')).toBe(true);
      expect(result.files.some(f => f.path === 'flow-b.spec.ts')).toBe(true);
    });
  });

  describe('generateReport', () => {
    const mockResult = {
      id: 'E2E-123',
      executedAt: '2025-01-25T12:00:00Z',
      duration: 5000,
      environment: {
        ci: false,
        browser: 'chromium' as const,
        workers: 2,
      },
      suites: [
        {
          name: 'login.spec.ts',
          file: 'tests/login.spec.ts',
          tests: [
            { title: 'should login', file: 'tests/login.spec.ts', status: 'passed' as const, duration: 1000 },
            { title: 'should show error', file: 'tests/login.spec.ts', status: 'failed' as const, duration: 500, error: 'Element not found' },
          ],
          duration: 1500,
        },
      ],
      summary: {
        total: 2,
        passed: 1,
        failed: 1,
        skipped: 0,
        timedOut: 0,
        flaky: 0,
      },
      reports: {},
    };

    it('should generate markdown report', () => {
      const bridge = createE2ERunnerBridge();
      const report = bridge.generateReport(mockResult, 'markdown');

      expect(report.format).toBe('markdown');
      expect(report.content).toContain('# E2E Test Report');
      expect(report.content).toContain('✅ Passed | 1');
      expect(report.content).toContain('❌ Failed | 1');
      expect(report.content).toContain('## Failed Tests');
      expect(report.content).toContain('Element not found');
    });

    it('should generate JSON report', () => {
      const bridge = createE2ERunnerBridge();
      const report = bridge.generateReport(mockResult, 'json');

      expect(report.format).toBe('json');
      const parsed = JSON.parse(report.content);
      expect(parsed.id).toBe('E2E-123');
      expect(parsed.summary.total).toBe(2);
    });

    it('should generate text report', () => {
      const bridge = createE2ERunnerBridge();
      const report = bridge.generateReport(mockResult, 'text');

      expect(report.format).toBe('text');
      expect(report.content).toContain('E2E TEST REPORT');
      expect(report.content).toContain('Total:     2');
      expect(report.content).toContain('Passed:    1');
    });

    it('should generate HTML report', () => {
      const bridge = createE2ERunnerBridge();
      const report = bridge.generateReport(mockResult, 'html');

      expect(report.format).toBe('html');
      expect(report.content).toContain('<!DOCTYPE html>');
      expect(report.content).toContain('<title>E2E Test Report</title>');
      expect(report.content).toContain('✅ Passed');
    });
  });

  describe('generatePlaywrightConfig', () => {
    it('should generate valid Playwright config', () => {
      const bridge = createE2ERunnerBridge({
        testDir: './e2e',
        baseUrl: 'http://localhost:3000',
        workers: 4,
        retries: 2,
      });

      const config = bridge.generatePlaywrightConfig();

      expect(config).toContain("testDir: './e2e'");
      expect(config).toContain("baseURL: 'http://localhost:3000'");
      expect(config).toContain('workers: process.env.CI ? 1 : 4');
      expect(config).toContain('retries: process.env.CI ? 2 : 0');
      expect(config).toContain("name: 'chromium'");
      expect(config).toContain("name: 'firefox'");
      expect(config).toContain("name: 'webkit'");
    });
  });
});

describe('parseFlowFromMarkdown', () => {
  it('should parse flow from markdown', () => {
    const markdown = `# Login Flow

Description: Test user login functionality

Start URL: /login

1. Click on "#username" field
2. Fill "#username" with "testuser"
3. Click "#login-btn"
4. Verify "#welcome" is visible
    `;

    const flow = parseFlowFromMarkdown(markdown);

    expect(flow).not.toBeNull();
    expect(flow!.name).toBe('Login Flow');
    expect(flow!.startUrl).toBe('/login');
    expect(flow!.steps.length).toBe(4);
    expect(flow!.steps[0].action).toBe('click');
    expect(flow!.steps[1].action).toBe('fill');
    expect(flow!.steps[1].value).toBe('testuser');
  });

  it('should return null for empty markdown', () => {
    const flow = parseFlowFromMarkdown('');
    expect(flow).toBeNull();
  });

  it('should handle navigation steps', () => {
    const markdown = `
# Navigation Test

Start URL: /

1. Navigate to "/about"
2. Go to "/contact"
    `;

    const flow = parseFlowFromMarkdown(markdown);

    expect(flow).not.toBeNull();
    expect(flow!.steps[0].action).toBe('navigate');
    expect(flow!.steps[0].target).toBe('/about');
  });
});

describe('Step Code Generation', () => {
  it('should generate correct code for different actions', () => {
    const bridge = createE2ERunnerBridge();

    const flow: UserFlow = {
      name: 'Action Test',
      startUrl: '/',
      steps: [
        { name: 'Click button', action: 'click', target: '#btn' },
        { name: 'Fill input', action: 'fill', target: '#input', value: 'text' },
        { name: 'Navigate', action: 'navigate', target: '/page' },
        { name: 'Wait for element', action: 'wait', target: '#loading' },
        { name: 'Wait timeout', action: 'wait', target: '', timeout: 1000 },
        { name: 'Assert visible', action: 'assert', target: '#result' },
        { name: 'Assert text', action: 'assert', target: '#text', expected: 'Hello' },
        { name: 'Custom action', action: 'custom', target: '', value: 'await page.reload()' },
      ],
    };

    const result = bridge.generateTest(flow);
    const content = result.files[0].content;

    expect(content).toContain("await page.locator('#btn').click()");
    expect(content).toContain("await page.locator('#input').fill('text')");
    expect(content).toContain("await page.goto('/page')");
    expect(content).toContain("await page.locator('#loading').waitFor()");
    expect(content).toContain('await page.waitForTimeout(1000)');
    expect(content).toContain("await expect(page.locator('#result')).toBeVisible()");
    expect(content).toContain("await expect(page.locator('#text')).toContainText('Hello')");
    expect(content).toContain('await page.reload()');
  });
});

describe('Config Management', () => {
  it('should merge configs correctly', () => {
    const bridge = createE2ERunnerBridge({
      testDir: './custom-tests',
    });

    bridge.updateConfig({
      workers: 8,
      retries: 3,
    });

    const config = bridge.getConfig();

    expect(config.testDir).toBe('./custom-tests');
    expect(config.workers).toBe(8);
    expect(config.retries).toBe(3);
    expect(config.parallel).toBe(DEFAULT_E2E_RUNNER_CONFIG.parallel);
  });
});
