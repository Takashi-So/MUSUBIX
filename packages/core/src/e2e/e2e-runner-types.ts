/**
 * @fileoverview E2E Runner Bridge Types for Agent Skills Integration
 * @traceability REQ-E2E-001, REQ-E2E-002, REQ-E2E-003
 */

// ============================================================================
// Test Generation Types
// ============================================================================

/**
 * User flow step
 */
export interface FlowStep {
  /** Step name */
  name: string;
  /** Step description */
  description?: string;
  /** Step action type */
  action: 'click' | 'fill' | 'navigate' | 'wait' | 'assert' | 'custom';
  /** Target selector or URL */
  target: string;
  /** Input value (for fill actions) */
  value?: string;
  /** Expected result (for assertions) */
  expected?: string;
  /** Timeout in ms */
  timeout?: number;
}

/**
 * User flow definition
 */
export interface UserFlow {
  /** Flow name */
  name: string;
  /** Flow description */
  description?: string;
  /** Starting URL */
  startUrl: string;
  /** Flow steps */
  steps: FlowStep[];
  /** Setup actions (before test) */
  setup?: FlowStep[];
  /** Teardown actions (after test) */
  teardown?: FlowStep[];
  /** Tags for categorization */
  tags?: string[];
}

/**
 * Generated test file
 */
export interface GeneratedTestFile {
  /** File path relative to test directory */
  path: string;
  /** File content */
  content: string;
  /** Flow name */
  flowName: string;
}

/**
 * Test generation result
 */
export interface TestGenerationResult {
  /** Generated files */
  files: GeneratedTestFile[];
  /** Generation timestamp */
  generatedAt: string;
  /** Flows processed */
  flowsProcessed: number;
}

// ============================================================================
// Test Execution Types
// ============================================================================

/**
 * Browser type
 */
export type BrowserType = 'chromium' | 'firefox' | 'webkit';

/**
 * Test execution options
 */
export interface TestExecutionOptions {
  /** Browser to use */
  browser?: BrowserType;
  /** Run headed (show browser) */
  headed?: boolean;
  /** Debug mode */
  debug?: boolean;
  /** Record trace */
  trace?: boolean | 'on' | 'off' | 'retain-on-failure';
  /** Take screenshots */
  screenshot?: boolean | 'on' | 'off' | 'only-on-failure';
  /** Number of workers */
  workers?: number;
  /** Number of retries */
  retries?: number;
  /** Timeout in ms */
  timeout?: number;
  /** Test filter (flow name or pattern) */
  filter?: string;
  /** Project names to run */
  projects?: string[];
}

/**
 * Single test result
 */
export interface TestResult {
  /** Test title */
  title: string;
  /** Test file */
  file: string;
  /** Test status */
  status: 'passed' | 'failed' | 'skipped' | 'timedOut';
  /** Duration in ms */
  duration: number;
  /** Error message (if failed) */
  error?: string;
  /** Error stack (if failed) */
  stack?: string;
  /** Screenshot path (if captured) */
  screenshotPath?: string;
  /** Trace path (if recorded) */
  tracePath?: string;
  /** Retry count */
  retry?: number;
}

/**
 * Test suite result
 */
export interface TestSuiteResult {
  /** Suite name */
  name: string;
  /** Test file */
  file: string;
  /** Individual test results */
  tests: TestResult[];
  /** Suite duration */
  duration: number;
}

/**
 * Complete test execution result
 */
export interface TestExecutionResult {
  /** Execution ID */
  id: string;
  /** Execution timestamp */
  executedAt: string;
  /** Total duration */
  duration: number;
  /** Environment info */
  environment: {
    ci: boolean;
    browser: BrowserType;
    workers: number;
  };
  /** Suite results */
  suites: TestSuiteResult[];
  /** Summary */
  summary: {
    total: number;
    passed: number;
    failed: number;
    skipped: number;
    timedOut: number;
    flaky: number;
  };
  /** Report paths */
  reports: {
    html?: string;
    json?: string;
    junit?: string;
  };
}

// ============================================================================
// Report Types
// ============================================================================

/**
 * E2E report format
 */
export type E2EReportFormat = 'markdown' | 'json' | 'text' | 'html';

/**
 * E2E report
 */
export interface E2EReport {
  /** Report format */
  format: E2EReportFormat;
  /** Report content */
  content: string;
  /** Generated at */
  generatedAt: string;
  /** Result reference */
  resultId: string;
}

// ============================================================================
// Bridge Configuration
// ============================================================================

/**
 * E2E runner bridge configuration
 */
export interface E2ERunnerBridgeConfig {
  /** Test directory */
  testDir: string;
  /** Fixtures directory */
  fixturesDir: string;
  /** Base URL for tests */
  baseUrl: string;
  /** Default timeout */
  defaultTimeout: number;
  /** Default browser */
  defaultBrowser: BrowserType;
  /** Enable parallel execution */
  parallel: boolean;
  /** Number of workers */
  workers: number;
  /** Retries on failure */
  retries: number;
}

/**
 * Default configuration
 */
export const DEFAULT_E2E_RUNNER_CONFIG: E2ERunnerBridgeConfig = {
  testDir: 'tests/e2e',
  fixturesDir: 'tests/e2e/fixtures',
  baseUrl: 'http://localhost:3000',
  defaultTimeout: 30000,
  defaultBrowser: 'chromium',
  parallel: true,
  workers: 4,
  retries: 0,
};

// ============================================================================
// Bridge Interface
// ============================================================================

/**
 * E2E runner bridge interface
 */
export interface E2ERunnerBridge {
  /**
   * Generate test from user flow
   * @param flow User flow definition
   * @returns Generated test files
   */
  generateTest(flow: UserFlow): TestGenerationResult;

  /**
   * Generate tests from multiple flows
   * @param flows User flows
   * @returns Generation result
   */
  generateTests(flows: UserFlow[]): TestGenerationResult;

  /**
   * Run E2E tests
   * @param options Execution options
   * @returns Test execution result
   */
  runTests(options?: TestExecutionOptions): Promise<TestExecutionResult>;

  /**
   * Run specific test file
   * @param testFile Test file path
   * @param options Execution options
   * @returns Test execution result
   */
  runTestFile(testFile: string, options?: TestExecutionOptions): Promise<TestExecutionResult>;

  /**
   * Generate report
   * @param result Execution result
   * @param format Report format
   * @returns Generated report
   */
  generateReport(result: TestExecutionResult, format?: E2EReportFormat): E2EReport;

  /**
   * Write test files to disk
   * @param result Generation result
   */
  writeTestFiles(result: TestGenerationResult): Promise<void>;

  /**
   * Get configuration
   */
  getConfig(): E2ERunnerBridgeConfig;

  /**
   * Update configuration
   * @param config Partial config to update
   */
  updateConfig(config: Partial<E2ERunnerBridgeConfig>): void;

  /**
   * Check if Playwright is installed
   */
  checkPlaywrightInstalled(): Promise<boolean>;

  /**
   * Generate Playwright config
   */
  generatePlaywrightConfig(): string;
}
