/**
 * E2E Runner Types
 *
 * Type definitions for E2E test runner skill
 *
 * @see REQ-E2E-001 - E2E Test Generation
 * @see REQ-E2E-002 - E2E Test Execution
 * @see REQ-E2E-003 - E2E Test Report
 */

/**
 * E2E test framework
 */
export type E2EFramework = 'playwright' | 'cypress' | 'puppeteer' | 'selenium';

/**
 * Test status
 */
export type TestStatus = 'pending' | 'running' | 'passed' | 'failed' | 'skipped';

/**
 * User flow type
 */
export type UserFlowType =
  | 'authentication'
  | 'navigation'
  | 'form-submission'
  | 'data-crud'
  | 'payment'
  | 'custom';

/**
 * E2E test case
 *
 * @see REQ-E2E-001 - E2E Test Generation
 */
export interface E2ETestCase {
  readonly id: string;
  readonly name: string;
  readonly description: string;
  readonly flowType: UserFlowType;
  readonly steps: E2ETestStep[];
  readonly tags: string[];
  readonly timeout: number;
  readonly retries: number;
}

/**
 * E2E test step
 */
export interface E2ETestStep {
  readonly order: number;
  readonly action: string;
  readonly selector?: string;
  readonly value?: string;
  readonly assertion?: string;
  readonly screenshot?: boolean;
}

/**
 * User flow definition
 *
 * @see REQ-E2E-001 - E2E Test Generation
 */
export interface UserFlowDefinition {
  readonly id: string;
  readonly name: string;
  readonly type: UserFlowType;
  readonly description: string;
  readonly preconditions: string[];
  readonly steps: string[];
  readonly expectedOutcome: string;
}

/**
 * E2E test result
 *
 * @see REQ-E2E-002 - E2E Test Execution
 */
export interface E2ETestResult {
  readonly testId: string;
  readonly status: TestStatus;
  readonly duration: number;
  readonly startedAt: Date;
  readonly finishedAt?: Date;
  readonly error?: string;
  readonly screenshots: string[];
  readonly videoPath?: string;
  readonly logs: string[];
}

/**
 * E2E test suite result
 */
export interface E2ESuiteResult {
  readonly suiteId: string;
  readonly name: string;
  readonly framework: E2EFramework;
  readonly totalTests: number;
  readonly passed: number;
  readonly failed: number;
  readonly skipped: number;
  readonly duration: number;
  readonly results: E2ETestResult[];
}

/**
 * E2E test report
 *
 * @see REQ-E2E-003 - E2E Test Report
 */
export interface E2ETestReport {
  readonly id: string;
  readonly generatedAt: Date;
  readonly suites: E2ESuiteResult[];
  readonly summary: {
    readonly totalSuites: number;
    readonly totalTests: number;
    readonly passed: number;
    readonly failed: number;
    readonly skipped: number;
    readonly passRate: number;
    readonly totalDuration: number;
  };
  readonly failedTests: E2ETestResult[];
  readonly screenshots: string[];
}

/**
 * E2E runner configuration
 */
export interface E2ERunnerConfig {
  readonly framework: E2EFramework;
  readonly baseUrl: string;
  readonly outputDir: string;
  readonly screenshotOnFailure: boolean;
  readonly videoRecording: boolean;
  readonly retries: number;
  readonly timeout: number;
  readonly headless: boolean;
  readonly parallel: number;
}

/**
 * Default E2E runner configuration
 */
export const DEFAULT_E2E_RUNNER_CONFIG: E2ERunnerConfig = {
  framework: 'playwright',
  baseUrl: 'http://localhost:3000',
  outputDir: 'test-results/e2e',
  screenshotOnFailure: true,
  videoRecording: false,
  retries: 2,
  timeout: 30000,
  headless: true,
  parallel: 1,
};

/**
 * E2E runner manager interface
 */
export interface E2ERunnerManager {
  /**
   * Generate E2E tests from user flow
   *
   * @param flow - User flow definition
   * @returns Generated test cases
   */
  generateTests(flow: UserFlowDefinition): E2ETestCase[];

  /**
   * Generate tests from multiple flows
   *
   * @param flows - Array of user flow definitions
   * @returns Generated test cases
   */
  generateTestsFromFlows(flows: UserFlowDefinition[]): E2ETestCase[];

  /**
   * Execute E2E test
   *
   * @param testCase - Test case to execute
   * @returns Test result
   */
  executeTest(testCase: E2ETestCase): Promise<E2ETestResult>;

  /**
   * Execute test suite
   *
   * @param tests - Array of test cases
   * @param suiteName - Suite name
   * @returns Suite result
   */
  executeSuite(tests: E2ETestCase[], suiteName: string): Promise<E2ESuiteResult>;

  /**
   * Generate test report
   *
   * @param suites - Suite results
   * @returns Test report
   */
  generateReport(suites: E2ESuiteResult[]): E2ETestReport;

  /**
   * Get configuration
   */
  getConfig(): E2ERunnerConfig;
}
