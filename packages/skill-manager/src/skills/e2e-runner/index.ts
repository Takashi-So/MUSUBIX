/**
 * E2E Runner Skill
 *
 * E2E test generation, execution, and reporting
 *
 * @see REQ-E2E-001 - E2E Test Generation
 * @see REQ-E2E-002 - E2E Test Execution
 * @see REQ-E2E-003 - E2E Test Report
 */

export * from './types.js';
export {
  createE2ERunnerManager,
  formatE2EReportMarkdown,
  generatePlaywrightCode,
} from './e2e-runner.js';
