/**
 * E2E Testing Framework
 *
 * @fileoverview Main entry point for E2E testing utilities
 * @module @musubix/core/testing
 * @requirement REQ-E2E-001
 */

// Types
export type {
  CliResult,
  CliRunnerOptions,
  ProjectTemplate,
  TestProjectOptions,
  EarsRequirementFixture,
  TripleFixture,
  TestFixtures,
  PerformanceBudget,
  ToolCall,
  ITestContext,
  ITestProject,
  ICliRunner,
} from './types.js';

// Test Project
export {
  createTestProject,
  createTestProjectWithTemplate,
  withTestProject,
} from './test-project.js';

// Test Fixtures
export {
  getFixtures,
  getFixturesWith,
  createRequirementFixture,
  createTripleFixture,
} from './test-fixtures.js';

// CLI Runner
export {
  createCliRunner,
  createCliRunnerInDir,
} from './cli-runner.js';

// Test Context
export {
  TestContext,
  createTestContext,
  withTestContext,
} from './test-context.js';

// Assertions
export {
  isValidEars,
  getEarsPattern,
  hasExitCode,
  isWithinBudget,
  hasTraceability,
  containsPattern,
  matchesC4Schema,
  assertValidEars,
  assertExitCode,
  assertWithinBudget,
  assertHasTraceability,
  assertContainsPattern,
  assertMatchesC4Schema,
} from './assertions.js';
export type { AssertionResult } from './assertions.js';
