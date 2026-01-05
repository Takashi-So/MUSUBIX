/**
 * Test Context Builder
 *
 * @fileoverview Combines test helpers into a unified context
 * @module @musubix/core/testing/test-context
 * @requirement REQ-E2E-002
 */

import type { ITestContext, ITestProject, ICliRunner, TestFixtures, TestProjectOptions, CliRunnerOptions } from './types.js';
import { createTestProjectWithTemplate } from './test-project.js';
import { getFixtures, getFixturesWith } from './test-fixtures.js';
import { createCliRunner } from './cli-runner.js';

/**
 * Test context implementation
 */
class TestContextImpl implements ITestContext {
  readonly project: ITestProject;
  readonly fixtures: TestFixtures;
  readonly cli: ICliRunner;

  constructor(
    project: ITestProject,
    fixtures: TestFixtures,
    cli: ICliRunner
  ) {
    this.project = project;
    this.fixtures = fixtures;
    this.cli = cli;
  }

  /**
   * Cleanup all resources
   */
  async cleanup(): Promise<void> {
    await this.project.destroy();
  }
}

/**
 * Test context builder options
 */
interface TestContextBuilderOptions {
  project?: TestProjectOptions;
  fixtures?: Partial<TestFixtures>;
  cli?: CliRunnerOptions;
  cliPath?: string;
}

/**
 * Test context builder
 */
class TestContextBuilder {
  private projectOptions: TestProjectOptions = { template: 'minimal' };
  private fixturesOverrides: Partial<TestFixtures> | null = null;
  private cliOptions: CliRunnerOptions = {};
  private cliPath?: string;

  /**
   * Configure project options
   */
  withProject(options: TestProjectOptions = {}): this {
    this.projectOptions = { ...this.projectOptions, ...options };
    return this;
  }

  /**
   * Configure fixtures
   */
  withFixtures(fixtures?: Partial<TestFixtures>): this {
    this.fixturesOverrides = fixtures ?? {};
    return this;
  }

  /**
   * Configure CLI runner
   */
  withCliRunner(options: CliRunnerOptions = {}): this {
    this.cliOptions = { ...this.cliOptions, ...options };
    return this;
  }

  /**
   * Set custom CLI path
   */
  withCliPath(path: string): this {
    this.cliPath = path;
    return this;
  }

  /**
   * Build the test context
   */
  async build(): Promise<ITestContext> {
    // Create project
    const project = await createTestProjectWithTemplate(this.projectOptions);

    // Get fixtures
    const fixtures = this.fixturesOverrides
      ? getFixturesWith(this.fixturesOverrides)
      : getFixtures();

    // Create CLI runner with project cwd
    const cli = createCliRunner(this.cliPath, {
      ...this.cliOptions,
      cwd: project.path,
    });

    return new TestContextImpl(project, fixtures, cli);
  }
}

/**
 * Create a test context builder
 *
 * @returns Test context builder
 *
 * @example
 * ```typescript
 * const ctx = await TestContext.builder()
 *   .withProject({ template: 'sdd' })
 *   .withFixtures()
 *   .build();
 *
 * try {
 *   const result = await ctx.cli.run(['--version']);
 *   expect(result.exitCode).toBe(0);
 * } finally {
 *   await ctx.cleanup();
 * }
 * ```
 */
function builder(): TestContextBuilder {
  return new TestContextBuilder();
}

/**
 * Test context static methods
 */
export const TestContext = {
  builder,
};

/**
 * Create a test context with default options
 *
 * @param options - Optional overrides
 * @returns Test context
 */
export async function createTestContext(
  options: TestContextBuilderOptions = {}
): Promise<ITestContext> {
  let builder = TestContext.builder();

  if (options.project) {
    builder = builder.withProject(options.project);
  }

  if (options.fixtures !== undefined) {
    builder = builder.withFixtures(options.fixtures);
  } else {
    builder = builder.withFixtures();
  }

  if (options.cli) {
    builder = builder.withCliRunner(options.cli);
  }

  if (options.cliPath) {
    builder = builder.withCliPath(options.cliPath);
  }

  return builder.build();
}

/**
 * Run test with automatic context management
 *
 * @param options - Context options
 * @param fn - Test function
 *
 * @example
 * ```typescript
 * await withTestContext({ project: { template: 'sdd' } }, async (ctx) => {
 *   const result = await ctx.cli.requirements('analyze', 'requirements.md');
 *   expect(result.exitCode).toBe(0);
 * });
 * // Context is automatically cleaned up
 * ```
 */
export async function withTestContext<T>(
  options: TestContextBuilderOptions,
  fn: (ctx: ITestContext) => Promise<T>
): Promise<T> {
  const ctx = await createTestContext(options);
  try {
    return await fn(ctx);
  } finally {
    await ctx.cleanup();
  }
}
