/**
 * E2E Testing Types
 *
 * @fileoverview Type definitions for E2E testing framework
 * @module @musubix/core/testing/types
 * @requirement REQ-E2E-001
 */

/**
 * CLI execution result
 */
export interface CliResult {
  /** Standard output */
  stdout: string;
  /** Standard error */
  stderr: string;
  /** Exit code */
  exitCode: number;
  /** Execution duration in milliseconds */
  duration: number;
}

/**
 * Options for CLI runner
 */
export interface CliRunnerOptions {
  /** Working directory */
  cwd?: string;
  /** Environment variables */
  env?: Record<string, string>;
  /** Timeout in milliseconds */
  timeout?: number;
  /** Input to pass to stdin */
  input?: string;
}

/**
 * Test project template type
 */
export type ProjectTemplate = 'minimal' | 'full' | 'sdd';

/**
 * Options for creating test project
 */
export interface TestProjectOptions {
  /** Project name (default: auto-generated) */
  name?: string;
  /** Template type */
  template?: ProjectTemplate;
  /** Auto cleanup on destroy (default: true) */
  cleanup?: boolean;
  /** Base directory for test projects */
  baseDir?: string;
}

/**
 * EARS requirement fixture
 */
export interface EarsRequirementFixture {
  /** Requirement ID */
  id: string;
  /** EARS pattern type */
  pattern: 'ubiquitous' | 'event-driven' | 'state-driven' | 'unwanted' | 'optional';
  /** Requirement text */
  text: string;
  /** Is valid EARS format */
  valid: boolean;
}

/**
 * Triple fixture for ontology testing
 */
export interface TripleFixture {
  subject: string;
  predicate: string;
  object: string;
}

/**
 * Test fixtures collection
 */
export interface TestFixtures {
  /** EARS requirements samples */
  requirements: {
    valid: EarsRequirementFixture[];
    invalid: string[];
  };
  /** Code samples */
  code: {
    typescript: string;
    patterns: Record<string, string>;
  };
  /** Triple samples */
  triples: {
    valid: TripleFixture[];
    circular: TripleFixture[];
    inconsistent: TripleFixture[];
  };
}

/**
 * Performance budget for assertions
 */
export interface PerformanceBudget {
  /** Maximum duration in milliseconds */
  maxDuration?: number;
  /** Maximum memory in bytes */
  maxMemory?: number;
}

/**
 * MCP tool call record
 */
export interface ToolCall {
  /** Tool name */
  name: string;
  /** Tool arguments */
  arguments: unknown;
  /** Call timestamp */
  timestamp: Date;
}

/**
 * Test context combining all helpers
 */
export interface ITestContext {
  /** Test project instance */
  readonly project: ITestProject;
  /** Test fixtures */
  readonly fixtures: TestFixtures;
  /** CLI runner */
  readonly cli: ICliRunner;
  /** Cleanup all resources */
  cleanup(): Promise<void>;
}

/**
 * Test project interface
 */
export interface ITestProject {
  /** Project directory path */
  readonly path: string;
  /** Project name */
  readonly name: string;
  /** Create the project */
  create(): Promise<void>;
  /** Destroy the project */
  destroy(): Promise<void>;
  /** Add a file to the project */
  addFile(relativePath: string, content: string): Promise<void>;
  /** Get file content */
  getFile(relativePath: string): Promise<string>;
  /** Check if file exists */
  fileExists(relativePath: string): boolean;
}

/**
 * CLI runner interface
 */
export interface ICliRunner {
  /** Run CLI command */
  run(args: string[], options?: CliRunnerOptions): Promise<CliResult>;
  /** Run CLI with stdin input */
  runWithInput(args: string[], input: string): Promise<CliResult>;
  /** Run requirements subcommand */
  requirements(subcommand: string, ...args: string[]): Promise<CliResult>;
  /** Run design subcommand */
  design(subcommand: string, ...args: string[]): Promise<CliResult>;
  /** Run learn subcommand */
  learn(subcommand: string, ...args: string[]): Promise<CliResult>;
  /** Run ontology subcommand */
  ontology(subcommand: string, ...args: string[]): Promise<CliResult>;
  /** Run perf subcommand */
  perf(subcommand: string, ...args: string[]): Promise<CliResult>;
  /** Run codegen subcommand */
  codegen(subcommand: string, ...args: string[]): Promise<CliResult>;
  /** Run trace subcommand */
  trace(subcommand: string, ...args: string[]): Promise<CliResult>;
}
