/**
 * Integration Test Generator
 * 
 * Generates integration tests for component interactions
 * 
 * @packageDocumentation
 * @module codegen/integration-test-generator
 * 
 * @see REQ-TST-002 - Integration Test Generation
 * @see Article VII - Quality Assurance Standards
 */

import type { TestFramework, AssertionStyle, TestMock } from './unit-test-generator.js';

/**
 * Integration test type
 */
export type IntegrationTestType =
  | 'api'
  | 'database'
  | 'service'
  | 'component'
  | 'workflow'
  | 'event'
  | 'message-queue'
  | 'file-system'
  | 'external-service';

/**
 * Test fixture
 */
export interface TestFixture {
  /** Fixture name */
  name: string;
  /** Fixture type */
  type: 'database' | 'file' | 'mock-server' | 'state' | 'config';
  /** Setup data */
  data: unknown;
  /** Cleanup required */
  cleanupRequired: boolean;
}

/**
 * Integration test scenario
 */
export interface IntegrationTestScenario {
  /** Scenario name */
  name: string;
  /** Description */
  description: string;
  /** Test type */
  type: IntegrationTestType;
  /** Components involved */
  components: string[];
  /** Preconditions */
  preconditions: string[];
  /** Steps */
  steps: TestStep[];
  /** Expected outcomes */
  expectedOutcomes: ExpectedOutcome[];
  /** Fixtures */
  fixtures?: TestFixture[];
  /** Mocks */
  mocks?: TestMock[];
  /** Timeout (ms) */
  timeout?: number;
  /** Tags */
  tags?: string[];
}

/**
 * Test step
 */
export interface TestStep {
  /** Step number */
  order: number;
  /** Action description */
  action: string;
  /** Target component */
  target: string;
  /** Method/endpoint */
  method?: string;
  /** Input data */
  input?: unknown;
  /** Wait condition */
  waitFor?: string;
  /** Delay (ms) */
  delay?: number;
}

/**
 * Expected outcome
 */
export interface ExpectedOutcome {
  /** Component */
  component: string;
  /** Assertion type */
  type: 'state' | 'response' | 'event' | 'side-effect' | 'data';
  /** Expected value */
  expected: unknown;
  /** Matcher */
  matcher?: 'equals' | 'contains' | 'matches' | 'exists' | 'called';
}

/**
 * API endpoint info
 */
export interface ApiEndpointInfo {
  /** HTTP method */
  method: 'GET' | 'POST' | 'PUT' | 'PATCH' | 'DELETE';
  /** Path */
  path: string;
  /** Base URL */
  baseUrl?: string;
  /** Headers */
  headers?: Record<string, string>;
  /** Query parameters */
  queryParams?: Record<string, string>;
  /** Request body schema */
  requestBody?: Record<string, unknown>;
  /** Response schema */
  responseSchema?: Record<string, unknown>;
  /** Authentication type */
  auth?: 'none' | 'bearer' | 'basic' | 'api-key';
}

/**
 * Service interaction info
 */
export interface ServiceInteractionInfo {
  /** Source service */
  source: string;
  /** Target service */
  target: string;
  /** Interaction type */
  type: 'sync' | 'async' | 'event' | 'message';
  /** Method/topic */
  method: string;
  /** Input */
  input?: Record<string, unknown>;
  /** Expected output */
  output?: Record<string, unknown>;
}

/**
 * Integration test suite
 */
export interface IntegrationTestSuite {
  /** Suite name */
  name: string;
  /** Description */
  description: string;
  /** Test type */
  type: IntegrationTestType;
  /** Scenarios */
  scenarios: IntegrationTestScenario[];
  /** Global fixtures */
  fixtures: TestFixture[];
  /** Global setup */
  globalSetup?: string;
  /** Global teardown */
  globalTeardown?: string;
}

/**
 * Generated integration test
 */
export interface GeneratedIntegrationTest {
  /** Test content */
  content: string;
  /** File path */
  filePath: string;
  /** Scenario count */
  scenarioCount: number;
  /** Fixtures used */
  fixtures: string[];
  /** External dependencies */
  externalDependencies: string[];
  /** Estimated duration (ms) */
  estimatedDuration: number;
  /** Warnings */
  warnings: string[];
}

/**
 * Integration test generator config
 */
export interface IntegrationTestGeneratorConfig {
  /** Test framework */
  framework: TestFramework;
  /** Assertion style */
  assertionStyle: AssertionStyle;
  /** Include fixtures */
  includeFixtures: boolean;
  /** Generate cleanup */
  generateCleanup: boolean;
  /** Default timeout */
  defaultTimeout: number;
  /** Test file suffix */
  testFileSuffix: string;
  /** Use containers */
  useContainers: boolean;
  /** Base URL for API tests */
  apiBaseUrl: string;
  /** Database connection string pattern */
  dbConnectionPattern: string;
}

/**
 * Default configuration
 */
export const DEFAULT_INTEGRATION_CONFIG: IntegrationTestGeneratorConfig = {
  framework: 'jest',
  assertionStyle: 'expect',
  includeFixtures: true,
  generateCleanup: true,
  defaultTimeout: 30000,
  testFileSuffix: '.integration.test',
  useContainers: false,
  apiBaseUrl: 'http://localhost:3000',
  dbConnectionPattern: 'postgresql://localhost:5432/test',
};

/**
 * Integration Test Generator
 */
export class IntegrationTestGenerator {
  private config: IntegrationTestGeneratorConfig;

  constructor(config?: Partial<IntegrationTestGeneratorConfig>) {
    this.config = { ...DEFAULT_INTEGRATION_CONFIG, ...config };
  }

  /**
   * Generate API integration tests
   */
  generateApiTests(
    endpoints: ApiEndpointInfo[],
    targetFile: string
  ): GeneratedIntegrationTest {
    const scenarios = endpoints.map((endpoint) => this.createApiScenario(endpoint));
    const suite: IntegrationTestSuite = {
      name: 'API Integration Tests',
      description: 'Integration tests for API endpoints',
      type: 'api',
      scenarios,
      fixtures: [],
    };

    return this.generateTestFile(suite, targetFile);
  }

  /**
   * Generate service integration tests
   */
  generateServiceTests(
    interactions: ServiceInteractionInfo[],
    targetFile: string
  ): GeneratedIntegrationTest {
    const scenarios = interactions.map((interaction) =>
      this.createServiceScenario(interaction)
    );
    const suite: IntegrationTestSuite = {
      name: 'Service Integration Tests',
      description: 'Integration tests for service interactions',
      type: 'service',
      scenarios,
      fixtures: [],
    };

    return this.generateTestFile(suite, targetFile);
  }

  /**
   * Generate database integration tests
   */
  generateDatabaseTests(
    operations: Array<{
      name: string;
      type: 'insert' | 'update' | 'delete' | 'select' | 'transaction';
      table: string;
      data?: unknown;
    }>,
    targetFile: string
  ): GeneratedIntegrationTest {
    const scenarios = operations.map((op) => this.createDatabaseScenario(op));
    const fixtures: TestFixture[] = [
      {
        name: 'database-connection',
        type: 'database',
        data: { connectionString: this.config.dbConnectionPattern },
        cleanupRequired: true,
      },
    ];

    const suite: IntegrationTestSuite = {
      name: 'Database Integration Tests',
      description: 'Integration tests for database operations',
      type: 'database',
      scenarios,
      fixtures,
      globalSetup: this.generateDatabaseSetup(),
      globalTeardown: this.generateDatabaseTeardown(),
    };

    return this.generateTestFile(suite, targetFile);
  }

  /**
   * Generate workflow integration tests
   */
  generateWorkflowTests(
    workflows: Array<{
      name: string;
      steps: string[];
      expectedState: Record<string, unknown>;
    }>,
    targetFile: string
  ): GeneratedIntegrationTest {
    const scenarios = workflows.map((workflow) =>
      this.createWorkflowScenario(workflow)
    );
    const suite: IntegrationTestSuite = {
      name: 'Workflow Integration Tests',
      description: 'Integration tests for business workflows',
      type: 'workflow',
      scenarios,
      fixtures: [],
    };

    return this.generateTestFile(suite, targetFile);
  }

  /**
   * Generate from scenarios
   */
  generateFromScenarios(
    scenarios: IntegrationTestScenario[],
    suiteName: string,
    targetFile: string
  ): GeneratedIntegrationTest {
    const suite: IntegrationTestSuite = {
      name: suiteName,
      description: `Integration tests: ${suiteName}`,
      type: scenarios[0]?.type ?? 'component',
      scenarios,
      fixtures: this.collectFixtures(scenarios),
    };

    return this.generateTestFile(suite, targetFile);
  }

  /**
   * Create API scenario
   */
  private createApiScenario(endpoint: ApiEndpointInfo): IntegrationTestScenario {
    const steps: TestStep[] = [
      {
        order: 1,
        action: `Send ${endpoint.method} request to ${endpoint.path}`,
        target: 'api',
        method: endpoint.method,
        input: endpoint.requestBody,
      },
    ];

    const expectedOutcomes: ExpectedOutcome[] = [
      {
        component: 'api',
        type: 'response',
        expected: { status: endpoint.method === 'POST' ? 201 : 200 },
        matcher: 'contains',
      },
    ];

    if (endpoint.responseSchema) {
      expectedOutcomes.push({
        component: 'api',
        type: 'response',
        expected: endpoint.responseSchema,
        matcher: 'matches',
      });
    }

    return {
      name: `${endpoint.method} ${endpoint.path}`,
      description: `Test ${endpoint.method} ${endpoint.path} endpoint`,
      type: 'api',
      components: ['api'],
      preconditions: endpoint.auth !== 'none' ? ['User is authenticated'] : [],
      steps,
      expectedOutcomes,
      timeout: this.config.defaultTimeout,
      tags: ['api', endpoint.method.toLowerCase()],
    };
  }

  /**
   * Create service scenario
   */
  private createServiceScenario(
    interaction: ServiceInteractionInfo
  ): IntegrationTestScenario {
    const steps: TestStep[] = [
      {
        order: 1,
        action: `Call ${interaction.method} on ${interaction.target}`,
        target: interaction.target,
        method: interaction.method,
        input: interaction.input,
      },
    ];

    if (interaction.type === 'async' || interaction.type === 'event') {
      steps.push({
        order: 2,
        action: 'Wait for response/event',
        target: interaction.source,
        waitFor: 'response',
        delay: 1000,
      });
    }

    return {
      name: `${interaction.source} → ${interaction.target}`,
      description: `Test ${interaction.source} calling ${interaction.target}.${interaction.method}`,
      type: 'service',
      components: [interaction.source, interaction.target],
      preconditions: ['Services are running'],
      steps,
      expectedOutcomes: [
        {
          component: interaction.source,
          type: 'response',
          expected: interaction.output ?? {},
          matcher: interaction.output ? 'equals' : 'exists',
        },
      ],
      tags: ['service', interaction.type],
    };
  }

  /**
   * Create database scenario
   */
  private createDatabaseScenario(operation: {
    name: string;
    type: string;
    table: string;
    data?: unknown;
  }): IntegrationTestScenario {
    const steps: TestStep[] = [];
    const expectedOutcomes: ExpectedOutcome[] = [];

    switch (operation.type) {
      case 'insert':
        steps.push({
          order: 1,
          action: `Insert into ${operation.table}`,
          target: 'database',
          method: 'insert',
          input: operation.data,
        });
        expectedOutcomes.push({
          component: 'database',
          type: 'data',
          expected: { rowCount: 1 },
          matcher: 'contains',
        });
        break;

      case 'select':
        steps.push({
          order: 1,
          action: `Select from ${operation.table}`,
          target: 'database',
          method: 'select',
          input: operation.data,
        });
        expectedOutcomes.push({
          component: 'database',
          type: 'data',
          expected: { rows: [] },
          matcher: 'exists',
        });
        break;

      case 'update':
        steps.push(
          {
            order: 1,
            action: `Setup: Insert test data into ${operation.table}`,
            target: 'database',
            method: 'insert',
            input: operation.data,
          },
          {
            order: 2,
            action: `Update ${operation.table}`,
            target: 'database',
            method: 'update',
            input: operation.data,
          }
        );
        expectedOutcomes.push({
          component: 'database',
          type: 'data',
          expected: { rowCount: 1 },
          matcher: 'contains',
        });
        break;

      case 'delete':
        steps.push(
          {
            order: 1,
            action: `Setup: Insert test data into ${operation.table}`,
            target: 'database',
            method: 'insert',
            input: operation.data,
          },
          {
            order: 2,
            action: `Delete from ${operation.table}`,
            target: 'database',
            method: 'delete',
          }
        );
        expectedOutcomes.push({
          component: 'database',
          type: 'data',
          expected: { rowCount: 1 },
          matcher: 'contains',
        });
        break;

      case 'transaction':
        steps.push(
          {
            order: 1,
            action: 'Begin transaction',
            target: 'database',
            method: 'beginTransaction',
          },
          {
            order: 2,
            action: `Perform operations on ${operation.table}`,
            target: 'database',
            method: 'execute',
            input: operation.data,
          },
          {
            order: 3,
            action: 'Commit transaction',
            target: 'database',
            method: 'commit',
          }
        );
        expectedOutcomes.push({
          component: 'database',
          type: 'state',
          expected: { committed: true },
          matcher: 'equals',
        });
        break;
    }

    return {
      name: operation.name,
      description: `Database ${operation.type} test for ${operation.table}`,
      type: 'database',
      components: ['database', operation.table],
      preconditions: ['Database connection established', 'Test database clean'],
      steps,
      expectedOutcomes,
      tags: ['database', operation.type],
    };
  }

  /**
   * Create workflow scenario
   */
  private createWorkflowScenario(workflow: {
    name: string;
    steps: string[];
    expectedState: Record<string, unknown>;
  }): IntegrationTestScenario {
    const steps: TestStep[] = workflow.steps.map((step, index) => ({
      order: index + 1,
      action: step,
      target: 'workflow',
    }));

    const expectedOutcomes: ExpectedOutcome[] = Object.entries(
      workflow.expectedState
    ).map(([key, value]) => ({
      component: 'workflow',
      type: 'state' as const,
      expected: { [key]: value },
      matcher: 'equals' as const,
    }));

    return {
      name: workflow.name,
      description: `Workflow test: ${workflow.name}`,
      type: 'workflow',
      components: ['workflow'],
      preconditions: ['System in initial state'],
      steps,
      expectedOutcomes,
      tags: ['workflow', 'e2e'],
    };
  }

  /**
   * Generate test file
   */
  private generateTestFile(
    suite: IntegrationTestSuite,
    targetFile: string
  ): GeneratedIntegrationTest {
    const lines: string[] = [];

    // Imports
    lines.push(this.generateImports(suite));
    lines.push('');

    // Global setup
    if (suite.globalSetup) {
      lines.push(suite.globalSetup);
      lines.push('');
    }

    // Describe block
    lines.push(`describe('${suite.name}', () => {`);
    
    // Setup/teardown
    if (this.config.includeFixtures && suite.fixtures.length > 0) {
      lines.push(this.generateFixtureSetup(suite.fixtures));
    }

    if (suite.globalTeardown) {
      lines.push(`  afterAll(async () => {`);
      lines.push(`    ${suite.globalTeardown}`);
      lines.push(`  });`);
      lines.push('');
    }

    // Scenarios
    for (const scenario of suite.scenarios) {
      lines.push(this.generateScenarioTest(scenario));
      lines.push('');
    }

    lines.push('});');

    // Calculate metadata
    const content = lines.join('\n');
    const filePath = this.getTestFilePath(targetFile);
    const fixtures = suite.fixtures.map((f) => f.name);
    const externalDeps = this.collectExternalDependencies(suite);
    const estimatedDuration = this.estimateDuration(suite);

    return {
      content,
      filePath,
      scenarioCount: suite.scenarios.length,
      fixtures,
      externalDependencies: externalDeps,
      estimatedDuration,
      warnings: this.generateWarnings(suite),
    };
  }

  /**
   * Generate imports
   */
  private generateImports(suite: IntegrationTestSuite): string {
    const lines: string[] = [];

    // Framework imports
    switch (this.config.framework) {
      case 'jest':
        // Jest globals are available
        break;
      case 'vitest':
        lines.push("import { describe, it, expect, beforeAll, afterAll, beforeEach, afterEach } from 'vitest';");
        break;
      case 'mocha':
        lines.push("import { expect } from 'chai';");
        break;
    }

    // Type-specific imports
    if (suite.type === 'api') {
      lines.push("import request from 'supertest';");
    }

    if (suite.type === 'database') {
      lines.push("import { Pool } from 'pg';");
    }

    if (this.config.useContainers) {
      lines.push("import { GenericContainer, StartedTestContainer } from 'testcontainers';");
    }

    return lines.join('\n');
  }

  /**
   * Generate fixture setup
   */
  private generateFixtureSetup(fixtures: TestFixture[]): string {
    const lines: string[] = [];
    
    // Declare fixture variables
    for (const fixture of fixtures) {
      lines.push(`  let ${fixture.name.replace(/-/g, '_')}: any;`);
    }
    lines.push('');

    // Setup
    lines.push('  beforeAll(async () => {');
    for (const fixture of fixtures) {
      const varName = fixture.name.replace(/-/g, '_');
      switch (fixture.type) {
        case 'database':
          lines.push(`    ${varName} = await setupDatabase(${JSON.stringify(fixture.data)});`);
          break;
        case 'mock-server':
          lines.push(`    ${varName} = await startMockServer(${JSON.stringify(fixture.data)});`);
          break;
        case 'file':
          lines.push(`    ${varName} = await setupTestFiles(${JSON.stringify(fixture.data)});`);
          break;
        default:
          lines.push(`    ${varName} = ${JSON.stringify(fixture.data)};`);
      }
    }
    lines.push('  });');
    lines.push('');

    // Teardown
    if (fixtures.some((f) => f.cleanupRequired)) {
      lines.push('  afterAll(async () => {');
      for (const fixture of fixtures.filter((f) => f.cleanupRequired)) {
        const varName = fixture.name.replace(/-/g, '_');
        switch (fixture.type) {
          case 'database':
            lines.push(`    await ${varName}?.end();`);
            break;
          case 'mock-server':
            lines.push(`    await ${varName}?.close();`);
            break;
          case 'file':
            lines.push(`    await cleanupTestFiles(${varName});`);
            break;
        }
      }
      lines.push('  });');
      lines.push('');
    }

    return lines.join('\n');
  }

  /**
   * Generate scenario test
   */
  private generateScenarioTest(scenario: IntegrationTestScenario): string {
    const lines: string[] = [];
    const timeout = scenario.timeout ?? this.config.defaultTimeout;

    lines.push(`  describe('${scenario.name}', () => {`);
    
    // Add tags as comments
    if (scenario.tags?.length) {
      lines.push(`    // Tags: ${scenario.tags.join(', ')}`);
    }

    // Preconditions setup
    if (scenario.preconditions.length > 0) {
      lines.push('    // Preconditions:');
      for (const precondition of scenario.preconditions) {
        lines.push(`    //   - ${precondition}`);
      }
    }

    // Generate test based on type
    switch (scenario.type) {
      case 'api':
        lines.push(this.generateApiTest(scenario, timeout));
        break;
      case 'database':
        lines.push(this.generateDatabaseTest(scenario, timeout));
        break;
      case 'service':
        lines.push(this.generateServiceTest(scenario, timeout));
        break;
      case 'workflow':
        lines.push(this.generateWorkflowTest(scenario, timeout));
        break;
      default:
        lines.push(this.generateGenericTest(scenario, timeout));
    }

    lines.push('  });');

    return lines.join('\n');
  }

  /**
   * Generate API test
   */
  private generateApiTest(scenario: IntegrationTestScenario, timeout: number): string {
    const lines: string[] = [];
    const step = scenario.steps[0];

    lines.push(`    it('${scenario.description}', async () => {`);
    lines.push(`      const response = await request(app)`);
    lines.push(`        .${(step?.method ?? 'get').toLowerCase()}('${step?.target ?? '/'}')`);
    
    if (step?.input) {
      lines.push(`        .send(${JSON.stringify(step.input)})`);
    }
    
    lines.push(`        .expect('Content-Type', /json/);`);
    lines.push('');

    for (const outcome of scenario.expectedOutcomes) {
      if (outcome.type === 'response') {
        const expected = outcome.expected as Record<string, unknown>;
        if (expected.status) {
          lines.push(`      expect(response.status).toBe(${expected.status});`);
        }
        if (expected.body) {
          lines.push(`      expect(response.body).toMatchObject(${JSON.stringify(expected.body)});`);
        }
      }
    }

    lines.push(`    }, ${timeout});`);

    return lines.join('\n');
  }

  /**
   * Generate database test
   */
  private generateDatabaseTest(scenario: IntegrationTestScenario, timeout: number): string {
    const lines: string[] = [];

    lines.push(`    it('${scenario.description}', async () => {`);
    lines.push('      const client = await pool.connect();');
    lines.push('      try {');

    for (const step of scenario.steps) {
      lines.push(`        // Step ${step.order}: ${step.action}`);
      switch (step.method) {
        case 'insert':
          lines.push(`        const insertResult = await client.query(`);
          lines.push(`          'INSERT INTO ${step.target} VALUES ($1) RETURNING *',`);
          lines.push(`          [${JSON.stringify(step.input)}]`);
          lines.push('        );');
          break;
        case 'select':
          lines.push(`        const selectResult = await client.query('SELECT * FROM ${step.target}');`);
          break;
        case 'update':
          lines.push(`        const updateResult = await client.query(`);
          lines.push(`          'UPDATE ${step.target} SET data = $1',`);
          lines.push(`          [${JSON.stringify(step.input)}]`);
          lines.push('        );');
          break;
        case 'delete':
          lines.push(`        const deleteResult = await client.query('DELETE FROM ${step.target}');`);
          break;
        case 'beginTransaction':
          lines.push('        await client.query(\'BEGIN\');');
          break;
        case 'commit':
          lines.push('        await client.query(\'COMMIT\');');
          break;
      }
    }

    lines.push('');
    for (const outcome of scenario.expectedOutcomes) {
      const expected = outcome.expected as Record<string, unknown>;
      if (expected.rowCount !== undefined) {
        lines.push(`        expect(result.rowCount).toBe(${expected.rowCount});`);
      }
      if (expected.committed !== undefined) {
        lines.push('        // Transaction committed successfully');
      }
    }

    lines.push('      } finally {');
    lines.push('        client.release();');
    lines.push('      }');
    lines.push(`    }, ${timeout});`);

    return lines.join('\n');
  }

  /**
   * Generate service test
   */
  private generateServiceTest(scenario: IntegrationTestScenario, timeout: number): string {
    const lines: string[] = [];

    lines.push(`    it('${scenario.description}', async () => {`);

    for (const step of scenario.steps) {
      lines.push(`      // Step ${step.order}: ${step.action}`);
      if (step.delay) {
        lines.push(`      await new Promise(resolve => setTimeout(resolve, ${step.delay}));`);
      }
      lines.push(`      const result${step.order} = await ${step.target}.${step.method}(${JSON.stringify(step.input)});`);
    }

    lines.push('');
    for (const outcome of scenario.expectedOutcomes) {
      switch (outcome.matcher) {
        case 'equals':
          lines.push(`      expect(result).toEqual(${JSON.stringify(outcome.expected)});`);
          break;
        case 'contains':
          lines.push(`      expect(result).toMatchObject(${JSON.stringify(outcome.expected)});`);
          break;
        case 'exists':
          lines.push('      expect(result).toBeDefined();');
          break;
        case 'called':
          lines.push(`      expect(${outcome.component}).toHaveBeenCalled();`);
          break;
      }
    }

    lines.push(`    }, ${timeout});`);

    return lines.join('\n');
  }

  /**
   * Generate workflow test
   */
  private generateWorkflowTest(scenario: IntegrationTestScenario, timeout: number): string {
    const lines: string[] = [];

    lines.push(`    it('${scenario.description}', async () => {`);
    lines.push('      let state = initialState;');
    lines.push('');

    for (const step of scenario.steps) {
      lines.push(`      // Step ${step.order}: ${step.action}`);
      lines.push(`      state = await executeStep(state, '${step.action}');`);
    }

    lines.push('');
    for (const outcome of scenario.expectedOutcomes) {
      const expected = outcome.expected as Record<string, unknown>;
      for (const [key, value] of Object.entries(expected)) {
        lines.push(`      expect(state.${key}).toEqual(${JSON.stringify(value)});`);
      }
    }

    lines.push(`    }, ${timeout});`);

    return lines.join('\n');
  }

  /**
   * Generate generic test
   */
  private generateGenericTest(scenario: IntegrationTestScenario, timeout: number): string {
    const lines: string[] = [];

    lines.push(`    it('${scenario.description}', async () => {`);

    for (const step of scenario.steps) {
      lines.push(`      // ${step.action}`);
    }

    lines.push('');
    lines.push('      // Add assertions');
    lines.push('      expect(true).toBe(true);');

    lines.push(`    }, ${timeout});`);

    return lines.join('\n');
  }

  /**
   * Generate database setup
   */
  private generateDatabaseSetup(): string {
    return `
const pool = new Pool({
  connectionString: process.env.DATABASE_URL || '${this.config.dbConnectionPattern}'
});

async function setupDatabase() {
  const client = await pool.connect();
  try {
    // Create test tables
    await client.query(\`
      CREATE TABLE IF NOT EXISTS test_table (
        id SERIAL PRIMARY KEY,
        data JSONB
      )
    \`);
  } finally {
    client.release();
  }
}
`.trim();
  }

  /**
   * Generate database teardown
   */
  private generateDatabaseTeardown(): string {
    return `await pool.end();`;
  }

  /**
   * Collect fixtures from scenarios
   */
  private collectFixtures(scenarios: IntegrationTestScenario[]): TestFixture[] {
    const fixtures = new Map<string, TestFixture>();
    
    for (const scenario of scenarios) {
      if (scenario.fixtures) {
        for (const fixture of scenario.fixtures) {
          if (!fixtures.has(fixture.name)) {
            fixtures.set(fixture.name, fixture);
          }
        }
      }
    }

    return Array.from(fixtures.values());
  }

  /**
   * Collect external dependencies
   */
  private collectExternalDependencies(suite: IntegrationTestSuite): string[] {
    const deps = new Set<string>();

    if (suite.type === 'api') {
      deps.add('supertest');
    }

    if (suite.type === 'database') {
      deps.add('pg');
    }

    if (this.config.useContainers) {
      deps.add('testcontainers');
    }

    return Array.from(deps);
  }

  /**
   * Estimate duration
   */
  private estimateDuration(suite: IntegrationTestSuite): number {
    let duration = 0;

    for (const scenario of suite.scenarios) {
      duration += scenario.timeout ?? this.config.defaultTimeout;
      
      // Add time for each step
      for (const step of scenario.steps) {
        duration += step.delay ?? 100;
      }
    }

    // Add fixture setup time
    duration += suite.fixtures.length * 2000;

    return duration;
  }

  /**
   * Get test file path
   */
  private getTestFilePath(targetFile: string): string {
    const parts = targetFile.split('/');
    const filename = parts.pop()!;
    const ext = filename.split('.').pop();
    const baseName = filename.replace(`.${ext}`, '');
    
    return [...parts, '__tests__', `${baseName}${this.config.testFileSuffix}.${ext}`].join('/');
  }

  /**
   * Generate warnings
   */
  private generateWarnings(suite: IntegrationTestSuite): string[] {
    const warnings: string[] = [];

    if (suite.scenarios.length > 20) {
      warnings.push('Large number of scenarios - consider splitting into multiple files');
    }

    if (suite.type === 'database' && !suite.fixtures.some((f) => f.type === 'database')) {
      warnings.push('Database tests without database fixture - tests may fail');
    }

    const totalDuration = this.estimateDuration(suite);
    if (totalDuration > 300000) {
      warnings.push('Estimated test duration exceeds 5 minutes - consider parallelization');
    }

    return warnings;
  }
}

/**
 * Create integration test generator instance
 */
export function createIntegrationTestGenerator(
  config?: Partial<IntegrationTestGeneratorConfig>
): IntegrationTestGenerator {
  return new IntegrationTestGenerator(config);
}
