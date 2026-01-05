/**
 * Unit Test Generator
 * 
 * Generates unit tests from code and specifications
 * 
 * @packageDocumentation
 * @module codegen/unit-test-generator
 * 
 * @see REQ-TST-001 - Unit Test Generation
 * @see Article VII - Quality Assurance Standards
 */

/**
 * Test framework type
 */
export type TestFramework = 'jest' | 'mocha' | 'vitest' | 'ava' | 'tap' | 'pytest' | 'unittest' | 'junit' | 'nunit' | 'xunit' | 'go-test';

/**
 * Test assertion style
 */
export type AssertionStyle = 'expect' | 'assert' | 'should' | 'chai';

/**
 * Test target type
 */
export type TestTargetType = 'function' | 'method' | 'class' | 'module' | 'component';

/**
 * Test case info
 */
export interface TestCaseInfo {
  /** Test case name */
  name: string;
  /** Description */
  description: string;
  /** Test type */
  type: 'unit' | 'edge' | 'boundary' | 'error' | 'null';
  /** Input values */
  inputs: TestInput[];
  /** Expected output */
  expectedOutput: TestOutput;
  /** Setup code */
  setup?: string;
  /** Teardown code */
  teardown?: string;
  /** Mocks required */
  mocks?: TestMock[];
  /** Tags */
  tags?: string[];
}

/**
 * Test input
 */
export interface TestInput {
  /** Parameter name */
  name: string;
  /** Value */
  value: unknown;
  /** Type */
  type: string;
  /** Description */
  description?: string;
}

/**
 * Test output
 */
export interface TestOutput {
  /** Expected value */
  value?: unknown;
  /** Expected type */
  type?: string;
  /** Expected error */
  error?: {
    type: string;
    message?: string;
  };
  /** Custom assertion */
  assertion?: string;
}

/**
 * Test mock
 */
export interface TestMock {
  /** Module or object to mock */
  target: string;
  /** Method to mock */
  method?: string;
  /** Return value */
  returnValue?: unknown;
  /** Implementation */
  implementation?: string;
  /** Is spy */
  isSpy?: boolean;
}

/**
 * Test suite info
 */
export interface TestSuiteInfo {
  /** Suite name */
  name: string;
  /** Description */
  description: string;
  /** Target file */
  targetFile: string;
  /** Test framework */
  framework: TestFramework;
  /** Test cases */
  testCases: TestCaseInfo[];
  /** Imports */
  imports: string[];
  /** Setup */
  beforeAll?: string;
  /** Teardown */
  afterAll?: string;
  /** Before each */
  beforeEach?: string;
  /** After each */
  afterEach?: string;
}

/**
 * Function to test
 */
export interface FunctionToTest {
  /** Function name */
  name: string;
  /** Parameters */
  parameters: Array<{
    name: string;
    type: string;
    optional?: boolean;
    defaultValue?: string;
  }>;
  /** Return type */
  returnType: string;
  /** Is async */
  isAsync: boolean;
  /** Is static */
  isStatic?: boolean;
  /** Class name (if method) */
  className?: string;
  /** JSDoc description */
  description?: string;
  /** Source code */
  sourceCode?: string;
}

/**
 * Generated test result
 */
export interface GeneratedTestResult {
  /** Test file content */
  content: string;
  /** Test file path */
  filePath: string;
  /** Number of test cases */
  testCount: number;
  /** Coverage estimate */
  coverageEstimate: {
    statements: number;
    branches: number;
    functions: number;
    lines: number;
  };
  /** Warnings */
  warnings: string[];
}

/**
 * Test generator configuration
 */
export interface UnitTestGeneratorConfig {
  /** Test framework */
  framework: TestFramework;
  /** Assertion style */
  assertionStyle: AssertionStyle;
  /** Generate edge cases */
  generateEdgeCases: boolean;
  /** Generate error cases */
  generateErrorCases: boolean;
  /** Generate null/undefined cases */
  generateNullCases: boolean;
  /** Maximum test cases per function */
  maxTestCasesPerFunction: number;
  /** Include setup/teardown */
  includeSetupTeardown: boolean;
  /** Generate mocks */
  generateMocks: boolean;
  /** Test file suffix */
  testFileSuffix: string;
  /** Test directory */
  testDirectory: string;
  /** Verbose descriptions */
  verboseDescriptions: boolean;
}

/**
 * Default configuration
 */
export const DEFAULT_TEST_GENERATOR_CONFIG: UnitTestGeneratorConfig = {
  framework: 'jest',
  assertionStyle: 'expect',
  generateEdgeCases: true,
  generateErrorCases: true,
  generateNullCases: true,
  maxTestCasesPerFunction: 10,
  includeSetupTeardown: true,
  generateMocks: true,
  testFileSuffix: '.test',
  testDirectory: '__tests__',
  verboseDescriptions: true,
};

/**
 * Framework templates
 */
const FRAMEWORK_TEMPLATES: Record<TestFramework, {
  imports: string;
  describe: (name: string, body: string) => string;
  it: (name: string, body: string, isAsync: boolean) => string;
  beforeAll: (body: string) => string;
  afterAll: (body: string) => string;
  beforeEach: (body: string) => string;
  afterEach: (body: string) => string;
  expect: (value: string) => string;
  mockFn: () => string;
  mockModule: (module: string) => string;
}> = {
  jest: {
    imports: '',
    describe: (name, body) => `describe('${name}', () => {\n${body}\n});`,
    it: (name, body, isAsync) => `  it('${name}', ${isAsync ? 'async ' : ''}() => {\n${body}\n  });`,
    beforeAll: (body) => `  beforeAll(() => {\n${body}\n  });`,
    afterAll: (body) => `  afterAll(() => {\n${body}\n  });`,
    beforeEach: (body) => `  beforeEach(() => {\n${body}\n  });`,
    afterEach: (body) => `  afterEach(() => {\n${body}\n  });`,
    expect: (value) => `expect(${value})`,
    mockFn: () => 'jest.fn()',
    mockModule: (module) => `jest.mock('${module}')`,
  },
  vitest: {
    imports: "import { describe, it, expect, beforeAll, afterAll, beforeEach, afterEach, vi } from 'vitest';",
    describe: (name, body) => `describe('${name}', () => {\n${body}\n});`,
    it: (name, body, isAsync) => `  it('${name}', ${isAsync ? 'async ' : ''}() => {\n${body}\n  });`,
    beforeAll: (body) => `  beforeAll(() => {\n${body}\n  });`,
    afterAll: (body) => `  afterAll(() => {\n${body}\n  });`,
    beforeEach: (body) => `  beforeEach(() => {\n${body}\n  });`,
    afterEach: (body) => `  afterEach(() => {\n${body}\n  });`,
    expect: (value) => `expect(${value})`,
    mockFn: () => 'vi.fn()',
    mockModule: (module) => `vi.mock('${module}')`,
  },
  mocha: {
    imports: "import { expect } from 'chai';",
    describe: (name, body) => `describe('${name}', () => {\n${body}\n});`,
    it: (name, body, isAsync) => `  it('${name}', ${isAsync ? 'async ' : ''}() => {\n${body}\n  });`,
    beforeAll: (body) => `  before(() => {\n${body}\n  });`,
    afterAll: (body) => `  after(() => {\n${body}\n  });`,
    beforeEach: (body) => `  beforeEach(() => {\n${body}\n  });`,
    afterEach: (body) => `  afterEach(() => {\n${body}\n  });`,
    expect: (value) => `expect(${value})`,
    mockFn: () => "sinon.stub()",
    mockModule: (module) => `// Mock ${module} with sinon or proxyquire`,
  },
  ava: {
    imports: "import test from 'ava';",
    describe: (name, body) => `// ${name}\n${body}`,
    it: (name, body, isAsync) => `test('${name}', ${isAsync ? 'async ' : ''}(t) => {\n${body.replace(/expect\(/g, 't.is(')}\n});`,
    beforeAll: (body) => `test.before(() => {\n${body}\n});`,
    afterAll: (body) => `test.after(() => {\n${body}\n});`,
    beforeEach: (body) => `test.beforeEach(() => {\n${body}\n});`,
    afterEach: (body) => `test.afterEach(() => {\n${body}\n});`,
    expect: (value) => `t.is(${value}`,
    mockFn: () => "sinon.stub()",
    mockModule: (module) => `// Mock ${module} with proxyquire`,
  },
  tap: {
    imports: "import tap from 'tap';",
    describe: (name, body) => `tap.test('${name}', (t) => {\n${body}\n  t.end();\n});`,
    it: (name, body, isAsync) => `  t.test('${name}', ${isAsync ? 'async ' : ''}(t) => {\n${body}\n    t.end();\n  });`,
    beforeAll: (body) => `  t.before(() => {\n${body}\n  });`,
    afterAll: (body) => `  t.after(() => {\n${body}\n  });`,
    beforeEach: (body) => `  t.beforeEach(() => {\n${body}\n  });`,
    afterEach: (body) => `  t.afterEach(() => {\n${body}\n  });`,
    expect: (value) => `t.equal(${value}`,
    mockFn: () => "sinon.stub()",
    mockModule: (module) => `// Mock ${module}`,
  },
  pytest: {
    imports: 'import pytest\nfrom unittest.mock import Mock, patch',
    describe: (name, body) => `class Test${name.replace(/\s+/g, '')}:\n${body}`,
    it: (name, body, isAsync) => `    ${isAsync ? 'async ' : ''}def test_${name.replace(/\s+/g, '_').toLowerCase()}(self):\n${body}`,
    beforeAll: (body) => `    @classmethod\n    def setup_class(cls):\n${body}`,
    afterAll: (body) => `    @classmethod\n    def teardown_class(cls):\n${body}`,
    beforeEach: (body) => `    def setup_method(self):\n${body}`,
    afterEach: (body) => `    def teardown_method(self):\n${body}`,
    expect: (value) => `assert ${value}`,
    mockFn: () => 'Mock()',
    mockModule: (module) => `@patch('${module}')`,
  },
  unittest: {
    imports: 'import unittest\nfrom unittest.mock import Mock, patch',
    describe: (name, body) => `class Test${name.replace(/\s+/g, '')}(unittest.TestCase):\n${body}`,
    it: (name, body, _isAsync) => `    def test_${name.replace(/\s+/g, '_').toLowerCase()}(self):\n${body}`,
    beforeAll: (body) => `    @classmethod\n    def setUpClass(cls):\n${body}`,
    afterAll: (body) => `    @classmethod\n    def tearDownClass(cls):\n${body}`,
    beforeEach: (body) => `    def setUp(self):\n${body}`,
    afterEach: (body) => `    def tearDown(self):\n${body}`,
    expect: (value) => `self.assertEqual(${value}`,
    mockFn: () => 'Mock()',
    mockModule: (module) => `@patch('${module}')`,
  },
  junit: {
    imports: 'import org.junit.jupiter.api.*;\nimport static org.junit.jupiter.api.Assertions.*;',
    describe: (name, body) => `class ${name.replace(/\s+/g, '')}Test {\n${body}\n}`,
    it: (name, body, _isAsync) => `    @Test\n    void test${name.replace(/\s+/g, '')}() {\n${body}\n    }`,
    beforeAll: (body) => `    @BeforeAll\n    static void setUpAll() {\n${body}\n    }`,
    afterAll: (body) => `    @AfterAll\n    static void tearDownAll() {\n${body}\n    }`,
    beforeEach: (body) => `    @BeforeEach\n    void setUp() {\n${body}\n    }`,
    afterEach: (body) => `    @AfterEach\n    void tearDown() {\n${body}\n    }`,
    expect: (value) => `assertEquals(${value}`,
    mockFn: () => 'mock()',
    mockModule: (module) => `// Mock ${module} with Mockito`,
  },
  nunit: {
    imports: 'using NUnit.Framework;\nusing Moq;',
    describe: (name, body) => `[TestFixture]\npublic class ${name.replace(/\s+/g, '')}Tests\n{\n${body}\n}`,
    it: (name, body, _isAsync) => `    [Test]\n    public void Test${name.replace(/\s+/g, '')}()\n    {\n${body}\n    }`,
    beforeAll: (body) => `    [OneTimeSetUp]\n    public void SetUpFixture()\n    {\n${body}\n    }`,
    afterAll: (body) => `    [OneTimeTearDown]\n    public void TearDownFixture()\n    {\n${body}\n    }`,
    beforeEach: (body) => `    [SetUp]\n    public void SetUp()\n    {\n${body}\n    }`,
    afterEach: (body) => `    [TearDown]\n    public void TearDown()\n    {\n${body}\n    }`,
    expect: (value) => `Assert.That(${value}`,
    mockFn: () => 'new Mock<T>()',
    mockModule: (module) => `// Mock ${module} with Moq`,
  },
  xunit: {
    imports: 'using Xunit;\nusing Moq;',
    describe: (name, body) => `public class ${name.replace(/\s+/g, '')}Tests\n{\n${body}\n}`,
    it: (name, body, _isAsync) => `    [Fact]\n    public void Test${name.replace(/\s+/g, '')}()\n    {\n${body}\n    }`,
    beforeAll: (body) => `    public XunitTests()\n    {\n${body}\n    }`,
    afterAll: (body) => `    public void Dispose()\n    {\n${body}\n    }`,
    beforeEach: (body) => `    // Setup: ${body}`,
    afterEach: (body) => `    // Teardown: ${body}`,
    expect: (value) => `Assert.Equal(${value}`,
    mockFn: () => 'new Mock<T>()',
    mockModule: (module) => `// Mock ${module} with Moq`,
  },
  'go-test': {
    imports: 'import (\n    "testing"\n)',
    describe: (name, body) => `// ${name}\n${body}`,
    it: (name, body, _isAsync) => `func Test${name.replace(/\s+/g, '')}(t *testing.T) {\n${body}\n}`,
    beforeAll: (body) => `func TestMain(m *testing.M) {\n${body}\n    os.Exit(m.Run())\n}`,
    afterAll: (body) => `// Teardown in TestMain: ${body}`,
    beforeEach: (body) => `    // Setup: ${body}`,
    afterEach: (body) => `    // Teardown: ${body}`,
    expect: (value) => `if ${value}`,
    mockFn: () => '// mock function',
    mockModule: (module) => `// Mock ${module}`,
  },
};

/**
 * Unit Test Generator
 */
export class UnitTestGenerator {
  private config: UnitTestGeneratorConfig;
  private template: typeof FRAMEWORK_TEMPLATES[TestFramework];

  constructor(config?: Partial<UnitTestGeneratorConfig>) {
    this.config = { ...DEFAULT_TEST_GENERATOR_CONFIG, ...config };
    this.template = FRAMEWORK_TEMPLATES[this.config.framework];
  }

  /**
   * Generate tests for a function
   */
  generateForFunction(func: FunctionToTest, targetFile: string): GeneratedTestResult {
    const testCases = this.generateTestCases(func);
    const content = this.generateTestFile(func, testCases, targetFile);
    
    const testFilePath = this.getTestFilePath(targetFile);
    const coverageEstimate = this.estimateCoverage(func, testCases);

    return {
      content,
      filePath: testFilePath,
      testCount: testCases.length,
      coverageEstimate,
      warnings: this.generateWarnings(func, testCases),
    };
  }

  /**
   * Generate tests for multiple functions
   */
  generateForModule(
    functions: FunctionToTest[],
    targetFile: string
  ): GeneratedTestResult {
    const allTestCases: TestCaseInfo[] = [];
    const warnings: string[] = [];

    for (const func of functions) {
      const testCases = this.generateTestCases(func);
      allTestCases.push(...testCases);
      warnings.push(...this.generateWarnings(func, testCases));
    }

    const content = this.generateModuleTestFile(functions, allTestCases, targetFile);
    const testFilePath = this.getTestFilePath(targetFile);

    return {
      content,
      filePath: testFilePath,
      testCount: allTestCases.length,
      coverageEstimate: this.estimateModuleCoverage(functions, allTestCases),
      warnings,
    };
  }

  /**
   * Generate test cases for a function
   */
  private generateTestCases(func: FunctionToTest): TestCaseInfo[] {
    const testCases: TestCaseInfo[] = [];

    // Basic happy path test
    testCases.push(this.generateHappyPathTest(func));

    // Edge cases
    if (this.config.generateEdgeCases) {
      testCases.push(...this.generateEdgeCaseTests(func));
    }

    // Error cases
    if (this.config.generateErrorCases) {
      testCases.push(...this.generateErrorTests(func));
    }

    // Null/undefined cases
    if (this.config.generateNullCases) {
      testCases.push(...this.generateNullTests(func));
    }

    // Limit test cases
    return testCases.slice(0, this.config.maxTestCasesPerFunction);
  }

  /**
   * Generate happy path test
   */
  private generateHappyPathTest(func: FunctionToTest): TestCaseInfo {
    return {
      name: `should ${this.generateTestName(func)} with valid input`,
      description: `Tests ${func.name} with typical valid input`,
      type: 'unit',
      inputs: func.parameters.map((p) => ({
        name: p.name,
        value: this.generateSampleValue(p.type),
        type: p.type,
      })),
      expectedOutput: {
        type: func.returnType,
        value: this.generateExpectedValue(func.returnType),
      },
    };
  }

  /**
   * Generate edge case tests
   */
  private generateEdgeCaseTests(func: FunctionToTest): TestCaseInfo[] {
    const tests: TestCaseInfo[] = [];

    for (const param of func.parameters) {
      const edgeValues = this.getEdgeValues(param.type);
      
      for (const edge of edgeValues) {
        tests.push({
          name: `should handle ${param.name} with ${edge.description}`,
          description: `Edge case test for ${param.name}`,
          type: 'edge',
          inputs: func.parameters.map((p) => ({
            name: p.name,
            value: p.name === param.name ? edge.value : this.generateSampleValue(p.type),
            type: p.type,
          })),
          expectedOutput: {
            type: func.returnType,
          },
          tags: ['edge-case'],
        });
      }
    }

    return tests;
  }

  /**
   * Generate error tests
   */
  private generateErrorTests(func: FunctionToTest): TestCaseInfo[] {
    const tests: TestCaseInfo[] = [];

    // Invalid type tests
    for (const param of func.parameters) {
      if (!param.optional) {
        tests.push({
          name: `should throw error when ${param.name} is invalid`,
          description: `Error handling test for invalid ${param.name}`,
          type: 'error',
          inputs: func.parameters.map((p) => ({
            name: p.name,
            value: p.name === param.name ? this.generateInvalidValue(p.type) : this.generateSampleValue(p.type),
            type: p.type,
          })),
          expectedOutput: {
            error: {
              type: 'Error',
              message: `Invalid ${param.name}`,
            },
          },
          tags: ['error-handling'],
        });
      }
    }

    return tests;
  }

  /**
   * Generate null/undefined tests
   */
  private generateNullTests(func: FunctionToTest): TestCaseInfo[] {
    const tests: TestCaseInfo[] = [];

    for (const param of func.parameters) {
      if (!param.optional) {
        // Null test
        tests.push({
          name: `should handle null ${param.name}`,
          description: `Null handling test for ${param.name}`,
          type: 'null',
          inputs: func.parameters.map((p) => ({
            name: p.name,
            value: p.name === param.name ? null : this.generateSampleValue(p.type),
            type: p.type,
          })),
          expectedOutput: {
            error: {
              type: 'TypeError',
            },
          },
          tags: ['null-check'],
        });

        // Undefined test
        tests.push({
          name: `should handle undefined ${param.name}`,
          description: `Undefined handling test for ${param.name}`,
          type: 'null',
          inputs: func.parameters.map((p) => ({
            name: p.name,
            value: p.name === param.name ? undefined : this.generateSampleValue(p.type),
            type: p.type,
          })),
          expectedOutput: {
            error: {
              type: 'TypeError',
            },
          },
          tags: ['undefined-check'],
        });
      }
    }

    return tests;
  }

  /**
   * Generate test file content
   */
  private generateTestFile(
    func: FunctionToTest,
    testCases: TestCaseInfo[],
    targetFile: string
  ): string {
    const lines: string[] = [];
    
    // Framework imports
    if (this.template.imports) {
      lines.push(this.template.imports);
    }

    // Import target
    const importPath = this.getImportPath(targetFile);
    lines.push(`import { ${func.name} } from '${importPath}';`);
    lines.push('');

    // Generate describe block
    const testBody = this.generateDescribeBody(func, testCases);
    lines.push(this.template.describe(func.name, testBody));

    return lines.join('\n');
  }

  /**
   * Generate module test file
   */
  private generateModuleTestFile(
    functions: FunctionToTest[],
    testCases: TestCaseInfo[],
    targetFile: string
  ): string {
    const lines: string[] = [];

    // Framework imports
    if (this.template.imports) {
      lines.push(this.template.imports);
    }

    // Import targets
    const importPath = this.getImportPath(targetFile);
    const imports = functions.map((f) => f.name).join(', ');
    lines.push(`import { ${imports} } from '${importPath}';`);
    lines.push('');

    // Generate describe blocks for each function
    for (const func of functions) {
      const funcTests = testCases.filter((t) => 
        t.name.includes(func.name) || t.description.includes(func.name)
      );
      const testBody = this.generateDescribeBody(func, funcTests);
      lines.push(this.template.describe(func.name, testBody));
      lines.push('');
    }

    return lines.join('\n');
  }

  /**
   * Generate describe block body
   */
  private generateDescribeBody(func: FunctionToTest, testCases: TestCaseInfo[]): string {
    const lines: string[] = [];

    // Setup/teardown
    if (this.config.includeSetupTeardown) {
      lines.push(this.template.beforeEach('    // Setup'));
      lines.push('');
    }

    // Test cases
    for (const testCase of testCases) {
      const testBody = this.generateTestBody(func, testCase);
      lines.push(this.template.it(testCase.name, testBody, func.isAsync));
      lines.push('');
    }

    return lines.join('\n');
  }

  /**
   * Generate test body
   */
  private generateTestBody(func: FunctionToTest, testCase: TestCaseInfo): string {
    const lines: string[] = [];
    const indent = '    ';

    // Setup mocks
    if (testCase.mocks) {
      for (const mock of testCase.mocks) {
        lines.push(`${indent}const ${mock.target}Mock = ${this.template.mockFn()};`);
      }
    }

    // Arrange: prepare inputs
    const inputVars: string[] = [];
    for (const input of testCase.inputs) {
      const varName = input.name;
      const value = JSON.stringify(input.value);
      lines.push(`${indent}const ${varName} = ${value};`);
      inputVars.push(varName);
    }
    lines.push('');

    // Act: call function
    const funcCall = func.className
      ? `new ${func.className}().${func.name}(${inputVars.join(', ')})`
      : `${func.name}(${inputVars.join(', ')})`;

    if (testCase.expectedOutput.error) {
      // Expect error
      if (func.isAsync) {
        lines.push(`${indent}await ${this.template.expect(`${funcCall}`)}.rejects.toThrow();`);
      } else {
        lines.push(`${indent}${this.template.expect(`() => ${funcCall}`)}.toThrow();`);
      }
    } else {
      // Expect result
      const resultVar = func.isAsync
        ? `await ${funcCall}`
        : funcCall;
      lines.push(`${indent}const result = ${resultVar};`);
      lines.push('');

      // Assert
      if (testCase.expectedOutput.value !== undefined) {
        const expected = JSON.stringify(testCase.expectedOutput.value);
        lines.push(`${indent}${this.template.expect('result')}.toEqual(${expected});`);
      } else {
        lines.push(`${indent}${this.template.expect('result')}.toBeDefined();`);
      }
    }

    return lines.join('\n');
  }

  /**
   * Generate test name from function
   */
  private generateTestName(func: FunctionToTest): string {
    // Convert camelCase to words
    const words = func.name
      .replace(/([A-Z])/g, ' $1')
      .toLowerCase()
      .trim();
    return words;
  }

  /**
   * Generate sample value for type
   */
  private generateSampleValue(type: string): unknown {
    const normalized = type.toLowerCase().replace(/\s+/g, '');
    
    if (normalized.includes('string')) return 'test';
    if (normalized.includes('number') || normalized.includes('int') || normalized.includes('float')) return 42;
    if (normalized.includes('boolean') || normalized.includes('bool')) return true;
    if (normalized.includes('array') || normalized.includes('[]')) return [];
    if (normalized.includes('object') || normalized.includes('record')) return {};
    if (normalized.includes('date')) return new Date().toISOString();
    if (normalized.includes('null')) return null;
    if (normalized.includes('undefined')) return undefined;
    
    return {};
  }

  /**
   * Generate expected value for return type
   */
  private generateExpectedValue(type: string): unknown {
    const normalized = type.toLowerCase().replace(/\s+/g, '');
    
    if (normalized === 'void' || normalized === 'undefined') return undefined;
    if (normalized.includes('promise')) {
      const inner = type.match(/<(.+)>/)?.[1] ?? 'unknown';
      return this.generateSampleValue(inner);
    }
    
    return this.generateSampleValue(type);
  }

  /**
   * Generate invalid value for type
   */
  private generateInvalidValue(type: string): unknown {
    const normalized = type.toLowerCase().replace(/\s+/g, '');
    
    if (normalized.includes('string')) return 123;
    if (normalized.includes('number')) return 'not a number';
    if (normalized.includes('boolean')) return 'not boolean';
    if (normalized.includes('array')) return 'not array';
    if (normalized.includes('object')) return 'not object';
    
    return Symbol('invalid');
  }

  /**
   * Get edge values for type
   */
  private getEdgeValues(type: string): Array<{ value: unknown; description: string }> {
    const normalized = type.toLowerCase().replace(/\s+/g, '');
    const edges: Array<{ value: unknown; description: string }> = [];

    if (normalized.includes('string')) {
      edges.push({ value: '', description: 'empty string' });
      edges.push({ value: ' ', description: 'whitespace' });
      edges.push({ value: 'a'.repeat(1000), description: 'very long string' });
    }

    if (normalized.includes('number')) {
      edges.push({ value: 0, description: 'zero' });
      edges.push({ value: -1, description: 'negative' });
      edges.push({ value: Number.MAX_SAFE_INTEGER, description: 'max safe integer' });
      edges.push({ value: Number.MIN_SAFE_INTEGER, description: 'min safe integer' });
      edges.push({ value: Infinity, description: 'infinity' });
      edges.push({ value: NaN, description: 'NaN' });
    }

    if (normalized.includes('array')) {
      edges.push({ value: [], description: 'empty array' });
      edges.push({ value: new Array(1000).fill(0), description: 'large array' });
    }

    return edges;
  }

  /**
   * Get test file path
   */
  private getTestFilePath(targetFile: string): string {
    const parts = targetFile.split('/');
    const filename = parts.pop()!;
    const ext = filename.split('.').pop();
    const baseName = filename.replace(`.${ext}`, '');
    
    return [...parts, this.config.testDirectory, `${baseName}${this.config.testFileSuffix}.${ext}`].join('/');
  }

  /**
   * Get import path
   */
  private getImportPath(targetFile: string): string {
    // Convert absolute to relative import
    const parts = targetFile.split('/');
    const filename = parts.pop()!;
    const ext = filename.split('.').pop();
    const baseName = filename.replace(`.${ext}`, '');
    
    return `../${baseName}`;
  }

  /**
   * Estimate coverage
   */
  private estimateCoverage(
    _func: FunctionToTest,
    testCases: TestCaseInfo[]
  ): GeneratedTestResult['coverageEstimate'] {
    const hasHappyPath = testCases.some((t) => t.type === 'unit');
    const hasEdgeCases = testCases.some((t) => t.type === 'edge');
    const hasErrorCases = testCases.some((t) => t.type === 'error');
    const hasNullCases = testCases.some((t) => t.type === 'null');

    let base = hasHappyPath ? 50 : 0;
    if (hasEdgeCases) base += 15;
    if (hasErrorCases) base += 20;
    if (hasNullCases) base += 15;

    return {
      statements: Math.min(base + 10, 100),
      branches: Math.min(base, 100),
      functions: hasHappyPath ? 100 : 0,
      lines: Math.min(base + 10, 100),
    };
  }

  /**
   * Estimate module coverage
   */
  private estimateModuleCoverage(
    functions: FunctionToTest[],
    testCases: TestCaseInfo[]
  ): GeneratedTestResult['coverageEstimate'] {
    const functionsCovered = functions.filter((f) =>
      testCases.some((t) => t.name.includes(f.name) || t.description.includes(f.name))
    ).length;

    const functionCoverage = functions.length > 0
      ? (functionsCovered / functions.length) * 100
      : 0;

    return {
      statements: Math.round(functionCoverage * 0.9),
      branches: Math.round(functionCoverage * 0.7),
      functions: Math.round(functionCoverage),
      lines: Math.round(functionCoverage * 0.9),
    };
  }

  /**
   * Generate warnings
   */
  private generateWarnings(func: FunctionToTest, testCases: TestCaseInfo[]): string[] {
    const warnings: string[] = [];

    if (testCases.length < 3) {
      warnings.push(`Low test count for ${func.name}: consider adding more test cases`);
    }

    if (func.parameters.length > 5) {
      warnings.push(`${func.name} has many parameters: consider refactoring`);
    }

    if (!testCases.some((t) => t.type === 'error')) {
      warnings.push(`No error handling tests for ${func.name}`);
    }

    return warnings;
  }
}

/**
 * Create unit test generator instance
 */
export function createUnitTestGenerator(
  config?: Partial<UnitTestGeneratorConfig>
): UnitTestGenerator {
  return new UnitTestGenerator(config);
}

/**
 * EARS Requirement structure for test generation
 */
export interface EarsRequirement {
  id: string;
  type: 'ubiquitous' | 'event-driven' | 'state-driven' | 'unwanted' | 'optional';
  text: string;
  system?: string;
  event?: string;
  state?: string;
  condition?: string;
  response?: string;
}

/**
 * Test case generated from EARS requirement
 */
export interface EarsTestCase {
  requirementId: string;
  testName: string;
  testDescription: string;
  testType: 'positive' | 'negative' | 'boundary';
  setup?: string;
  action: string;
  assertion: string;
}

/**
 * EARS Test Generator - Generate tests from EARS requirements (BP-TEST-004, BP-TEST-005)
 * 
 * This class implements learning patterns:
 * - BP-TEST-004: Result Type Test Pattern - test both isOk() and isErr() cases
 * - BP-TEST-005: Status Transition Testing - test valid/invalid transitions
 * - BP-TEST-001: Test Counter Reset - reset counters in beforeEach
 */
export class EarsTestGenerator {
  private config: UnitTestGeneratorConfig;

  constructor(config?: Partial<UnitTestGeneratorConfig>) {
    this.config = { ...DEFAULT_TEST_GENERATOR_CONFIG, ...config };
  }

  /**
   * Generate test cases from EARS requirements
   */
  generateFromRequirements(requirements: EarsRequirement[]): EarsTestCase[] {
    const testCases: EarsTestCase[] = [];

    for (const req of requirements) {
      testCases.push(...this.generateTestsForRequirement(req));
    }

    return testCases;
  }

  /**
   * Generate tests for a single EARS requirement
   */
  private generateTestsForRequirement(req: EarsRequirement): EarsTestCase[] {
    switch (req.type) {
      case 'ubiquitous':
        return this.generateUbiquitousTests(req);
      case 'event-driven':
        return this.generateEventDrivenTests(req);
      case 'state-driven':
        return this.generateStateDrivenTests(req);
      case 'unwanted':
        return this.generateUnwantedTests(req);
      case 'optional':
        return this.generateOptionalTests(req);
      default:
        return [];
    }
  }

  /**
   * Generate tests for UBIQUITOUS requirements (THE system SHALL)
   */
  private generateUbiquitousTests(req: EarsRequirement): EarsTestCase[] {
    const tests: EarsTestCase[] = [];
    const actionName = this.extractActionName(req.response || req.text);

    // Positive test - should always work
    tests.push({
      requirementId: req.id,
      testName: `should ${actionName}`,
      testDescription: `Verify: ${req.text}`,
      testType: 'positive',
      action: `// Act: ${actionName}`,
      assertion: `// Assert: Verify the system ${actionName}`,
    });

    // Boundary test with Result type pattern (BP-TEST-004)
    tests.push({
      requirementId: req.id,
      testName: `should return Result.ok when ${actionName} succeeds`,
      testDescription: `Result type positive case for ${req.id}`,
      testType: 'positive',
      action: `const result = ${this.toFunctionCall(actionName)}(validInput);`,
      assertion: `expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value).toBeDefined();
    }`,
    });

    return tests;
  }

  /**
   * Generate tests for EVENT-DRIVEN requirements (WHEN event, THE system SHALL)
   */
  private generateEventDrivenTests(req: EarsRequirement): EarsTestCase[] {
    const tests: EarsTestCase[] = [];
    const eventName = req.event || this.extractEventName(req.text);
    const actionName = this.extractActionName(req.response || req.text);

    // Positive test - event triggers response
    tests.push({
      requirementId: req.id,
      testName: `should ${actionName} when ${eventName}`,
      testDescription: `Event-driven test: ${req.text}`,
      testType: 'positive',
      setup: `// Arrange: Set up conditions for ${eventName}`,
      action: `// Act: Trigger ${eventName}`,
      assertion: `// Assert: Verify ${actionName}`,
    });

    // Negative test - no event, no response
    tests.push({
      requirementId: req.id,
      testName: `should not ${actionName} when ${eventName} has not occurred`,
      testDescription: `Negative case: Event not triggered`,
      testType: 'negative',
      action: `// Act: Do not trigger ${eventName}`,
      assertion: `// Assert: Verify ${actionName} did not happen`,
    });

    return tests;
  }

  /**
   * Generate tests for STATE-DRIVEN requirements (WHILE state, THE system SHALL)
   */
  private generateStateDrivenTests(req: EarsRequirement): EarsTestCase[] {
    const tests: EarsTestCase[] = [];
    const stateName = req.state || this.extractStateName(req.text);
    const actionName = this.extractActionName(req.response || req.text);

    // Positive test - in state, behavior applies
    tests.push({
      requirementId: req.id,
      testName: `should ${actionName} while in ${stateName} state`,
      testDescription: `State-driven test: ${req.text}`,
      testType: 'positive',
      setup: `// Arrange: Set system to ${stateName} state`,
      action: `// Act: Perform action`,
      assertion: `// Assert: Verify ${actionName}`,
    });

    // Negative test - not in state, behavior doesn't apply
    tests.push({
      requirementId: req.id,
      testName: `should not ${actionName} when not in ${stateName} state`,
      testDescription: `Negative case: Wrong state`,
      testType: 'negative',
      setup: `// Arrange: Ensure system is NOT in ${stateName} state`,
      action: `// Act: Attempt action`,
      assertion: `// Assert: Verify ${actionName} is not applied`,
    });

    // Status Transition Testing (BP-TEST-005)
    tests.push({
      requirementId: req.id,
      testName: `should validate status transitions for ${stateName}`,
      testDescription: `Status transition test (BP-TEST-005)`,
      testType: 'boundary',
      setup: `// Arrange: Get valid transitions from status map`,
      action: `const validTransitions = validStatusTransitions['${stateName}'];`,
      assertion: `// Assert: Each valid transition should succeed
    for (const nextStatus of validTransitions) {
      const result = transitionTo(entity, nextStatus);
      expect(result.isOk()).toBe(true);
    }`,
    });

    return tests;
  }

  /**
   * Generate tests for UNWANTED requirements (THE system SHALL NOT)
   */
  private generateUnwantedTests(req: EarsRequirement): EarsTestCase[] {
    const tests: EarsTestCase[] = [];
    const unwantedBehavior = this.extractUnwantedBehavior(req.text);

    // Test that unwanted behavior doesn't occur
    tests.push({
      requirementId: req.id,
      testName: `should not ${unwantedBehavior}`,
      testDescription: `Unwanted behavior test: ${req.text}`,
      testType: 'negative',
      action: `// Act: Attempt to trigger unwanted behavior`,
      assertion: `// Assert: Verify ${unwantedBehavior} does not occur`,
    });

    // Result type error case (BP-TEST-004)
    tests.push({
      requirementId: req.id,
      testName: `should return Result.err when attempting ${unwantedBehavior}`,
      testDescription: `Result type error case for ${req.id}`,
      testType: 'negative',
      action: `const result = ${this.toFunctionCall(unwantedBehavior)}(invalidInput);`,
      assertion: `expect(result.isErr()).toBe(true);
    if (result.isErr()) {
      expect(result.error).toBeInstanceOf(ValidationError);
    }`,
    });

    return tests;
  }

  /**
   * Generate tests for OPTIONAL requirements (IF condition, THEN THE system SHALL)
   */
  private generateOptionalTests(req: EarsRequirement): EarsTestCase[] {
    const tests: EarsTestCase[] = [];
    const condition = req.condition || this.extractCondition(req.text);
    const actionName = this.extractActionName(req.response || req.text);

    // Positive test - condition met
    tests.push({
      requirementId: req.id,
      testName: `should ${actionName} when ${condition}`,
      testDescription: `Optional requirement positive: ${req.text}`,
      testType: 'positive',
      setup: `// Arrange: Set up ${condition}`,
      action: `// Act: Trigger action`,
      assertion: `// Assert: Verify ${actionName}`,
    });

    // Negative test - condition not met
    tests.push({
      requirementId: req.id,
      testName: `should not ${actionName} when ${condition} is not met`,
      testDescription: `Optional requirement negative: Condition not satisfied`,
      testType: 'negative',
      setup: `// Arrange: Ensure ${condition} is NOT met`,
      action: `// Act: Attempt action`,
      assertion: `// Assert: Verify ${actionName} does not happen`,
    });

    return tests;
  }

  /**
   * Generate test file content from EARS test cases
   */
  generateTestFileContent(
    testCases: EarsTestCase[],
    moduleName: string
  ): string {
    const lines: string[] = [];
    const framework = this.config.framework;

    // Imports
    if (framework === 'vitest') {
      lines.push("import { describe, it, expect, beforeEach } from 'vitest';");
    }
    lines.push(`import { /* imports from ${moduleName} */ } from './${moduleName}';`);
    lines.push('');

    // Group by requirement
    const byRequirement = new Map<string, EarsTestCase[]>();
    for (const tc of testCases) {
      const cases = byRequirement.get(tc.requirementId) || [];
      cases.push(tc);
      byRequirement.set(tc.requirementId, cases);
    }

    // Generate describe blocks
    lines.push(`describe('${moduleName}', () => {`);
    
    // Counter reset (BP-TEST-001)
    lines.push('  // BP-TEST-001: Reset counters before each test');
    lines.push('  beforeEach(() => {');
    lines.push('    // resetEntityCounter();');
    lines.push('  });');
    lines.push('');

    for (const [reqId, cases] of byRequirement) {
      lines.push(`  describe('${reqId}', () => {`);
      for (const tc of cases) {
        lines.push(`    it('${tc.testName}', () => {`);
        lines.push(`      // ${tc.testDescription}`);
        if (tc.setup) {
          lines.push(`      ${tc.setup}`);
        }
        lines.push(`      ${tc.action}`);
        lines.push(`      ${tc.assertion}`);
        lines.push('    });');
        lines.push('');
      }
      lines.push('  });');
      lines.push('');
    }

    lines.push('});');

    return lines.join('\n');
  }

  // Helper methods
  private extractActionName(text: string): string {
    const match = text.match(/SHALL\s+(.+?)(?:\.|$)/i);
    return match ? match[1].trim().toLowerCase() : 'perform the action';
  }

  private extractEventName(text: string): string {
    const match = text.match(/WHEN\s+(.+?),/i);
    return match ? match[1].trim() : 'the event occurs';
  }

  private extractStateName(text: string): string {
    const match = text.match(/WHILE\s+(.+?),/i);
    return match ? match[1].trim() : 'in the state';
  }

  private extractUnwantedBehavior(text: string): string {
    const match = text.match(/SHALL\s+NOT\s+(.+?)(?:\.|$)/i);
    return match ? match[1].trim().toLowerCase() : 'perform unwanted action';
  }

  private extractCondition(text: string): string {
    const match = text.match(/IF\s+(.+?),?\s+THEN/i);
    return match ? match[1].trim() : 'the condition is met';
  }

  private toFunctionCall(action: string): string {
    return action
      .split(' ')
      .map((word, i) => i === 0 ? word.toLowerCase() : word.charAt(0).toUpperCase() + word.slice(1).toLowerCase())
      .join('')
      .replace(/[^a-zA-Z0-9]/g, '');
  }
}

/**
 * Create EARS test generator instance
 */
export function createEarsTestGenerator(
  config?: Partial<UnitTestGeneratorConfig>
): EarsTestGenerator {
  return new EarsTestGenerator(config);
}
