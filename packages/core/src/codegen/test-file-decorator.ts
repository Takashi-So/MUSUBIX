/**
 * Test File Decorator
 *
 * Automatically inserts beforeEach with counter reset calls for test files.
 *
 * @packageDocumentation
 * @module codegen/test-file-decorator
 *
 * @see REQ-TST-002 - テストカウンターリセット自動挿入
 * @see TSK-TST-002 - カウンターリセット自動挿入タスク
 * @see BP-TEST-001 - Test Counter Reset Pattern
 */

/**
 * Counter reset function info
 */
export interface CounterResetFunction {
  /** Function name (e.g., 'resetOrderCounter') */
  name: string;
  /** Import path (e.g., './order') */
  importPath: string;
  /** Module name if named export */
  moduleName?: string;
}

/**
 * Test file decoration options
 */
export interface TestFileDecoratorOptions {
  /** Test framework (default: 'vitest') */
  framework?: 'vitest' | 'jest' | 'mocha';
  /** Whether to add import statements */
  addImports?: boolean;
  /** Custom beforeEach content to add */
  customBeforeEach?: string[];
}

/**
 * Decoration result
 */
export interface DecorationResult {
  /** Decorated source code */
  code: string;
  /** Counter reset functions added */
  countersAdded: CounterResetFunction[];
  /** Whether beforeEach was inserted */
  beforeEachInserted: boolean;
  /** Imports added */
  importsAdded: string[];
}

const DEFAULT_OPTIONS: Required<TestFileDecoratorOptions> = {
  framework: 'vitest',
  addImports: true,
  customBeforeEach: [],
};

/**
 * Test File Decorator
 *
 * Analyzes test files and automatically inserts beforeEach blocks
 * with counter reset calls to ensure test isolation.
 */
export class TestFileDecorator {
  private options: Required<TestFileDecoratorOptions>;

  constructor(options?: TestFileDecoratorOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Decorate a test file with beforeEach and counter resets
   *
   * @param sourceCode - Original test file source code
   * @param entityImports - List of entity imports that may have counters
   * @returns Decorated source code with beforeEach
   */
  decorate(
    sourceCode: string,
    entityImports: CounterResetFunction[] = []
  ): DecorationResult {
    const countersToAdd = this.detectCounterResets(sourceCode, entityImports);
    const hasBeforeEach = this.hasBeforeEach(sourceCode);

    if (countersToAdd.length === 0 && this.options.customBeforeEach.length === 0) {
      return {
        code: sourceCode,
        countersAdded: [],
        beforeEachInserted: false,
        importsAdded: [],
      };
    }

    let decoratedCode = sourceCode;
    const importsAdded: string[] = [];

    // Add imports for counter reset functions
    if (this.options.addImports) {
      const importStatements = this.generateImportStatements(countersToAdd);
      if (importStatements.length > 0) {
        decoratedCode = this.insertImports(decoratedCode, importStatements);
        importsAdded.push(...importStatements);
      }
    }

    // Add or update beforeEach
    if (hasBeforeEach) {
      decoratedCode = this.updateBeforeEach(decoratedCode, countersToAdd);
    } else {
      decoratedCode = this.insertBeforeEach(decoratedCode, countersToAdd);
    }

    return {
      code: decoratedCode,
      countersAdded: countersToAdd,
      beforeEachInserted: !hasBeforeEach,
      importsAdded,
    };
  }

  /**
   * Detect counter reset functions that should be called
   */
  detectCounterResets(
    sourceCode: string,
    entityImports: CounterResetFunction[]
  ): CounterResetFunction[] {
    const detected: CounterResetFunction[] = [];

    // Check for entity factory/creation patterns
    const entityPatterns = [
      /create(\w+)\(/g,           // createOrder(...)
      /new\s+(\w+)\(/g,           // new Order(...)
      /(\w+)\.create\(/g,         // Order.create(...)
      /generate(\w+)Id\(/g,       // generateOrderId()
    ];

    const entities = new Set<string>();

    for (const pattern of entityPatterns) {
      let match;
      while ((match = pattern.exec(sourceCode)) !== null) {
        entities.add(match[1]);
      }
    }

    // Match entities with their reset functions
    for (const entity of entities) {
      const resetFnName = `reset${entity}Counter`;
      
      // Check if reset function is already imported or referenced
      if (sourceCode.includes(resetFnName)) {
        continue; // Already has reset function
      }

      // Find matching import from provided entity imports
      const matchingImport = entityImports.find(
        (imp) => imp.name === resetFnName ||
                 imp.importPath.toLowerCase().includes(entity.toLowerCase())
      );

      if (matchingImport) {
        detected.push(matchingImport);
      } else if (this.hasEntityImport(sourceCode, entity)) {
        // Infer reset function from entity import
        detected.push({
          name: resetFnName,
          importPath: this.inferImportPath(sourceCode, entity),
        });
      }
    }

    return detected;
  }

  /**
   * Check if source has beforeEach block
   */
  hasBeforeEach(sourceCode: string): boolean {
    return /beforeEach\s*\(/.test(sourceCode);
  }

  /**
   * Check if entity is imported
   */
  private hasEntityImport(sourceCode: string, entity: string): boolean {
    const importPattern = new RegExp(
      `import\\s+.*?\\b${entity}\\b.*?from\\s+['"](.+?)['"]`,
      'i'
    );
    return importPattern.test(sourceCode);
  }

  /**
   * Infer import path from existing imports
   */
  private inferImportPath(sourceCode: string, entity: string): string {
    const importPattern = new RegExp(
      `import\\s+.*?\\b${entity}\\b.*?from\\s+['"](.+?)['"]`,
      'i'
    );
    const match = sourceCode.match(importPattern);
    return match?.[1] ?? `./${entity.toLowerCase()}`;
  }

  /**
   * Generate import statements for counter reset functions
   */
  private generateImportStatements(counters: CounterResetFunction[]): string[] {
    const importsByPath = new Map<string, string[]>();

    for (const counter of counters) {
      const existing = importsByPath.get(counter.importPath) ?? [];
      existing.push(counter.name);
      importsByPath.set(counter.importPath, existing);
    }

    return Array.from(importsByPath.entries()).map(([path, names]) => {
      return `import { ${names.join(', ')} } from '${path}';`;
    });
  }

  /**
   * Insert import statements at the top of the file
   */
  private insertImports(sourceCode: string, imports: string[]): string {
    // Find the last import statement
    const lines = sourceCode.split('\n');
    let lastImportIndex = -1;

    for (let i = 0; i < lines.length; i++) {
      if (lines[i].trim().startsWith('import ')) {
        lastImportIndex = i;
      } else if (lastImportIndex !== -1 && lines[i].trim() !== '') {
        // Found a non-empty line after imports
        break;
      }
    }

    if (lastImportIndex === -1) {
      // No imports found, add at the beginning
      return imports.join('\n') + '\n\n' + sourceCode;
    }

    // Insert after last import
    lines.splice(lastImportIndex + 1, 0, ...imports);
    return lines.join('\n');
  }

  /**
   * Insert beforeEach block into test file
   */
  private insertBeforeEach(
    sourceCode: string,
    counters: CounterResetFunction[]
  ): string {
    const beforeEachContent = this.generateBeforeEachContent(counters);

    // Find first describe block
    const describeMatch = sourceCode.match(/describe\s*\(\s*['"`]/);
    if (!describeMatch || describeMatch.index === undefined) {
      // No describe block, can't insert
      return sourceCode;
    }

    // Find the opening brace of the describe callback
    const afterDescribe = sourceCode.substring(describeMatch.index);
    const braceMatch = afterDescribe.match(/\)\s*=>\s*\{|\)\s*,\s*(?:async\s*)?\(\)\s*=>\s*\{|\)\s*,\s*function\s*\(\)\s*\{/);
    
    if (!braceMatch || braceMatch.index === undefined) {
      return sourceCode;
    }

    const insertPosition = describeMatch.index + braceMatch.index + braceMatch[0].length;

    return (
      sourceCode.substring(0, insertPosition) +
      '\n' + beforeEachContent +
      sourceCode.substring(insertPosition)
    );
  }

  /**
   * Update existing beforeEach with additional counter resets
   */
  private updateBeforeEach(
    sourceCode: string,
    counters: CounterResetFunction[]
  ): string {
    // Find beforeEach block
    const beforeEachMatch = sourceCode.match(/beforeEach\s*\(\s*(?:async\s*)?\(\)\s*=>\s*\{/);
    
    if (!beforeEachMatch || beforeEachMatch.index === undefined) {
      // Can't find beforeEach pattern to update
      return sourceCode;
    }

    // Find the opening brace position
    const braceStart = beforeEachMatch.index + beforeEachMatch[0].length;

    // Generate reset calls
    const resetCalls = counters.map((c) => `    ${c.name}();`).join('\n');
    const customCalls = this.options.customBeforeEach.map((c) => `    ${c};`).join('\n');
    const allCalls = [resetCalls, customCalls].filter(Boolean).join('\n');

    if (!allCalls) {
      return sourceCode;
    }

    // Insert after opening brace
    return (
      sourceCode.substring(0, braceStart) +
      '\n' + allCalls +
      sourceCode.substring(braceStart)
    );
  }

  /**
   * Generate beforeEach block content
   */
  private generateBeforeEachContent(counters: CounterResetFunction[]): string {
    const resetCalls = counters.map((c) => `    ${c.name}();`).join('\n');
    const customCalls = this.options.customBeforeEach.map((c) => `    ${c};`).join('\n');
    const allCalls = [resetCalls, customCalls].filter(Boolean).join('\n');

    return `  beforeEach(() => {
${allCalls}
  });
`;
  }
}

/**
 * Convenience function to decorate a test file
 *
 * @param sourceCode - Original test file source
 * @param entityImports - Entity imports with reset functions
 * @param options - Decoration options
 * @returns Decorated result
 */
export function decorateTestFile(
  sourceCode: string,
  entityImports: CounterResetFunction[] = [],
  options?: TestFileDecoratorOptions
): DecorationResult {
  const decorator = new TestFileDecorator(options);
  return decorator.decorate(sourceCode, entityImports);
}

/**
 * Check if test file needs counter reset decoration
 *
 * @param sourceCode - Test file source code
 * @returns true if decoration is recommended
 */
export function needsCounterReset(sourceCode: string): boolean {
  // Has entity creation patterns
  const hasEntityCreation =
    /create\w+\(|new\s+\w+\(|generate\w+Id\(/i.test(sourceCode);

  // Doesn't have beforeEach with reset
  const hasResetInBeforeEach =
    /beforeEach\s*\([^)]*\)\s*=>\s*\{[^}]*reset\w*Counter/s.test(sourceCode);

  return hasEntityCreation && !hasResetInBeforeEach;
}
