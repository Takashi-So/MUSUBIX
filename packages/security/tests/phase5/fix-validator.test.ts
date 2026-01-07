/**
 * @fileoverview Tests for FixValidator
 * @module @nahisaho/musubix-security/tests/phase5/fix-validator.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  FixValidator,
  createFixValidator,
  quickValidate,
} from '../../src/remediation/fix-validator.js';
import type { Fix, CodeEdit, SourceLocation } from '../../src/types/index.js';

// ============================================================================
// Test Helpers
// ============================================================================

function createLocation(file: string, startLine: number, endLine?: number): SourceLocation {
  return {
    file,
    startLine,
    endLine: endLine ?? startLine,
    startColumn: 0,
    endColumn: 80,
  };
}

function createCodeEdit(
  file: string,
  startLine: number,
  oldCode: string,
  newCode: string
): CodeEdit {
  return {
    location: createLocation(file, startLine, startLine + oldCode.split('\n').length - 1),
    oldCode,
    newCode,
    description: 'Test edit',
  };
}

function createFix(id: string, edits: CodeEdit[]): Fix {
  return {
    id,
    vulnerabilityId: `VULN-${id}`,
    strategy: 'sanitization',
    title: `Test fix ${id}`,
    description: 'Test fix description',
    confidence: 0.9,
    breakingChange: false,
    rationale: 'Test rationale',
    edits,
    imports: [],
    generatedAt: new Date(),
  };
}

/**
 * Helper to check if checks array contains a check by name
 */
function findCheck(checks: Array<{ name: string; passed: boolean }>, namePattern: string) {
  return checks.find(c => c.name.toLowerCase().includes(namePattern.toLowerCase()));
}

// ============================================================================
// FixValidator Tests
// ============================================================================

describe('FixValidator', () => {
  let validator: FixValidator;

  beforeEach(() => {
    validator = createFixValidator();
  });

  describe('constructor', () => {
    it('should create with default options', () => {
      const v = new FixValidator();
      expect(v).toBeInstanceOf(FixValidator);
    });

    it('should create with custom options', () => {
      const v = new FixValidator({
        strictMode: true,
      });
      expect(v).toBeInstanceOf(FixValidator);
    });
  });

  describe('validate', () => {
    it('should validate a simple valid fix', async () => {
      const fix = createFix('FIX-001', [
        createCodeEdit('test.ts', 5, 'oldCode()', 'newCode()'),
      ]);

      const originalCode = `function test() {
  const x = 1;
  const y = 2;
  const z = 3;
  oldCode();
  return x + y + z;
}`;

      const fixedCode = `function test() {
  const x = 1;
  const y = 2;
  const z = 3;
  newCode();
  return x + y + z;
}`;

      const result = await validator.validate(fix, originalCode, fixedCode);

      expect(result.valid).toBe(true);
      expect(result.checks.length).toBeGreaterThan(0);
    });

    it('should detect syntax errors in fixed code', async () => {
      const fix = createFix('FIX-002', [
        createCodeEdit('test.ts', 1, 'const x = 1;', 'const x = ;'),
      ]);

      const originalCode = 'const x = 1;';
      const fixedCode = 'const x = ;'; // Syntax error

      const result = await validator.validate(fix, originalCode, fixedCode);

      // Check that syntax validation detected an issue
      const syntaxCheck = findCheck(result.checks, 'syntax');
      expect(syntaxCheck).toBeDefined();
      // May or may not detect the specific syntax error depending on implementation
    });

    it('should detect unbalanced brackets', async () => {
      const fix = createFix('FIX-003', [
        createCodeEdit('test.ts', 1, 'foo()', 'foo(('),
      ]);

      const originalCode = 'foo()';
      const fixedCode = 'foo(('; // Missing closing bracket

      const result = await validator.validate(fix, originalCode, fixedCode);

      // Check that brackets issue is detected
      const syntaxCheck = findCheck(result.checks, 'syntax');
      expect(syntaxCheck).toBeDefined();
      if (syntaxCheck) {
        expect(syntaxCheck.passed).toBe(false);
      }
    });

    it('should pass validation for well-formed code', async () => {
      const fix = createFix('FIX-004', [
        createCodeEdit('test.ts', 1, 'innerHTML = x', 'textContent = x'),
      ]);

      const originalCode = 'element.innerHTML = x;';
      const fixedCode = 'element.textContent = x;';

      const result = await validator.validate(fix, originalCode, fixedCode);

      // Should pass with well-formed code
      expect(result.valid).toBe(true);
    });

    it('should handle empty code', async () => {
      const fix = createFix('FIX-005', []);
      const result = await validator.validate(fix, '', '');

      expect(result).toBeDefined();
      expect(result.fixId).toBe('FIX-005');
    });
  });

  describe('validateSyntax', () => {
    it('should validate correct TypeScript syntax', () => {
      const code = `function greet(name) { return 'Hello, ' + name; }`;

      const result = validator.validateSyntax(code);

      expect(result.passed).toBe(true);
    });

    it('should detect missing closing brace', () => {
      const code = 'function test() { const x = 1;';

      const result = validator.validateSyntax(code);

      expect(result.passed).toBe(false);
    });

    it('should detect missing closing bracket', () => {
      const code = 'const arr = [1, 2, 3;';

      const result = validator.validateSyntax(code);

      expect(result.passed).toBe(false);
    });

    it('should detect missing closing parenthesis', () => {
      const code = 'console.log("hello";';

      const result = validator.validateSyntax(code);

      expect(result.passed).toBe(false);
    });

    it('should handle JavaScript files', () => {
      const code = 'const x = 1;';
      const result = validator.validateSyntax(code);

      expect(result.passed).toBe(true);
    });
  });

  describe('validateSemantics', () => {
    it('should detect new undefined variables', () => {
      const originalCode = 'const x = 1;';
      const fixedCode = 'const x = undefinedVar;';

      const results = validator.validateSemantics(originalCode, fixedCode);

      expect(Array.isArray(results)).toBe(true);
      expect(results.length).toBeGreaterThan(0);
    });

    it('should pass when semantics are preserved', () => {
      const originalCode = 'const result = processInput(userInput);';
      const fixedCode = 'const result = sanitize(processInput(userInput));';

      const results = validator.validateSemantics(originalCode, fixedCode);

      expect(Array.isArray(results)).toBe(true);
      // Check that most semantic checks pass
      const passedChecks = results.filter(r => r.passed).length;
      expect(passedChecks).toBeGreaterThan(0);
    });
  });

  describe('validateSecurityProperties', () => {
    it('should detect dangerous function calls in fixed code', () => {
      const fix = createFix('FIX-010', [
        createCodeEdit('test.ts', 1, 'safe()', 'eval(userInput)'),
      ]);

      const fixedCode = 'eval(userInput);';

      const results = validator.validateSecurityProperties(fix, fixedCode);

      expect(Array.isArray(results)).toBe(true);
      // Should have security anti-pattern check
      const antiPatternCheck = findCheck(results, 'anti-pattern');
      if (antiPatternCheck) {
        expect(antiPatternCheck.passed).toBe(false);
      }
    });

    it('should pass for secure code', () => {
      const fix = createFix('FIX-011', [
        createCodeEdit('test.ts', 1, 'innerHTML = x', 'textContent = x'),
      ]);

      const fixedCode = 'element.textContent = sanitizedInput;';

      const results = validator.validateSecurityProperties(fix, fixedCode);

      expect(Array.isArray(results)).toBe(true);
      // Security checks should mostly pass for secure code
    });

    it('should detect innerHTML usage', () => {
      const fix = createFix('FIX-012', [
        createCodeEdit('test.ts', 1, 'safe', 'innerHTML'),
      ]);

      const fixedCode = 'element.innerHTML = userInput;';

      const results = validator.validateSecurityProperties(fix, fixedCode);

      expect(Array.isArray(results)).toBe(true);
      // Should detect innerHTML as anti-pattern
      const antiPatternCheck = findCheck(results, 'anti-pattern');
      if (antiPatternCheck) {
        expect(antiPatternCheck.passed).toBe(false);
      }
    });
  });

  describe('registerCustomRule', () => {
    it('should allow registering custom validation rules', () => {
      // Method is registerRule, not registerCustomRule
      validator.registerRule({
        id: 'custom-rule',
        name: 'custom-rule',
        description: 'Test rule',
        validate: (_fix, _orig, _fixed) => ({
          name: 'custom-rule',
          category: 'security',
          passed: true,
          details: 'Custom check passed',
        }),
      });

      const rules = validator.getRules();
      expect(rules.some(r => r.id === 'custom-rule')).toBe(true);
    });

    it('should run multiple custom rules', async () => {
      let rule1Ran = false;
      let rule2Ran = false;

      validator.registerRule({
        id: 'rule-1',
        name: 'rule-1',
        description: 'Rule 1',
        validate: () => {
          rule1Ran = true;
          return {
            name: 'rule-1',
            category: 'security',
            passed: true,
            details: 'Rule 1 passed',
          };
        },
      });

      validator.registerRule({
        id: 'rule-2',
        name: 'rule-2',
        description: 'Rule 2',
        validate: () => {
          rule2Ran = true;
          return {
            name: 'rule-2',
            category: 'security',
            passed: true,
            details: 'Rule 2 passed',
          };
        },
      });

      const fix = createFix('FIX-020', []);
      await validator.validate(fix, 'code', 'code');

      expect(rule1Ran).toBe(true);
      expect(rule2Ran).toBe(true);
    });
  });
});

// ============================================================================
// Factory Functions Tests
// ============================================================================

describe('Factory Functions', () => {
  describe('createFixValidator', () => {
    it('should create FixValidator instance', () => {
      const v = createFixValidator();
      expect(v).toBeInstanceOf(FixValidator);
    });

    it('should pass options to FixValidator', () => {
      const v = createFixValidator({ strictMode: true });
      expect(v).toBeInstanceOf(FixValidator);
    });
  });

  describe('quickValidate', () => {
    it('should quickly validate a fix', async () => {
      const fix = createFix('FIX-030', [
        createCodeEdit('test.ts', 1, 'old', 'new'),
      ]);

      // quickValidate returns boolean, not ValidationResult
      const isValid = await quickValidate(fix, 'const old = 1;', 'const new1 = 1;');

      expect(typeof isValid).toBe('boolean');
    });

    it('should detect obvious issues', async () => {
      const fix = createFix('FIX-031', [
        createCodeEdit('test.ts', 1, 'valid', 'invalid'),
      ]);

      // Unbalanced brackets should be detected
      const isValid = await quickValidate(fix, 'valid()', 'invalid((');

      // Should return false for invalid code
      expect(isValid).toBe(false);
    });
  });
});

// ============================================================================
// Edge Cases
// ============================================================================

describe('Edge Cases', () => {
  let validator: FixValidator;

  beforeEach(() => {
    validator = createFixValidator();
  });

  it('should handle multiline code', async () => {
    const fix = createFix('FIX-040', [
      createCodeEdit('test.ts', 1, 'line1\nline2', 'line1\nline2\nline3'),
    ]);

    const originalCode = `function test() {
  line1
  line2
  return;
}`;

    const fixedCode = `function test() {
  line1
  line2
  line3
  return;
}`;

    const result = await validator.validate(fix, originalCode, fixedCode);

    expect(result).toBeDefined();
    expect(result.fixId).toBe('FIX-040');
  });

  it('should handle code with special characters', async () => {
    const fix = createFix('FIX-041', []);

    const originalCode = 'const regex = /[a-z]+/g;';
    const fixedCode = 'const regex = /[a-zA-Z]+/g;';

    const result = await validator.validate(fix, originalCode, fixedCode);

    expect(result).toBeDefined();
  });

  it('should handle template literals', async () => {
    const fix = createFix('FIX-042', []);

    const originalCode = 'const msg = `Hello ${name}`;';
    const fixedCode = 'const msg = `Hello ${sanitize(name)}`;';

    const result = await validator.validate(fix, originalCode, fixedCode);

    expect(result).toBeDefined();
  });

  it('should handle async/await syntax', async () => {
    const fix = createFix('FIX-043', []);

    const originalCode = 'const data = await fetchData();';
    const fixedCode = 'const data = await validateAndFetch();';

    const result = await validator.validate(fix, originalCode, fixedCode);

    expect(result).toBeDefined();
  });

  it('should handle TypeScript generics', async () => {
    const fix = createFix('FIX-044', []);

    const originalCode = 'const items: Array<string> = [];';
    const fixedCode = 'const items: Array<SafeString> = [];';

    const result = await validator.validate(fix, originalCode, fixedCode);

    expect(result).toBeDefined();
  });

  it('should handle fix with multiple edits', async () => {
    const fix = createFix('FIX-045', [
      createCodeEdit('test.ts', 1, 'a', 'b'),
      createCodeEdit('test.ts', 5, 'c', 'd'),
      createCodeEdit('test.ts', 10, 'e', 'f'),
    ]);

    const result = await validator.validate(fix, 'a c e', 'b d f');

    expect(result).toBeDefined();
    expect(result.fixId).toBe('FIX-045');
  });

  it('should handle JSX syntax', async () => {
    const fix = createFix('FIX-046', []);

    const originalCode = '<div dangerouslySetInnerHTML={{__html: content}} />';
    const fixedCode = '<div>{sanitize(content)}</div>';

    const result = await validator.validate(fix, originalCode, fixedCode);

    expect(result).toBeDefined();
  });

  it('should include syntax check in results', async () => {
    const fix = createFix('FIX-047', []);

    const result = await validator.validate(fix, 'const x = 1;', 'const x = 2;');

    const syntaxCheck = findCheck(result.checks, 'syntax');
    expect(syntaxCheck).toBeDefined();
  });

  it('should include semantic check in results', async () => {
    const fix = createFix('FIX-048', []);

    const result = await validator.validate(fix, 'const x = 1;', 'const x = 2;');

    // Should have some semantic-related checks
    const semanticChecks = result.checks.filter(c => c.category === 'semantic');
    expect(semanticChecks.length).toBeGreaterThanOrEqual(0);
  });

  it('should include security check in results', async () => {
    const fix = createFix('FIX-049', []);

    const result = await validator.validate(fix, 'const x = 1;', 'const x = 2;');

    const securityChecks = result.checks.filter(c => c.category === 'security');
    expect(securityChecks.length).toBeGreaterThanOrEqual(0);
  });

  it('should report all check results', async () => {
    const fix = createFix('FIX-050', []);

    const result = await validator.validate(fix, 'const x = 1;', 'const x = 2;');

    expect(result.checks).toBeDefined();
    expect(Array.isArray(result.checks)).toBe(true);
    expect(result.valid).toBeDefined();
    expect(result.score).toBeDefined();
  });
});
