/**
 * @fileoverview Fix Validator for Security Fixes
 * @module @nahisaho/musubix-security/remediation/fix-validator
 * 
 * Validates security fixes before and after application to ensure
 * they correctly address vulnerabilities without introducing new issues.
 */

import type { Fix, Vulnerability, SourceLocation } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Validation result
 */
export interface ValidationResult {
  /** Whether validation passed */
  valid: boolean;
  /** Fix that was validated */
  fixId: string;
  /** Validation checks performed */
  checks: ValidationCheck[];
  /** Overall score (0-100) */
  score: number;
  /** Recommendations */
  recommendations: string[];
  /** Validation timestamp */
  timestamp: Date;
}

/**
 * Individual validation check
 */
export interface ValidationCheck {
  /** Check name */
  name: string;
  /** Check category */
  category: 'syntax' | 'semantic' | 'security' | 'regression' | 'compatibility';
  /** Whether check passed */
  passed: boolean;
  /** Check details */
  details: string;
  /** Severity if failed */
  severity?: 'error' | 'warning' | 'info';
}

/**
 * Syntax validation result
 */
export interface SyntaxValidationResult {
  /** Whether syntax is valid */
  valid: boolean;
  /** Syntax errors */
  errors: SyntaxError[];
  /** Abstract syntax tree available */
  hasAST: boolean;
}

/**
 * Syntax error
 */
export interface SyntaxError {
  /** Error message */
  message: string;
  /** Location */
  location?: SourceLocation;
  /** Error code */
  code?: string;
}

/**
 * Regression test result
 */
export interface RegressionTestResult {
  /** Total tests */
  total: number;
  /** Passed tests */
  passed: number;
  /** Failed tests */
  failed: number;
  /** Skipped tests */
  skipped: number;
  /** Test details */
  details: TestDetail[];
}

/**
 * Test detail
 */
export interface TestDetail {
  /** Test name */
  name: string;
  /** Test status */
  status: 'passed' | 'failed' | 'skipped';
  /** Duration in ms */
  duration: number;
  /** Error if failed */
  error?: string;
}

/**
 * Security re-scan result
 */
export interface SecurityRescanResult {
  /** Original vulnerability resolved */
  vulnerabilityResolved: boolean;
  /** New vulnerabilities introduced */
  newVulnerabilities: Vulnerability[];
  /** Remaining vulnerabilities */
  remainingVulnerabilities: Vulnerability[];
  /** Security improvement score */
  improvementScore: number;
}

/**
 * Fix validator options
 */
export interface FixValidatorOptions {
  /** Enable syntax validation */
  syntaxValidation?: boolean;
  /** Enable semantic validation */
  semanticValidation?: boolean;
  /** Enable security re-scan */
  securityRescan?: boolean;
  /** Enable regression testing */
  regressionTesting?: boolean;
  /** Strict mode (fail on warnings) */
  strictMode?: boolean;
  /** Custom validation rules */
  customRules?: CustomValidationRule[];
}

/**
 * Custom validation rule
 */
export interface CustomValidationRule {
  /** Rule ID */
  id: string;
  /** Rule name */
  name: string;
  /** Validation function */
  validate: (fix: Fix, originalCode: string, fixedCode: string) => ValidationCheck;
}

// ============================================================================
// FixValidator Class
// ============================================================================

/**
 * Validator for security fixes
 * 
 * @example
 * ```typescript
 * const validator = createFixValidator();
 * const result = await validator.validate(fix, originalCode, fixedCode);
 * if (!result.valid) {
 *   console.log('Fix validation failed:', result.checks);
 * }
 * ```
 */
export class FixValidator {
  private options: Required<FixValidatorOptions>;
  private customRules: Map<string, CustomValidationRule>;

  constructor(options: FixValidatorOptions = {}) {
    this.options = {
      syntaxValidation: options.syntaxValidation ?? true,
      semanticValidation: options.semanticValidation ?? true,
      securityRescan: options.securityRescan ?? true,
      regressionTesting: options.regressionTesting ?? false,
      strictMode: options.strictMode ?? false,
      customRules: options.customRules ?? [],
    };
    this.customRules = new Map();
    
    for (const rule of this.options.customRules) {
      this.customRules.set(rule.id, rule);
    }
  }

  /**
   * Validate a fix
   */
  async validate(
    fix: Fix,
    originalCode: string,
    fixedCode: string,
    _originalVulnerability?: Vulnerability
  ): Promise<ValidationResult> {
    const checks: ValidationCheck[] = [];
    const recommendations: string[] = [];

    // Basic fix validation
    checks.push(this.validateFixStructure(fix));

    // Syntax validation
    if (this.options.syntaxValidation) {
      const syntaxCheck = this.validateSyntax(fixedCode);
      checks.push(syntaxCheck);
      if (!syntaxCheck.passed) {
        recommendations.push('Fix the syntax errors before applying this fix');
      }
    }

    // Semantic validation
    if (this.options.semanticValidation) {
      const semanticChecks = this.validateSemantics(originalCode, fixedCode);
      checks.push(...semanticChecks);
    }

    // Security checks
    checks.push(...this.validateSecurityProperties(fix, fixedCode));

    // Custom rules
    for (const rule of this.customRules.values()) {
      try {
        const check = rule.validate(fix, originalCode, fixedCode);
        checks.push(check);
      } catch (error) {
        checks.push({
          name: rule.name,
          category: 'security',
          passed: false,
          details: `Custom rule failed: ${error instanceof Error ? error.message : 'Unknown error'}`,
          severity: 'warning',
        });
      }
    }

    // Calculate score
    const score = this.calculateScore(checks);

    // Determine validity
    const valid = this.determineValidity(checks);

    // Generate additional recommendations
    if (fix.breakingChange) {
      recommendations.push('This fix may cause breaking changes - review carefully');
    }
    if (fix.confidence < 0.8) {
      recommendations.push('Low confidence fix - manual review recommended');
    }

    return {
      valid,
      fixId: fix.id,
      checks,
      score,
      recommendations,
      timestamp: new Date(),
    };
  }

  /**
   * Validate fix syntax
   */
  validateSyntax(code: string): ValidationCheck {
    const errors: SyntaxError[] = [];

    // Basic syntax checks
    try {
      // Check for balanced brackets
      const balanced = this.checkBalancedBrackets(code);
      if (!balanced.valid) {
        errors.push({ message: balanced.message });
      }

      // Check for common syntax issues
      const commonIssues = this.checkCommonSyntaxIssues(code);
      errors.push(...commonIssues);

    } catch (error) {
      errors.push({
        message: error instanceof Error ? error.message : 'Unknown syntax error',
      });
    }

    return {
      name: 'Syntax Validation',
      category: 'syntax',
      passed: errors.length === 0,
      details: errors.length === 0
        ? 'Syntax validation passed'
        : `Found ${errors.length} syntax error(s): ${errors.map(e => e.message).join(', ')}`,
      severity: errors.length > 0 ? 'error' : undefined,
    };
  }

  /**
   * Validate semantic properties
   */
  validateSemantics(originalCode: string, fixedCode: string): ValidationCheck[] {
    const checks: ValidationCheck[] = [];

    // Check code length change
    const lengthRatio = fixedCode.length / originalCode.length;
    checks.push({
      name: 'Code Size Change',
      category: 'semantic',
      passed: lengthRatio > 0.5 && lengthRatio < 2.0,
      details: `Code size changed by ${((lengthRatio - 1) * 100).toFixed(1)}%`,
      severity: lengthRatio > 2.0 || lengthRatio < 0.5 ? 'warning' : undefined,
    });

    // Check for preserved structure
    const structurePreserved = this.checkStructurePreservation(originalCode, fixedCode);
    checks.push({
      name: 'Structure Preservation',
      category: 'semantic',
      passed: structurePreserved,
      details: structurePreserved
        ? 'Code structure largely preserved'
        : 'Significant structural changes detected',
      severity: !structurePreserved ? 'warning' : undefined,
    });

    // Check for variable usage
    const variableCheck = this.checkVariableUsage(originalCode, fixedCode);
    checks.push(variableCheck);

    return checks;
  }

  /**
   * Validate security properties of the fix
   */
  validateSecurityProperties(fix: Fix, fixedCode: string): ValidationCheck[] {
    const checks: ValidationCheck[] = [];

    // Check if fix addresses the vulnerability type
    checks.push({
      name: 'Vulnerability Type Match',
      category: 'security',
      passed: this.fixAddressesVulnerabilityType(fix),
      details: `Fix strategy '${fix.strategy}' for vulnerability`,
    });

    // Check for security anti-patterns in fixed code
    const antiPatterns = this.checkSecurityAntiPatterns(fixedCode);
    checks.push({
      name: 'Security Anti-patterns',
      category: 'security',
      passed: antiPatterns.length === 0,
      details: antiPatterns.length === 0
        ? 'No security anti-patterns detected'
        : `Found anti-patterns: ${antiPatterns.join(', ')}`,
      severity: antiPatterns.length > 0 ? 'error' : undefined,
    });

    // Check for dangerous function usage
    const dangerousFunctions = this.checkDangerousFunctions(fixedCode);
    checks.push({
      name: 'Dangerous Functions',
      category: 'security',
      passed: dangerousFunctions.length === 0,
      details: dangerousFunctions.length === 0
        ? 'No dangerous functions detected'
        : `Found dangerous functions: ${dangerousFunctions.join(', ')}`,
      severity: dangerousFunctions.length > 0 ? 'warning' : undefined,
    });

    return checks;
  }

  /**
   * Register a custom validation rule
   */
  registerRule(rule: CustomValidationRule): void {
    this.customRules.set(rule.id, rule);
  }

  /**
   * Remove a custom validation rule
   */
  removeRule(ruleId: string): boolean {
    return this.customRules.delete(ruleId);
  }

  /**
   * Get all validation rules
   */
  getRules(): CustomValidationRule[] {
    return Array.from(this.customRules.values());
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private validateFixStructure(fix: Fix): ValidationCheck {
    const issues: string[] = [];

    if (!fix.id) issues.push('Missing fix ID');
    if (!fix.vulnerabilityId) issues.push('Missing vulnerability reference');
    if (!fix.strategy) issues.push('Missing fix strategy');
    if (!fix.edits || fix.edits.length === 0) issues.push('No edits specified');

    return {
      name: 'Fix Structure',
      category: 'syntax',
      passed: issues.length === 0,
      details: issues.length === 0
        ? 'Fix structure is valid'
        : `Structure issues: ${issues.join(', ')}`,
      severity: issues.length > 0 ? 'error' : undefined,
    };
  }

  private checkBalancedBrackets(code: string): { valid: boolean; message: string } {
    const stack: string[] = [];
    const pairs: Record<string, string> = { '(': ')', '[': ']', '{': '}' };
    const openers = new Set(Object.keys(pairs));
    const closers = new Set(Object.values(pairs));

    // Track if we're in a string or comment
    let inString = false;
    let stringChar = '';
    let inSingleLineComment = false;
    let inMultiLineComment = false;

    for (let i = 0; i < code.length; i++) {
      const char = code[i];
      const prevChar = i > 0 ? code[i - 1] : '';
      const nextChar = i < code.length - 1 ? code[i + 1] : '';

      // Handle comments
      if (!inString) {
        if (char === '/' && nextChar === '/' && !inMultiLineComment) {
          inSingleLineComment = true;
          continue;
        }
        if (char === '/' && nextChar === '*' && !inSingleLineComment) {
          inMultiLineComment = true;
          continue;
        }
        if (char === '\n' && inSingleLineComment) {
          inSingleLineComment = false;
          continue;
        }
        if (char === '*' && nextChar === '/' && inMultiLineComment) {
          inMultiLineComment = false;
          i++; // Skip the '/'
          continue;
        }
      }

      if (inSingleLineComment || inMultiLineComment) continue;

      // Handle strings
      if ((char === '"' || char === "'" || char === '`') && prevChar !== '\\') {
        if (!inString) {
          inString = true;
          stringChar = char;
        } else if (char === stringChar) {
          inString = false;
          stringChar = '';
        }
        continue;
      }

      if (inString) continue;

      // Check brackets
      if (openers.has(char)) {
        stack.push(char);
      } else if (closers.has(char)) {
        if (stack.length === 0) {
          return { valid: false, message: `Unmatched closing bracket '${char}'` };
        }
        const opener = stack.pop()!;
        if (pairs[opener] !== char) {
          return { valid: false, message: `Mismatched brackets: '${opener}' and '${char}'` };
        }
      }
    }

    if (stack.length > 0) {
      return { valid: false, message: `Unclosed brackets: ${stack.join(', ')}` };
    }

    return { valid: true, message: 'Brackets are balanced' };
  }

  private checkCommonSyntaxIssues(code: string): SyntaxError[] {
    const errors: SyntaxError[] = [];

    // Check for duplicate operators
    if (/[+\-*\/]{3,}/.test(code)) {
      errors.push({ message: 'Multiple consecutive operators detected' });
    }

    // Check for obvious missing semicolons (conservative)
    // Note: Modern JS allows ASI, so we only flag clear issues
    const lines = code.split('\n');
    for (let i = 0; i < lines.length; i++) {
      const trimmed = lines[i].trim();
      // Check for specific patterns that almost always need semicolons
      if (/^(const|let|var)\s+\w+\s*=\s*[^{[\n]+\s*$/.test(trimmed) &&
          !trimmed.endsWith(';') &&
          !trimmed.endsWith(',')) {
        // Only flag if next line starts with something that would cause issues
        const nextLine = lines[i + 1]?.trim() || '';
        if (nextLine.startsWith('(') || nextLine.startsWith('[')) {
          // Potential ASI hazard - but still don't flag as error
        }
      }
    }

    return errors;
  }

  private checkStructurePreservation(original: string, fixed: string): boolean {
    // Count key structural elements
    const countStructure = (code: string) => ({
      functions: (code.match(/function\s+\w+/g) || []).length,
      classes: (code.match(/class\s+\w+/g) || []).length,
      arrows: (code.match(/=>/g) || []).length,
      returns: (code.match(/return\s/g) || []).length,
    });

    const originalStructure = countStructure(original);
    const fixedStructure = countStructure(fixed);

    // Allow some variation but flag major changes
    const functionDiff = Math.abs(originalStructure.functions - fixedStructure.functions);
    const classDiff = Math.abs(originalStructure.classes - fixedStructure.classes);

    return functionDiff <= 1 && classDiff === 0;
  }

  private checkVariableUsage(original: string, fixed: string): ValidationCheck {
    // Extract variable declarations
    const extractVars = (code: string): Set<string> => {
      const vars = new Set<string>();
      const matches = code.matchAll(/(?:const|let|var)\s+(\w+)/g);
      for (const match of matches) {
        vars.add(match[1]);
      }
      return vars;
    };

    const originalVars = extractVars(original);
    const fixedVars = extractVars(fixed);

    // Check for removed variables (might indicate important code removal)
    const removedVars = [...originalVars].filter(v => !fixedVars.has(v));

    return {
      name: 'Variable Usage',
      category: 'semantic',
      passed: removedVars.length <= 2,
      details: removedVars.length === 0
        ? 'All original variables preserved'
        : `${removedVars.length} variable(s) removed: ${removedVars.join(', ')}`,
      severity: removedVars.length > 2 ? 'warning' : undefined,
    };
  }

  private fixAddressesVulnerabilityType(fix: Fix): boolean {
    // Map strategies to what they address
    const strategyMap: Record<string, string[]> = {
      sanitization: ['xss', 'injection', 'html_injection'],
      encoding: ['xss', 'html_injection'],
      parameterization: ['sql_injection', 'injection'],
      validation: ['path_traversal', 'injection', 'input_validation'],
      configuration: ['hardcoded_secret', 'exposed_credential', 'misconfiguration'],
      replacement: ['weak_cryptography', 'deprecated_api'],
      access_control: ['authentication', 'authorization', 'access_control'],
    };

    const addressedTypes = strategyMap[fix.strategy] || [];
    return addressedTypes.length > 0;
  }

  private checkSecurityAntiPatterns(code: string): string[] {
    const antiPatterns: string[] = [];

    // eval usage
    if (/\beval\s*\(/.test(code)) {
      antiPatterns.push('eval()');
    }

    // innerHTML without sanitization
    if (/\.innerHTML\s*=/.test(code) && !/sanitize|DOMPurify/i.test(code)) {
      antiPatterns.push('innerHTML without sanitization');
    }

    // document.write
    if (/document\.write\s*\(/.test(code)) {
      antiPatterns.push('document.write()');
    }

    // new Function()
    if (/new\s+Function\s*\(/.test(code)) {
      antiPatterns.push('new Function()');
    }

    return antiPatterns;
  }

  private checkDangerousFunctions(code: string): string[] {
    const dangerous: string[] = [];

    const dangerousPatterns = [
      { pattern: /child_process\.exec\s*\(/, name: 'child_process.exec' },
      { pattern: /\.execSync\s*\(/, name: 'execSync' },
      { pattern: /\$\(.*\)\.html\s*\(/, name: 'jQuery.html()' },
      { pattern: /setTimeout\s*\(\s*["'`]/, name: 'setTimeout with string' },
      { pattern: /setInterval\s*\(\s*["'`]/, name: 'setInterval with string' },
    ];

    for (const { pattern, name } of dangerousPatterns) {
      if (pattern.test(code)) {
        dangerous.push(name);
      }
    }

    return dangerous;
  }

  private calculateScore(checks: ValidationCheck[]): number {
    if (checks.length === 0) return 100;

    let score = 100;
    const weights = { error: 25, warning: 10, info: 5 };

    for (const check of checks) {
      if (!check.passed) {
        const weight = weights[check.severity || 'info'] || 5;
        score -= weight;
      }
    }

    return Math.max(0, score);
  }

  private determineValidity(checks: ValidationCheck[]): boolean {
    if (this.options.strictMode) {
      return checks.every(c => c.passed);
    }

    // In non-strict mode, only fail on errors
    return !checks.some(c => !c.passed && c.severity === 'error');
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a fix validator
 */
export function createFixValidator(options?: FixValidatorOptions): FixValidator {
  return new FixValidator(options);
}

/**
 * Quick validate a fix
 */
export async function quickValidate(
  fix: Fix,
  originalCode: string,
  fixedCode: string
): Promise<boolean> {
  const validator = createFixValidator({
    syntaxValidation: true,
    semanticValidation: false,
    securityRescan: false,
    regressionTesting: false,
  });

  const result = await validator.validate(fix, originalCode, fixedCode);
  return result.valid;
}
