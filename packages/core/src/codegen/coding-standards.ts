/**
 * Coding Standards Checker
 * 
 * Checks and enforces coding standards
 * 
 * @packageDocumentation
 * @module codegen/coding-standards
 * 
 * @see REQ-COD-005 - Coding Standards Enforcement
 * @see Article III - Bidirectional Traceability
 */

/**
 * Severity level
 */
export type Severity = 'error' | 'warning' | 'info' | 'hint';

/**
 * Standard category
 */
export type StandardCategory =
  | 'naming'
  | 'formatting'
  | 'structure'
  | 'documentation'
  | 'complexity'
  | 'security'
  | 'performance'
  | 'testing'
  | 'style';

/**
 * Coding standard rule
 */
export interface CodingRule {
  /** Rule ID */
  id: string;
  /** Rule name */
  name: string;
  /** Description */
  description: string;
  /** Category */
  category: StandardCategory;
  /** Severity */
  severity: Severity;
  /** Enabled */
  enabled: boolean;
  /** Configurable options */
  options?: Record<string, unknown>;
  /** Auto-fix available */
  autoFixable: boolean;
}

/**
 * Rule violation
 */
export interface RuleViolation {
  /** Rule ID */
  ruleId: string;
  /** Rule name */
  ruleName: string;
  /** Severity */
  severity: Severity;
  /** Message */
  message: string;
  /** File path */
  file: string;
  /** Line number */
  line: number;
  /** Column number */
  column: number;
  /** End line */
  endLine?: number;
  /** End column */
  endColumn?: number;
  /** Suggestion */
  suggestion?: string;
  /** Auto-fix available */
  autoFixable: boolean;
  /** Fix function */
  fix?: () => string;
}

/**
 * Check result
 */
export interface CheckResult {
  /** File checked */
  file: string;
  /** Violations found */
  violations: RuleViolation[];
  /** Error count */
  errorCount: number;
  /** Warning count */
  warningCount: number;
  /** Info count */
  infoCount: number;
  /** Passed */
  passed: boolean;
  /** Check duration (ms) */
  duration: number;
}

/**
 * Standards report
 */
export interface StandardsReport {
  /** Timestamp */
  timestamp: Date;
  /** Files checked */
  filesChecked: number;
  /** Files passed */
  filesPassed: number;
  /** Files failed */
  filesFailed: number;
  /** Total violations */
  totalViolations: number;
  /** Violations by severity */
  bySeverity: Record<Severity, number>;
  /** Violations by category */
  byCategory: Record<StandardCategory, number>;
  /** Results by file */
  results: CheckResult[];
  /** Duration (ms) */
  duration: number;
  /** Pass rate */
  passRate: number;
}

/**
 * Standards config
 */
export interface CodingStandardsConfig {
  /** Language */
  language: 'typescript' | 'javascript' | 'python' | 'java';
  /** Enabled categories */
  enabledCategories: StandardCategory[];
  /** Min severity to report */
  minSeverity: Severity;
  /** Fail on warning */
  failOnWarning: boolean;
  /** Ignore patterns */
  ignorePatterns: string[];
  /** Custom rules */
  customRules: CodingRule[];
}

/**
 * Default configuration
 */
export const DEFAULT_STANDARDS_CONFIG: CodingStandardsConfig = {
  language: 'typescript',
  enabledCategories: ['naming', 'formatting', 'structure', 'documentation', 'complexity'],
  minSeverity: 'warning',
  failOnWarning: false,
  ignorePatterns: ['node_modules/**', 'dist/**', '*.min.*'],
  customRules: [],
};

/**
 * Built-in rules
 */
export const BUILTIN_RULES: CodingRule[] = [
  // Naming rules
  {
    id: 'naming/camel-case',
    name: 'camelCase Variables',
    description: 'Variables should use camelCase',
    category: 'naming',
    severity: 'warning',
    enabled: true,
    autoFixable: false,
  },
  {
    id: 'naming/pascal-case-class',
    name: 'PascalCase Classes',
    description: 'Classes should use PascalCase',
    category: 'naming',
    severity: 'error',
    enabled: true,
    autoFixable: false,
  },
  {
    id: 'naming/upper-case-constants',
    name: 'UPPER_CASE Constants',
    description: 'Constants should use UPPER_CASE',
    category: 'naming',
    severity: 'warning',
    enabled: true,
    autoFixable: false,
  },
  {
    id: 'naming/prefix-interface',
    name: 'Interface Prefix',
    description: 'Interfaces should start with I prefix (optional)',
    category: 'naming',
    severity: 'info',
    enabled: false,
    autoFixable: false,
  },
  {
    id: 'naming/meaningful-names',
    name: 'Meaningful Names',
    description: 'Names should be descriptive and meaningful',
    category: 'naming',
    severity: 'warning',
    enabled: true,
    autoFixable: false,
  },

  // Formatting rules
  {
    id: 'formatting/max-line-length',
    name: 'Max Line Length',
    description: 'Lines should not exceed max length',
    category: 'formatting',
    severity: 'warning',
    enabled: true,
    options: { maxLength: 100 },
    autoFixable: false,
  },
  {
    id: 'formatting/consistent-indentation',
    name: 'Consistent Indentation',
    description: 'Use consistent indentation',
    category: 'formatting',
    severity: 'error',
    enabled: true,
    options: { style: 'space', size: 2 },
    autoFixable: true,
  },
  {
    id: 'formatting/trailing-comma',
    name: 'Trailing Comma',
    description: 'Use trailing commas in multiline',
    category: 'formatting',
    severity: 'info',
    enabled: true,
    autoFixable: true,
  },
  {
    id: 'formatting/semicolons',
    name: 'Semicolons',
    description: 'Use semicolons consistently',
    category: 'formatting',
    severity: 'warning',
    enabled: true,
    autoFixable: true,
  },

  // Structure rules
  {
    id: 'structure/max-file-lines',
    name: 'Max File Lines',
    description: 'Files should not exceed max lines',
    category: 'structure',
    severity: 'warning',
    enabled: true,
    options: { maxLines: 500 },
    autoFixable: false,
  },
  {
    id: 'structure/max-function-lines',
    name: 'Max Function Lines',
    description: 'Functions should not exceed max lines',
    category: 'structure',
    severity: 'warning',
    enabled: true,
    options: { maxLines: 50 },
    autoFixable: false,
  },
  {
    id: 'structure/max-parameters',
    name: 'Max Parameters',
    description: 'Functions should not have too many parameters',
    category: 'structure',
    severity: 'warning',
    enabled: true,
    options: { maxParams: 5 },
    autoFixable: false,
  },
  {
    id: 'structure/single-responsibility',
    name: 'Single Responsibility',
    description: 'Functions/classes should have single responsibility',
    category: 'structure',
    severity: 'info',
    enabled: true,
    autoFixable: false,
  },

  // Documentation rules
  {
    id: 'documentation/jsdoc-required',
    name: 'JSDoc Required',
    description: 'Public APIs should have JSDoc comments',
    category: 'documentation',
    severity: 'warning',
    enabled: true,
    autoFixable: false,
  },
  {
    id: 'documentation/jsdoc-params',
    name: 'JSDoc Parameters',
    description: 'JSDoc should document all parameters',
    category: 'documentation',
    severity: 'warning',
    enabled: true,
    autoFixable: false,
  },
  {
    id: 'documentation/jsdoc-returns',
    name: 'JSDoc Returns',
    description: 'JSDoc should document return value',
    category: 'documentation',
    severity: 'info',
    enabled: true,
    autoFixable: false,
  },

  // Complexity rules
  {
    id: 'complexity/cyclomatic',
    name: 'Cyclomatic Complexity',
    description: 'Cyclomatic complexity should not exceed threshold',
    category: 'complexity',
    severity: 'warning',
    enabled: true,
    options: { maxComplexity: 10 },
    autoFixable: false,
  },
  {
    id: 'complexity/max-nesting',
    name: 'Max Nesting',
    description: 'Nesting level should not exceed threshold',
    category: 'complexity',
    severity: 'warning',
    enabled: true,
    options: { maxNesting: 4 },
    autoFixable: false,
  },
  {
    id: 'complexity/cognitive',
    name: 'Cognitive Complexity',
    description: 'Cognitive complexity should not exceed threshold',
    category: 'complexity',
    severity: 'warning',
    enabled: true,
    options: { maxCognitive: 15 },
    autoFixable: false,
  },

  // Security rules
  {
    id: 'security/no-eval',
    name: 'No Eval',
    description: 'Avoid using eval()',
    category: 'security',
    severity: 'error',
    enabled: true,
    autoFixable: false,
  },
  {
    id: 'security/no-hardcoded-secrets',
    name: 'No Hardcoded Secrets',
    description: 'Avoid hardcoded secrets',
    category: 'security',
    severity: 'error',
    enabled: true,
    autoFixable: false,
  },
];

/**
 * Naming patterns
 */
const NAMING_PATTERNS = {
  camelCase: /^[a-z][a-zA-Z0-9]*$/,
  PascalCase: /^[A-Z][a-zA-Z0-9]*$/,
  UPPER_CASE: /^[A-Z][A-Z0-9_]*$/,
  kebabCase: /^[a-z][a-z0-9-]*$/,
  snakeCase: /^[a-z][a-z0-9_]*$/,
};

/**
 * Short name patterns (likely not meaningful)
 */
const SHORT_NAME_EXCEPTIONS = new Set(['i', 'j', 'k', 'n', 'x', 'y', 'z', 'id', 'ok', 'fn', 'cb']);

/**
 * Coding Standards Checker
 */
export class CodingStandardsChecker {
  private config: CodingStandardsConfig;
  private rules: Map<string, CodingRule> = new Map();

  constructor(config?: Partial<CodingStandardsConfig>) {
    this.config = { ...DEFAULT_STANDARDS_CONFIG, ...config };
    this.initializeRules();
  }

  /**
   * Initialize rules
   */
  private initializeRules(): void {
    // Add built-in rules
    for (const rule of BUILTIN_RULES) {
      if (this.config.enabledCategories.includes(rule.category)) {
        this.rules.set(rule.id, { ...rule });
      }
    }

    // Add custom rules
    for (const rule of this.config.customRules) {
      this.rules.set(rule.id, rule);
    }
  }

  /**
   * Check file content
   */
  check(content: string, filePath: string): CheckResult {
    const startTime = Date.now();
    const violations: RuleViolation[] = [];
    const lines = content.split('\n');

    // Run each rule
    for (const rule of this.rules.values()) {
      if (!rule.enabled) continue;
      if (!this.shouldReport(rule.severity)) continue;

      const ruleViolations = this.runRule(rule, content, lines, filePath);
      violations.push(...ruleViolations);
    }

    // Sort violations by line number
    violations.sort((a, b) => a.line - b.line);

    // Count by severity
    const errorCount = violations.filter((v) => v.severity === 'error').length;
    const warningCount = violations.filter((v) => v.severity === 'warning').length;
    const infoCount = violations.filter((v) => v.severity === 'info' || v.severity === 'hint').length;

    // Determine pass/fail
    const passed = errorCount === 0 && (!this.config.failOnWarning || warningCount === 0);

    return {
      file: filePath,
      violations,
      errorCount,
      warningCount,
      infoCount,
      passed,
      duration: Date.now() - startTime,
    };
  }

  /**
   * Check multiple files
   */
  checkFiles(files: Array<{ path: string; content: string }>): StandardsReport {
    const startTime = Date.now();
    const results: CheckResult[] = [];

    for (const file of files) {
      // Check ignore patterns
      if (this.shouldIgnore(file.path)) continue;
      
      const result = this.check(file.content, file.path);
      results.push(result);
    }

    // Aggregate results
    const bySeverity: Record<Severity, number> = {
      error: 0,
      warning: 0,
      info: 0,
      hint: 0,
    };

    const byCategory: Record<StandardCategory, number> = {
      naming: 0,
      formatting: 0,
      structure: 0,
      documentation: 0,
      complexity: 0,
      security: 0,
      performance: 0,
      testing: 0,
      style: 0,
    };

    let totalViolations = 0;

    for (const result of results) {
      for (const violation of result.violations) {
        totalViolations++;
        bySeverity[violation.severity]++;
        const rule = this.rules.get(violation.ruleId);
        if (rule) {
          byCategory[rule.category]++;
        }
      }
    }

    const filesPassed = results.filter((r) => r.passed).length;
    const filesFailed = results.length - filesPassed;

    return {
      timestamp: new Date(),
      filesChecked: results.length,
      filesPassed,
      filesFailed,
      totalViolations,
      bySeverity,
      byCategory,
      results,
      duration: Date.now() - startTime,
      passRate: results.length > 0 ? filesPassed / results.length : 1,
    };
  }

  /**
   * Run a specific rule
   */
  private runRule(
    rule: CodingRule,
    content: string,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];

    switch (rule.id) {
      case 'naming/camel-case':
        violations.push(...this.checkCamelCase(rule, lines, filePath));
        break;
      case 'naming/pascal-case-class':
        violations.push(...this.checkPascalCaseClass(rule, lines, filePath));
        break;
      case 'naming/upper-case-constants':
        violations.push(...this.checkUpperCaseConstants(rule, lines, filePath));
        break;
      case 'naming/meaningful-names':
        violations.push(...this.checkMeaningfulNames(rule, lines, filePath));
        break;
      case 'formatting/max-line-length':
        violations.push(...this.checkMaxLineLength(rule, lines, filePath));
        break;
      case 'formatting/consistent-indentation':
        violations.push(...this.checkIndentation(rule, lines, filePath));
        break;
      case 'structure/max-file-lines':
        violations.push(...this.checkMaxFileLines(rule, lines, filePath));
        break;
      case 'structure/max-function-lines':
        violations.push(...this.checkMaxFunctionLines(rule, lines, filePath));
        break;
      case 'structure/max-parameters':
        violations.push(...this.checkMaxParameters(rule, lines, filePath));
        break;
      case 'documentation/jsdoc-required':
        violations.push(...this.checkJSDocRequired(rule, lines, filePath));
        break;
      case 'complexity/cyclomatic':
        violations.push(...this.checkCyclomaticComplexity(rule, content, filePath));
        break;
      case 'complexity/max-nesting':
        violations.push(...this.checkMaxNesting(rule, lines, filePath));
        break;
      case 'security/no-eval':
        violations.push(...this.checkNoEval(rule, lines, filePath));
        break;
      case 'security/no-hardcoded-secrets':
        violations.push(...this.checkNoHardcodedSecrets(rule, lines, filePath));
        break;
    }

    return violations;
  }

  /**
   * Check camelCase naming
   */
  private checkCamelCase(rule: CodingRule, lines: string[], filePath: string): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const varPattern = /(?:let|const|var)\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*[=:]/g;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      let match;

      while ((match = varPattern.exec(line)) !== null) {
        const name = match[1];
        
        // Skip UPPER_CASE (constants) and PascalCase (classes/types)
        if (NAMING_PATTERNS.UPPER_CASE.test(name) || NAMING_PATTERNS.PascalCase.test(name)) {
          continue;
        }

        if (!NAMING_PATTERNS.camelCase.test(name) && !name.startsWith('_')) {
          violations.push({
            ruleId: rule.id,
            ruleName: rule.name,
            severity: rule.severity,
            message: `Variable '${name}' should use camelCase`,
            file: filePath,
            line: i + 1,
            column: match.index + 1,
            autoFixable: false,
          });
        }
      }
    }

    return violations;
  }

  /**
   * Check PascalCase for classes
   */
  private checkPascalCaseClass(rule: CodingRule, lines: string[], filePath: string): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const classPattern = /class\s+([a-zA-Z_$][a-zA-Z0-9_$]*)/g;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      let match;

      while ((match = classPattern.exec(line)) !== null) {
        const name = match[1];
        
        if (!NAMING_PATTERNS.PascalCase.test(name)) {
          violations.push({
            ruleId: rule.id,
            ruleName: rule.name,
            severity: rule.severity,
            message: `Class '${name}' should use PascalCase`,
            file: filePath,
            line: i + 1,
            column: match.index + 1,
            autoFixable: false,
          });
        }
      }
    }

    return violations;
  }

  /**
   * Check UPPER_CASE for constants
   */
  private checkUpperCaseConstants(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const constPattern = /const\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*=/g;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      // Skip if inside a function/block (module-level constants only)
      if (line.match(/^\s{2,}/)) continue;

      let match;
      while ((match = constPattern.exec(line)) !== null) {
        const name = match[1];
        
        // Check if it's a primitive constant (not object/array/function)
        const valueStart = line.indexOf('=', match.index) + 1;
        const valuePart = line.slice(valueStart).trim();
        
        // Skip if it's an object, array, or function
        if (valuePart.startsWith('{') || valuePart.startsWith('[') || 
            valuePart.startsWith('function') || valuePart.includes('=>')) {
          continue;
        }

        // Only flag if it looks like a constant (primitive value)
        if (valuePart.match(/^['"`]|^\d|^true|^false|^null/)) {
          if (!NAMING_PATTERNS.UPPER_CASE.test(name) && !NAMING_PATTERNS.PascalCase.test(name)) {
            violations.push({
              ruleId: rule.id,
              ruleName: rule.name,
              severity: rule.severity,
              message: `Module-level constant '${name}' should use UPPER_CASE`,
              file: filePath,
              line: i + 1,
              column: match.index + 1,
              suggestion: name.replace(/([a-z])([A-Z])/g, '$1_$2').toUpperCase(),
              autoFixable: false,
            });
          }
        }
      }
    }

    return violations;
  }

  /**
   * Check meaningful names
   */
  private checkMeaningfulNames(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const namePattern = /(?:let|const|var|function)\s+([a-zA-Z_$][a-zA-Z0-9_$]*)/g;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      let match;

      while ((match = namePattern.exec(line)) !== null) {
        const name = match[1];
        
        // Skip if it's a known exception
        if (SHORT_NAME_EXCEPTIONS.has(name.toLowerCase())) continue;
        
        // Flag very short names (1-2 chars)
        if (name.length <= 2) {
          violations.push({
            ruleId: rule.id,
            ruleName: rule.name,
            severity: rule.severity,
            message: `Name '${name}' is too short, use a more descriptive name`,
            file: filePath,
            line: i + 1,
            column: match.index + 1,
            autoFixable: false,
          });
        }
      }
    }

    return violations;
  }

  /**
   * Check max line length
   */
  private checkMaxLineLength(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const maxLength = (rule.options?.maxLength as number) ?? 100;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      if (line.length > maxLength) {
        violations.push({
          ruleId: rule.id,
          ruleName: rule.name,
          severity: rule.severity,
          message: `Line exceeds ${maxLength} characters (${line.length})`,
          file: filePath,
          line: i + 1,
          column: maxLength + 1,
          autoFixable: false,
        });
      }
    }

    return violations;
  }

  /**
   * Check indentation
   */
  private checkIndentation(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const size = (rule.options?.size as number) ?? 2;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (!line.trim()) continue;  // Skip empty lines

      const leadingSpaces = line.match(/^(\s*)/)?.[1] ?? '';
      
      // Check for tabs
      if (leadingSpaces.includes('\t')) {
        violations.push({
          ruleId: rule.id,
          ruleName: rule.name,
          severity: rule.severity,
          message: 'Use spaces instead of tabs for indentation',
          file: filePath,
          line: i + 1,
          column: 1,
          autoFixable: true,
        });
        continue;
      }

      // Check indentation is multiple of size
      if (leadingSpaces.length % size !== 0) {
        violations.push({
          ruleId: rule.id,
          ruleName: rule.name,
          severity: rule.severity,
          message: `Indentation should be a multiple of ${size} spaces`,
          file: filePath,
          line: i + 1,
          column: 1,
          autoFixable: true,
        });
      }
    }

    return violations;
  }

  /**
   * Check max file lines
   */
  private checkMaxFileLines(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const maxLines = (rule.options?.maxLines as number) ?? 500;

    if (lines.length > maxLines) {
      violations.push({
        ruleId: rule.id,
        ruleName: rule.name,
        severity: rule.severity,
        message: `File has ${lines.length} lines, exceeds maximum of ${maxLines}`,
        file: filePath,
        line: 1,
        column: 1,
        suggestion: 'Consider splitting into multiple files',
        autoFixable: false,
      });
    }

    return violations;
  }

  /**
   * Check max function lines
   */
  private checkMaxFunctionLines(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const maxLines = (rule.options?.maxLines as number) ?? 50;
    const funcPattern = /(?:function\s+(\w+)|(?:const|let|var)\s+(\w+)\s*=\s*(?:async\s+)?(?:function|\())/;

    let funcStart = -1;
    let funcName = '';
    let braceCount = 0;
    let inFunction = false;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];

      if (!inFunction) {
        const match = line.match(funcPattern);
        if (match) {
          funcName = match[1] || match[2];
          funcStart = i;
          inFunction = true;
          braceCount = 0;
        }
      }

      if (inFunction) {
        braceCount += (line.match(/{/g) || []).length;
        braceCount -= (line.match(/}/g) || []).length;

        if (braceCount === 0 && funcStart >= 0) {
          const funcLines = i - funcStart + 1;
          if (funcLines > maxLines) {
            violations.push({
              ruleId: rule.id,
              ruleName: rule.name,
              severity: rule.severity,
              message: `Function '${funcName}' has ${funcLines} lines, exceeds maximum of ${maxLines}`,
              file: filePath,
              line: funcStart + 1,
              column: 1,
              suggestion: 'Consider breaking into smaller functions',
              autoFixable: false,
            });
          }
          inFunction = false;
          funcStart = -1;
        }
      }
    }

    return violations;
  }

  /**
   * Check max parameters
   */
  private checkMaxParameters(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const maxParams = (rule.options?.maxParams as number) ?? 5;
    const funcPattern = /(?:function\s+(\w+)|(?:const|let|var)\s+(\w+)\s*=\s*(?:async\s+)?function)\s*\(([^)]*)\)/g;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      let match;

      while ((match = funcPattern.exec(line)) !== null) {
        const funcName = match[1] || match[2];
        const params = match[3].split(',').filter((p) => p.trim());

        if (params.length > maxParams) {
          violations.push({
            ruleId: rule.id,
            ruleName: rule.name,
            severity: rule.severity,
            message: `Function '${funcName}' has ${params.length} parameters, exceeds maximum of ${maxParams}`,
            file: filePath,
            line: i + 1,
            column: match.index + 1,
            suggestion: 'Consider using an options object',
            autoFixable: false,
          });
        }
      }
    }

    return violations;
  }

  /**
   * Check JSDoc required
   */
  private checkJSDocRequired(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const exportPattern = /^export\s+(?:async\s+)?(?:function|class|const|interface|type)/;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];

      if (exportPattern.test(line.trim())) {
        // Check if previous lines have JSDoc
        let hasJSDoc = false;
        for (let j = i - 1; j >= 0 && j >= i - 10; j--) {
          const prevLine = lines[j].trim();
          if (prevLine === '*/') {
            hasJSDoc = true;
            break;
          }
          if (prevLine && !prevLine.startsWith('*') && !prevLine.startsWith('//')) {
            break;
          }
        }

        if (!hasJSDoc) {
          violations.push({
            ruleId: rule.id,
            ruleName: rule.name,
            severity: rule.severity,
            message: 'Exported member should have JSDoc documentation',
            file: filePath,
            line: i + 1,
            column: 1,
            autoFixable: false,
          });
        }
      }
    }

    return violations;
  }

  /**
   * Check cyclomatic complexity
   */
  private checkCyclomaticComplexity(
    rule: CodingRule,
    content: string,
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const maxComplexity = (rule.options?.maxComplexity as number) ?? 10;

    // Count complexity indicators
    const complexityPatterns = [
      /\bif\b/g,
      /\belse\s+if\b/g,
      /\bfor\b/g,
      /\bwhile\b/g,
      /\bcase\b/g,
      /\bcatch\b/g,
      /\b\?\s*[^:]/g,  // Ternary
      /&&/g,
      /\|\|/g,
    ];

    let complexity = 1;  // Base complexity
    for (const pattern of complexityPatterns) {
      const matches = content.match(pattern);
      if (matches) {
        complexity += matches.length;
      }
    }

    if (complexity > maxComplexity) {
      violations.push({
        ruleId: rule.id,
        ruleName: rule.name,
        severity: rule.severity,
        message: `File cyclomatic complexity is ${complexity}, exceeds maximum of ${maxComplexity}`,
        file: filePath,
        line: 1,
        column: 1,
        suggestion: 'Consider refactoring to reduce complexity',
        autoFixable: false,
      });
    }

    return violations;
  }

  /**
   * Check max nesting level
   */
  private checkMaxNesting(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const maxNesting = (rule.options?.maxNesting as number) ?? 4;

    let currentNesting = 0;
    let maxFound = 0;
    let maxFoundLine = 0;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      // Count braces
      const opens = (line.match(/{/g) || []).length;
      const closes = (line.match(/}/g) || []).length;

      currentNesting += opens;
      
      if (currentNesting > maxFound) {
        maxFound = currentNesting;
        maxFoundLine = i + 1;
      }

      currentNesting -= closes;
    }

    if (maxFound > maxNesting) {
      violations.push({
        ruleId: rule.id,
        ruleName: rule.name,
        severity: rule.severity,
        message: `Nesting level is ${maxFound}, exceeds maximum of ${maxNesting}`,
        file: filePath,
        line: maxFoundLine,
        column: 1,
        suggestion: 'Consider extracting nested code to separate functions',
        autoFixable: false,
      });
    }

    return violations;
  }

  /**
   * Check for eval usage
   */
  private checkNoEval(rule: CodingRule, lines: string[], filePath: string): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const evalPattern = /\beval\s*\(/g;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      let match;

      while ((match = evalPattern.exec(line)) !== null) {
        violations.push({
          ruleId: rule.id,
          ruleName: rule.name,
          severity: rule.severity,
          message: 'Avoid using eval() - it poses security risks',
          file: filePath,
          line: i + 1,
          column: match.index + 1,
          autoFixable: false,
        });
      }
    }

    return violations;
  }

  /**
   * Check for hardcoded secrets
   */
  private checkNoHardcodedSecrets(
    rule: CodingRule,
    lines: string[],
    filePath: string
  ): RuleViolation[] {
    const violations: RuleViolation[] = [];
    const secretPatterns = [
      /(?:password|passwd|pwd)\s*[:=]\s*['"][^'"]+['"]/gi,
      /(?:api[_-]?key|apikey)\s*[:=]\s*['"][^'"]+['"]/gi,
      /(?:secret|token)\s*[:=]\s*['"][^'"]{8,}['"]/gi,
      /(?:private[_-]?key)\s*[:=]\s*['"][^'"]+['"]/gi,
    ];

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      // Skip comments
      if (line.trim().startsWith('//') || line.trim().startsWith('*')) continue;

      for (const pattern of secretPatterns) {
        const match = line.match(pattern);
        if (match) {
          violations.push({
            ruleId: rule.id,
            ruleName: rule.name,
            severity: rule.severity,
            message: 'Potential hardcoded secret detected',
            file: filePath,
            line: i + 1,
            column: line.indexOf(match[0]) + 1,
            suggestion: 'Use environment variables or secure vault for secrets',
            autoFixable: false,
          });
          break;  // One violation per line
        }
      }
    }

    return violations;
  }

  /**
   * Check if severity should be reported
   */
  private shouldReport(severity: Severity): boolean {
    const levels: Severity[] = ['error', 'warning', 'info', 'hint'];
    const minLevel = levels.indexOf(this.config.minSeverity);
    const currentLevel = levels.indexOf(severity);
    return currentLevel <= minLevel;
  }

  /**
   * Check if file should be ignored
   */
  private shouldIgnore(filePath: string): boolean {
    for (const pattern of this.config.ignorePatterns) {
      const regex = new RegExp(pattern.replace(/\*\*/g, '.*').replace(/\*/g, '[^/]*'));
      if (regex.test(filePath)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Get enabled rules
   */
  getEnabledRules(): CodingRule[] {
    return Array.from(this.rules.values()).filter((r) => r.enabled);
  }

  /**
   * Enable/disable rule
   */
  setRuleEnabled(ruleId: string, enabled: boolean): void {
    const rule = this.rules.get(ruleId);
    if (rule) {
      rule.enabled = enabled;
    }
  }

  /**
   * Add custom rule
   */
  addRule(rule: CodingRule): void {
    this.rules.set(rule.id, rule);
  }

  /**
   * Format report as string
   */
  formatReport(report: StandardsReport): string {
    const lines: string[] = [];

    lines.push('# Coding Standards Report');
    lines.push('');
    lines.push(`**Generated:** ${report.timestamp.toISOString()}`);
    lines.push(`**Duration:** ${report.duration}ms`);
    lines.push('');

    // Summary
    lines.push('## Summary');
    lines.push('');
    lines.push(`| Metric | Value |`);
    lines.push(`|--------|-------|`);
    lines.push(`| Files Checked | ${report.filesChecked} |`);
    lines.push(`| Files Passed | ${report.filesPassed} |`);
    lines.push(`| Files Failed | ${report.filesFailed} |`);
    lines.push(`| Pass Rate | ${(report.passRate * 100).toFixed(1)}% |`);
    lines.push(`| Total Violations | ${report.totalViolations} |`);
    lines.push('');

    // By severity
    lines.push('### By Severity');
    lines.push('');
    lines.push(`- 🔴 Errors: ${report.bySeverity.error}`);
    lines.push(`- 🟡 Warnings: ${report.bySeverity.warning}`);
    lines.push(`- 🔵 Info: ${report.bySeverity.info}`);
    lines.push('');

    // Violations
    if (report.totalViolations > 0) {
      lines.push('## Violations');
      lines.push('');

      for (const result of report.results) {
        if (result.violations.length === 0) continue;

        lines.push(`### ${result.file}`);
        lines.push('');

        for (const v of result.violations) {
          const icon = v.severity === 'error' ? '🔴' : v.severity === 'warning' ? '🟡' : '🔵';
          lines.push(`${icon} Line ${v.line}: ${v.message}`);
          if (v.suggestion) {
            lines.push(`   💡 ${v.suggestion}`);
          }
        }
        lines.push('');
      }
    }

    return lines.join('\n');
  }
}

/**
 * Create coding standards checker instance
 */
export function createCodingStandardsChecker(
  config?: Partial<CodingStandardsConfig>
): CodingStandardsChecker {
  return new CodingStandardsChecker(config);
}
