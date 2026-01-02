/**
 * Static Analyzer
 * 
 * Performs static code analysis
 * 
 * @packageDocumentation
 * @module codegen/static-analyzer
 * 
 * @see REQ-COD-002 - Static Analysis
 * @see Article V - Code Quality Standards
 */

/**
 * Issue severity
 */
export type IssueSeverity = 'error' | 'warning' | 'info' | 'hint';

/**
 * Issue category
 */
export type IssueCategory =
  | 'syntax'
  | 'type'
  | 'style'
  | 'complexity'
  | 'maintainability'
  | 'performance'
  | 'security'
  | 'best-practice'
  | 'deprecated';

/**
 * Code issue
 */
export interface CodeIssue {
  /** Issue ID */
  id: string;
  /** Rule ID */
  ruleId: string;
  /** Severity */
  severity: IssueSeverity;
  /** Category */
  category: IssueCategory;
  /** Message */
  message: string;
  /** File path */
  file?: string;
  /** Line number */
  line?: number;
  /** Column */
  column?: number;
  /** End line */
  endLine?: number;
  /** End column */
  endColumn?: number;
  /** Code snippet */
  snippet?: string;
  /** Fix suggestion */
  fix?: CodeFix;
}

/**
 * Code fix
 */
export interface CodeFix {
  /** Fix description */
  description: string;
  /** Replacement text */
  replacement: string;
  /** Range to replace */
  range: {
    start: { line: number; column: number };
    end: { line: number; column: number };
  };
}

/**
 * Analysis result
 */
export interface AnalysisResult {
  /** File analyzed */
  file: string;
  /** Issues found */
  issues: CodeIssue[];
  /** Analysis time */
  analysisTime: number;
  /** Summary */
  summary: AnalysisSummary;
}

/**
 * Analysis summary
 */
export interface AnalysisSummary {
  /** Total issues */
  totalIssues: number;
  /** By severity */
  bySeverity: Record<IssueSeverity, number>;
  /** By category */
  byCategory: Record<IssueCategory, number>;
  /** Pass/fail */
  passed: boolean;
}

/**
 * Analysis rule
 */
export interface AnalysisRule {
  /** Rule ID */
  id: string;
  /** Rule name */
  name: string;
  /** Category */
  category: IssueCategory;
  /** Default severity */
  severity: IssueSeverity;
  /** Description */
  description: string;
  /** Detection function */
  detect: (code: string, context: AnalysisContext) => CodeIssue[];
  /** Is enabled */
  enabled: boolean;
}

/**
 * Analysis context
 */
export interface AnalysisContext {
  /** File path */
  file: string;
  /** Language */
  language: string;
  /** Options */
  options: StaticAnalyzerConfig;
}

/**
 * Static analyzer configuration
 */
export interface StaticAnalyzerConfig {
  /** Max errors to report */
  maxErrors: number;
  /** Severity threshold */
  severityThreshold: IssueSeverity;
  /** Categories to check */
  categories: IssueCategory[];
  /** Custom rules */
  customRules?: AnalysisRule[];
  /** Ignore patterns */
  ignorePatterns?: string[];
}

/**
 * Default configuration
 */
export const DEFAULT_ANALYZER_CONFIG: StaticAnalyzerConfig = {
  maxErrors: 100,
  severityThreshold: 'warning',
  categories: [
    'syntax',
    'type',
    'style',
    'complexity',
    'maintainability',
    'performance',
    'security',
    'best-practice',
  ],
};

/**
 * Built-in rules
 */
const BUILTIN_RULES: AnalysisRule[] = [
  {
    id: 'no-console',
    name: 'No console statements',
    category: 'best-practice',
    severity: 'warning',
    description: 'Disallow console statements in production code',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const regex = /console\.(log|warn|error|info|debug)\s*\(/g;
      let match;
      const lines = code.split('\n');

      while ((match = regex.exec(code)) !== null) {
        const line = code.substring(0, match.index).split('\n').length;
        issues.push({
          id: `${context.file}:${line}:no-console`,
          ruleId: 'no-console',
          severity: 'warning',
          category: 'best-practice',
          message: `Unexpected console.${match[1]} statement`,
          file: context.file,
          line,
          snippet: lines[line - 1]?.trim(),
        });
      }
      return issues;
    },
  },
  {
    id: 'no-debugger',
    name: 'No debugger statements',
    category: 'best-practice',
    severity: 'error',
    description: 'Disallow debugger statements',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const regex = /\bdebugger\b/g;
      let match;

      while ((match = regex.exec(code)) !== null) {
        const line = code.substring(0, match.index).split('\n').length;
        issues.push({
          id: `${context.file}:${line}:no-debugger`,
          ruleId: 'no-debugger',
          severity: 'error',
          category: 'best-practice',
          message: 'Unexpected debugger statement',
          file: context.file,
          line,
        });
      }
      return issues;
    },
  },
  {
    id: 'no-var',
    name: 'No var declarations',
    category: 'style',
    severity: 'warning',
    description: 'Require let or const instead of var',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const regex = /\bvar\s+\w+/g;
      let match;

      while ((match = regex.exec(code)) !== null) {
        const line = code.substring(0, match.index).split('\n').length;
        issues.push({
          id: `${context.file}:${line}:no-var`,
          ruleId: 'no-var',
          severity: 'warning',
          category: 'style',
          message: 'Unexpected var, use let or const instead',
          file: context.file,
          line,
          fix: {
            description: 'Replace var with const',
            replacement: match[0].replace('var', 'const'),
            range: {
              start: { line, column: 0 },
              end: { line, column: match[0].length },
            },
          },
        });
      }
      return issues;
    },
  },
  {
    id: 'no-any',
    name: 'No explicit any',
    category: 'type',
    severity: 'warning',
    description: 'Disallow explicit any type',
    enabled: true,
    detect: (code, context) => {
      if (context.language !== 'typescript') return [];
      
      const issues: CodeIssue[] = [];
      const regex = /:\s*any\b/g;
      let match;

      while ((match = regex.exec(code)) !== null) {
        const line = code.substring(0, match.index).split('\n').length;
        issues.push({
          id: `${context.file}:${line}:no-any`,
          ruleId: 'no-any',
          severity: 'warning',
          category: 'type',
          message: 'Unexpected any type, specify a more precise type',
          file: context.file,
          line,
        });
      }
      return issues;
    },
  },
  {
    id: 'max-lines',
    name: 'Maximum file lines',
    category: 'maintainability',
    severity: 'warning',
    description: 'Enforce a maximum number of lines per file',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const lines = code.split('\n').length;
      const maxLines = 500;

      if (lines > maxLines) {
        issues.push({
          id: `${context.file}:max-lines`,
          ruleId: 'max-lines',
          severity: 'warning',
          category: 'maintainability',
          message: `File has ${lines} lines, exceeds maximum of ${maxLines}`,
          file: context.file,
          line: maxLines,
        });
      }
      return issues;
    },
  },
  {
    id: 'max-line-length',
    name: 'Maximum line length',
    category: 'style',
    severity: 'info',
    description: 'Enforce a maximum line length',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const maxLength = 120;
      const lines = code.split('\n');

      lines.forEach((line, index) => {
        if (line.length > maxLength) {
          issues.push({
            id: `${context.file}:${index + 1}:max-line-length`,
            ruleId: 'max-line-length',
            severity: 'info',
            category: 'style',
            message: `Line ${index + 1} exceeds ${maxLength} characters (${line.length})`,
            file: context.file,
            line: index + 1,
          });
        }
      });
      return issues;
    },
  },
  {
    id: 'complexity',
    name: 'Cyclomatic complexity',
    category: 'complexity',
    severity: 'warning',
    description: 'Enforce a maximum cyclomatic complexity',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const maxComplexity = 10;
      
      // Simple complexity estimation based on control flow keywords
      const functionRegex = /(?:function\s+\w+|(?:async\s+)?(?:\w+)\s*(?:=|:)\s*(?:async\s+)?(?:function|\([^)]*\)\s*=>))/g;
      let funcMatch;
      
      while ((funcMatch = functionRegex.exec(code)) !== null) {
        const startIndex = funcMatch.index;
        const line = code.substring(0, startIndex).split('\n').length;
        
        // Find function body (simple heuristic)
        let braceCount = 0;
        let endIndex = startIndex;
        let started = false;
        
        for (let i = startIndex; i < code.length; i++) {
          if (code[i] === '{') {
            braceCount++;
            started = true;
          } else if (code[i] === '}') {
            braceCount--;
            if (started && braceCount === 0) {
              endIndex = i;
              break;
            }
          }
        }
        
        const funcBody = code.substring(startIndex, endIndex);
        
        // Count complexity indicators
        let complexity = 1;
        const keywords = ['if', 'else', 'for', 'while', 'case', 'catch', '\\?', '&&', '\\|\\|'];
        for (const kw of keywords) {
          const matches = funcBody.match(new RegExp(`\\b${kw}\\b`, 'g'));
          complexity += matches?.length ?? 0;
        }
        
        if (complexity > maxComplexity) {
          issues.push({
            id: `${context.file}:${line}:complexity`,
            ruleId: 'complexity',
            severity: 'warning',
            category: 'complexity',
            message: `Function has complexity of ${complexity}, exceeds maximum of ${maxComplexity}`,
            file: context.file,
            line,
          });
        }
      }
      return issues;
    },
  },
  {
    id: 'no-eval',
    name: 'No eval',
    category: 'security',
    severity: 'error',
    description: 'Disallow eval() and similar constructs',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const regex = /\beval\s*\(|\bnew\s+Function\s*\(/g;
      let match;

      while ((match = regex.exec(code)) !== null) {
        const line = code.substring(0, match.index).split('\n').length;
        issues.push({
          id: `${context.file}:${line}:no-eval`,
          ruleId: 'no-eval',
          severity: 'error',
          category: 'security',
          message: 'eval() or Function() is a security risk',
          file: context.file,
          line,
        });
      }
      return issues;
    },
  },
  {
    id: 'no-unused-vars',
    name: 'No unused variables',
    category: 'maintainability',
    severity: 'warning',
    description: 'Disallow unused variables',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      
      // Simple unused variable detection
      const declarations = code.matchAll(/(?:const|let|var)\s+(\w+)(?:\s*:\s*[^=]+)?\s*=/g);
      
      for (const match of declarations) {
        const varName = match[1];
        // Skip if variable name starts with underscore (intentionally unused)
        if (varName.startsWith('_')) continue;
        
        // Check if used elsewhere (simple check)
        const usageRegex = new RegExp(`\\b${varName}\\b`, 'g');
        const usages = code.match(usageRegex);
        
        // If only appears once (the declaration), it's unused
        if (usages && usages.length === 1) {
          const line = code.substring(0, match.index).split('\n').length;
          issues.push({
            id: `${context.file}:${line}:no-unused-vars`,
            ruleId: 'no-unused-vars',
            severity: 'warning',
            category: 'maintainability',
            message: `'${varName}' is declared but never used`,
            file: context.file,
            line,
          });
        }
      }
      return issues;
    },
  },
  {
    id: 'prefer-const',
    name: 'Prefer const',
    category: 'style',
    severity: 'info',
    description: 'Prefer const over let when variable is not reassigned',
    enabled: true,
    detect: (code, context) => {
      const issues: CodeIssue[] = [];
      const letDeclarations = code.matchAll(/\blet\s+(\w+)/g);
      
      for (const match of letDeclarations) {
        const varName = match[1];
        const afterDecl = code.substring((match.index ?? 0) + match[0].length);
        
        // Check if variable is reassigned
        const reassignRegex = new RegExp(`\\b${varName}\\s*=(?!=)`, 'g');
        const reassignments = afterDecl.match(reassignRegex);
        
        if (!reassignments || reassignments.length === 0) {
          const line = code.substring(0, match.index).split('\n').length;
          issues.push({
            id: `${context.file}:${line}:prefer-const`,
            ruleId: 'prefer-const',
            severity: 'info',
            category: 'style',
            message: `'${varName}' is never reassigned, use const instead`,
            file: context.file,
            line,
            fix: {
              description: 'Replace let with const',
              replacement: `const ${varName}`,
              range: {
                start: { line, column: 0 },
                end: { line, column: match[0].length },
              },
            },
          });
        }
      }
      return issues;
    },
  },
];

/**
 * Static Analyzer
 */
export class StaticAnalyzer {
  private config: StaticAnalyzerConfig;
  private rules: AnalysisRule[];

  constructor(config?: Partial<StaticAnalyzerConfig>) {
    this.config = { ...DEFAULT_ANALYZER_CONFIG, ...config };
    this.rules = [...BUILTIN_RULES];
    
    // Add custom rules
    if (this.config.customRules) {
      this.rules.push(...this.config.customRules);
    }
  }

  /**
   * Analyze code
   */
  analyze(code: string, file: string, language = 'typescript'): AnalysisResult {
    const startTime = Date.now();
    const issues: CodeIssue[] = [];

    const context: AnalysisContext = {
      file,
      language,
      options: this.config,
    };

    // Run enabled rules
    for (const rule of this.rules) {
      if (!rule.enabled) continue;
      if (!this.config.categories.includes(rule.category)) continue;

      try {
        const ruleIssues = rule.detect(code, context);
        issues.push(...ruleIssues);
      } catch (error) {
        // Rule failed, continue with others
        console.warn(`Rule ${rule.id} failed:`, error);
      }
    }

    // Filter by severity threshold
    const filteredIssues = this.filterBySeverity(issues);

    // Limit to max errors
    const limitedIssues = filteredIssues.slice(0, this.config.maxErrors);

    const analysisTime = Date.now() - startTime;
    const summary = this.createSummary(limitedIssues);

    return {
      file,
      issues: limitedIssues,
      analysisTime,
      summary,
    };
  }

  /**
   * Analyze multiple files
   */
  analyzeFiles(
    files: Array<{ path: string; content: string; language?: string }>
  ): AnalysisResult[] {
    return files.map((f) => this.analyze(f.content, f.path, f.language));
  }

  /**
   * Filter issues by severity threshold
   */
  private filterBySeverity(issues: CodeIssue[]): CodeIssue[] {
    const severityOrder: IssueSeverity[] = ['error', 'warning', 'info', 'hint'];
    const thresholdIndex = severityOrder.indexOf(this.config.severityThreshold);

    return issues.filter((issue) => {
      const issueIndex = severityOrder.indexOf(issue.severity);
      return issueIndex <= thresholdIndex;
    });
  }

  /**
   * Create analysis summary
   */
  private createSummary(issues: CodeIssue[]): AnalysisSummary {
    const bySeverity: Record<IssueSeverity, number> = {
      error: 0,
      warning: 0,
      info: 0,
      hint: 0,
    };

    const byCategory: Record<IssueCategory, number> = {
      syntax: 0,
      type: 0,
      style: 0,
      complexity: 0,
      maintainability: 0,
      performance: 0,
      security: 0,
      'best-practice': 0,
      deprecated: 0,
    };

    for (const issue of issues) {
      bySeverity[issue.severity]++;
      byCategory[issue.category]++;
    }

    return {
      totalIssues: issues.length,
      bySeverity,
      byCategory,
      passed: bySeverity.error === 0,
    };
  }

  /**
   * Get available rules
   */
  getRules(): AnalysisRule[] {
    return [...this.rules];
  }

  /**
   * Enable/disable rule
   */
  setRuleEnabled(ruleId: string, enabled: boolean): void {
    const rule = this.rules.find((r) => r.id === ruleId);
    if (rule) {
      rule.enabled = enabled;
    }
  }

  /**
   * Add custom rule
   */
  addRule(rule: AnalysisRule): void {
    this.rules.push(rule);
  }
}

/**
 * Create static analyzer instance
 */
export function createStaticAnalyzer(
  config?: Partial<StaticAnalyzerConfig>
): StaticAnalyzer {
  return new StaticAnalyzer(config);
}
