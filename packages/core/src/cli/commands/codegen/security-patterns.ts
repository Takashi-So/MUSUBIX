/**
 * Security Patterns and Analysis Rules
 *
 * Constants and functions for security scanning and static analysis
 *
 * @packageDocumentation
 * @module cli/commands/codegen/security-patterns
 *
 * @see REQ-CG-002 - Static Analysis
 */

import { readFile, readdir } from 'fs/promises';
import { extname, join } from 'path';
import type { AnalysisIssue, SecurityVulnerability } from './types.js';

/**
 * Security patterns to check
 */
export const SECURITY_PATTERNS = [
  {
    pattern: /eval\s*\(/g,
    type: 'Code Injection',
    severity: 'critical' as const,
    cwe: 'CWE-94',
    description: 'Use of eval() can lead to code injection vulnerabilities',
    recommendation: 'Avoid eval(). Use safer alternatives like JSON.parse() for data parsing.',
  },
  {
    pattern: /new\s+Function\s*\(/g,
    type: 'Code Injection',
    severity: 'high' as const,
    cwe: 'CWE-94',
    description: 'Dynamic function creation can lead to code injection',
    recommendation: 'Avoid dynamic function creation. Use predefined functions instead.',
  },
  {
    pattern: /innerHTML\s*=/g,
    type: 'XSS',
    severity: 'high' as const,
    cwe: 'CWE-79',
    description: 'Direct innerHTML assignment can lead to XSS vulnerabilities',
    recommendation: 'Use textContent or sanitize HTML before assignment.',
  },
  {
    pattern: /document\.write\s*\(/g,
    type: 'XSS',
    severity: 'high' as const,
    cwe: 'CWE-79',
    description: 'document.write can be exploited for XSS attacks',
    recommendation: 'Use DOM manipulation methods instead of document.write.',
  },
  {
    pattern: /password\s*[:=]\s*['"][^'"]+['"]/gi,
    type: 'Hardcoded Credentials',
    severity: 'critical' as const,
    cwe: 'CWE-798',
    description: 'Hardcoded passwords detected',
    recommendation: 'Use environment variables or secure credential stores.',
  },
  {
    pattern: /api[_-]?key\s*[:=]\s*['"][^'"]+['"]/gi,
    type: 'Hardcoded Credentials',
    severity: 'high' as const,
    cwe: 'CWE-798',
    description: 'Hardcoded API key detected',
    recommendation: 'Use environment variables for API keys.',
  },
  {
    pattern: /exec\s*\(/g,
    type: 'Command Injection',
    severity: 'high' as const,
    cwe: 'CWE-78',
    description: 'Use of exec() can lead to command injection',
    recommendation: 'Use execFile() or spawn() with explicit arguments.',
  },
  {
    pattern: /dangerouslySetInnerHTML/g,
    type: 'XSS',
    severity: 'medium' as const,
    cwe: 'CWE-79',
    description: 'React dangerouslySetInnerHTML can lead to XSS',
    recommendation: 'Sanitize HTML content before using dangerouslySetInnerHTML.',
  },
  {
    pattern: /\bhttp:\/\//g,
    type: 'Insecure Communication',
    severity: 'medium' as const,
    cwe: 'CWE-319',
    description: 'Use of HTTP instead of HTTPS',
    recommendation: 'Use HTTPS for all external communications.',
  },
  {
    pattern: /Math\.random\(\)/g,
    type: 'Weak Randomness',
    severity: 'low' as const,
    cwe: 'CWE-338',
    description: 'Math.random() is not cryptographically secure',
    recommendation: 'Use crypto.getRandomValues() for security-sensitive randomness.',
  },
];

/**
 * Code analysis rules
 */
export const ANALYSIS_RULES = [
  {
    name: 'no-any',
    pattern: /:\s*any\b/g,
    severity: 'warning' as const,
    message: 'Avoid using "any" type. Use proper types for better type safety.',
  },
  {
    name: 'no-console',
    pattern: /console\.(log|warn|error|info|debug)\s*\(/g,
    severity: 'info' as const,
    message: 'Console statements should be removed in production code.',
  },
  {
    name: 'max-line-length',
    check: (line: string) => line.length > 120,
    severity: 'info' as const,
    message: 'Line exceeds 120 characters.',
  },
  {
    name: 'no-magic-numbers',
    pattern: /[^0-9a-z_]([2-9]|[1-9]\d+)(?=[^0-9]|$)/gi,
    severity: 'info' as const,
    message: 'Avoid magic numbers. Use named constants instead.',
  },
  {
    name: 'prefer-const',
    pattern: /\blet\s+\w+\s*=/g,
    severity: 'info' as const,
    message: 'Consider using const if variable is not reassigned.',
  },
];

/**
 * Analyze file
 */
export function analyzeFile(file: string, lines: string[], issues: AnalysisIssue[]): void {
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];

    for (const rule of ANALYSIS_RULES) {
      if ('pattern' in rule && rule.pattern) {
        rule.pattern.lastIndex = 0;
        if (rule.pattern.test(line)) {
          issues.push({
            file,
            line: i + 1,
            severity: rule.severity,
            rule: rule.name,
            message: rule.message,
          });
        }
      } else if ('check' in rule && rule.check?.(line)) {
        issues.push({
          file,
          line: i + 1,
          severity: rule.severity,
          rule: rule.name,
          message: rule.message,
        });
      }
    }
  }
}

/**
 * Analyze directory
 */
export async function analyzeDirectory(
  dir: string,
  issues: AnalysisIssue[],
  onFile: (lines: number) => void
): Promise<void> {
  const entries = await readdir(dir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = join(dir, entry.name);

    if (entry.isDirectory()) {
      if (!entry.name.startsWith('.') && entry.name !== 'node_modules') {
        await analyzeDirectory(fullPath, issues, onFile);
      }
    } else if (entry.isFile()) {
      const ext = extname(entry.name);
      if (['.ts', '.js', '.tsx', '.jsx', '.py'].includes(ext)) {
        const content = await readFile(fullPath, 'utf-8');
        const lines = content.split('\n');
        analyzeFile(fullPath, lines, issues);
        onFile(lines.length);
      }
    }
  }
}

/**
 * Scan file for security issues
 */
export function scanFile(
  file: string,
  content: string,
  vulnerabilities: SecurityVulnerability[]
): void {
  const lines = content.split('\n');

  for (const pattern of SECURITY_PATTERNS) {
    pattern.pattern.lastIndex = 0;

    for (let i = 0; i < lines.length; i++) {
      pattern.pattern.lastIndex = 0;
      if (pattern.pattern.test(lines[i])) {
        vulnerabilities.push({
          severity: pattern.severity,
          type: pattern.type,
          file,
          line: i + 1,
          description: pattern.description,
          recommendation: pattern.recommendation,
          cwe: pattern.cwe,
        });
      }
    }
  }
}

/**
 * Scan directory for security issues
 */
export async function scanDirectory(
  dir: string,
  vulnerabilities: SecurityVulnerability[]
): Promise<void> {
  const entries = await readdir(dir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = join(dir, entry.name);

    if (entry.isDirectory()) {
      if (!entry.name.startsWith('.') && entry.name !== 'node_modules') {
        await scanDirectory(fullPath, vulnerabilities);
      }
    } else if (entry.isFile()) {
      const ext = extname(entry.name);
      if (['.ts', '.js', '.tsx', '.jsx', '.py', '.json', '.yml', '.yaml'].includes(ext)) {
        const content = await readFile(fullPath, 'utf-8');
        scanFile(fullPath, content, vulnerabilities);
      }
    }
  }
}
