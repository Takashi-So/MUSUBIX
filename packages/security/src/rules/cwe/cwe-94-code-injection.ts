/**
 * @fileoverview CWE-94: Improper Control of Generation of Code (Code Injection)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-94-code-injection
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe94CodeInjection: SecurityRule = {
  id: 'cwe-94-code-injection',
  name: 'CWE-94: Code Injection',
  description: 'Detects code injection through dynamic code generation',
  defaultSeverity: 'critical',
  category: 'injection',
  tags: ['cwe', 'code-injection', 'rce', 'security'],
  cwe: ['94'],
  owasp: ['A03:2021'],
  references: [
    { title: 'CWE-94', url: 'https://cwe.mitre.org/data/definitions/94.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /eval\s*\(/gi, type: 'eval() usage', severity: 'critical' as const },
      { pattern: /new\s+Function\s*\(/gi, type: 'new Function() usage', severity: 'critical' as const },
      { pattern: /setTimeout\s*\(\s*['"`]/gi, type: 'setTimeout with string', severity: 'high' as const },
      { pattern: /setInterval\s*\(\s*['"`]/gi, type: 'setInterval with string', severity: 'high' as const },
      { pattern: /vm\.runInContext\s*\(/gi, type: 'vm.runInContext', severity: 'high' as const },
      { pattern: /vm\.runInNewContext\s*\(/gi, type: 'vm.runInNewContext', severity: 'high' as const },
      { pattern: /require\s*\(\s*\w+\s*\)/gi, type: 'Dynamic require', severity: 'high' as const },
      { pattern: /import\s*\(\s*\w+\s*\)/gi, type: 'Dynamic import', severity: 'medium' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-94-${findings.length + 1}`,
            ruleId: 'cwe-94-code-injection',
            severity,
            message: `Code Injection - ${type}: Avoid dynamic code execution`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['94'],
            owasp: ['A03:2021'],
            suggestion: {
              description: 'Use safe alternatives to dynamic code execution',
              example: `// Instead of eval, use safe alternatives
// Bad: eval(userCode)
// Good: Use a sandboxed environment or predefined functions
const allowedOps = { add: (a, b) => a + b };
const result = allowedOps[operation]?.(a, b);`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe94CodeInjection;
