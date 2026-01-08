/**
 * @fileoverview CWE-77: Improper Neutralization of Special Elements (Command Injection)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-77-command-injection
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe77CommandInjection: SecurityRule = {
  id: 'cwe-77-command-injection',
  name: 'CWE-77: Command Injection',
  description: 'Detects command injection via special element neutralization issues',
  defaultSeverity: 'critical',
  category: 'injection',
  tags: ['cwe', 'command', 'injection', 'security'],
  cwe: ['77'],
  owasp: ['A03:2021'],
  references: [
    { title: 'CWE-77', url: 'https://cwe.mitre.org/data/definitions/77.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /child_process.*exec\s*\(/gi, type: 'child_process.exec', severity: 'critical' as const },
      { pattern: /execSync\s*\(\s*`/gi, type: 'execSync with template', severity: 'critical' as const },
      { pattern: /spawn\s*\([^,]+\+/gi, type: 'spawn with concatenation', severity: 'high' as const },
      { pattern: /system\s*\(\s*\$/gi, type: 'system() with variable', severity: 'critical' as const },
      { pattern: /popen\s*\(/gi, type: 'popen function', severity: 'high' as const },
      { pattern: /\$\{.*\}.*\|\s*sh/gi, type: 'Shell pipe with variable', severity: 'critical' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-77-${findings.length + 1}`,
            ruleId: 'cwe-77-command-injection',
            severity,
            message: `Command Injection - ${type}: Sanitize command arguments`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['77'],
            owasp: ['A03:2021'],
            suggestion: {
              description: 'Use spawn with array arguments instead of exec',
              example: `// Safe: use spawn with array
const { spawn } = require('child_process');
spawn('command', [arg1, arg2], { shell: false });`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe77CommandInjection;
