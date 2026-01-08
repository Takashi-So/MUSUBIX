/**
 * @fileoverview CWE-306: Missing Authentication for Critical Function
 * @module @nahisaho/musubix-security/rules/cwe/cwe-306-missing-auth-critical
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe306MissingAuthCritical: SecurityRule = {
  id: 'cwe-306-missing-auth-critical',
  name: 'CWE-306: Missing Authentication for Critical Function',
  description: 'Detects critical functions without authentication',
  defaultSeverity: 'critical',
  category: 'authentication',
  tags: ['cwe', 'authentication', 'critical', 'security'],
  cwe: ['306'],
  owasp: ['A07:2021'],
  references: [
    { title: 'CWE-306', url: 'https://cwe.mitre.org/data/definitions/306.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /app\.(post|put|delete)\s*\(\s*['"`]\/admin/gi, type: 'Admin route without auth middleware', severity: 'critical' as const },
      { pattern: /app\.(post|put|delete)\s*\(\s*['"`]\/api\/.*(?:delete|update|create)/gi, type: 'Critical API without auth', severity: 'high' as const },
      { pattern: /router\.(post|put|delete)\s*\(\s*['"`]\//gi, type: 'State-changing route', severity: 'medium' as const },
      { pattern: /\.destroy\s*\(\s*\)|\bdelete\s*\(/gi, type: 'Destructive operation', severity: 'medium' as const },
      { pattern: /password.*reset|reset.*password/gi, type: 'Password reset function', severity: 'high' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-306-${findings.length + 1}`,
            ruleId: 'cwe-306-missing-auth-critical',
            severity,
            message: `Missing Auth - ${type}: Add authentication middleware`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['306'],
            owasp: ['A07:2021'],
            suggestion: {
              description: 'Add authentication middleware',
              example: `// Add auth middleware
app.delete('/admin/user/:id', authMiddleware, adminOnly, handler);`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe306MissingAuthCritical;
