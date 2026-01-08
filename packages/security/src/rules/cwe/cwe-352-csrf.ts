/**
 * @fileoverview CWE-352: Cross-Site Request Forgery (CSRF)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-352-csrf
 * @trace TSK-RULE-005
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe352CSRF: SecurityRule = {
  id: 'cwe-352-csrf',
  name: 'CWE-352: Cross-Site Request Forgery',
  description: 'Detects missing CSRF protection patterns',
  defaultSeverity: 'high',
  category: 'session',
  tags: ['cwe', 'csrf', 'session', 'security'],
  cwe: ['352'],
  references: [
    { title: 'CWE-352: CSRF', url: 'https://cwe.mitre.org/data/definitions/352.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /app\.post\s*\(/gi, type: 'POST without CSRF', severity: 'medium' as const },
      { pattern: /app\.put\s*\(/gi, type: 'PUT without CSRF', severity: 'medium' as const },
      { pattern: /app\.delete\s*\(/gi, type: 'DELETE without CSRF', severity: 'medium' as const },
      { pattern: /SameSite\s*:\s*['"`]None['"`]/gi, type: 'SameSite=None cookie', severity: 'high' as const },
      { pattern: /credentials\s*:\s*['"`]include['"`]/gi, type: 'Fetch with credentials', severity: 'low' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-352-${findings.length + 1}`,
            ruleId: 'cwe-352-csrf',
            severity,
            message: `CSRF - ${type}: Ensure CSRF token validation`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['352'],
            suggestion: {
              description: 'Use CSRF middleware',
              example: `const csrf = require('csurf');
app.use(csrf({ cookie: true }));`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe352CSRF;
