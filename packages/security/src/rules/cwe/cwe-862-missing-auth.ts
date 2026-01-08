/**
 * @fileoverview CWE-862: Missing Authorization
 * @module @nahisaho/musubix-security/rules/cwe/cwe-862-missing-auth
 * @trace TSK-RULE-005
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe862MissingAuth: SecurityRule = {
  id: 'cwe-862-missing-auth',
  name: 'CWE-862: Missing Authorization',
  description: 'Detects missing authorization checks',
  defaultSeverity: 'high',
  category: 'access-control',
  tags: ['cwe', 'authorization', 'access-control', 'security'],
  owasp: ['A01:2021'],
  cwe: ['862'],
  references: [
    { title: 'CWE-862', url: 'https://cwe.mitre.org/data/definitions/862.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /app\.(?:get|post|put|delete)\s*\(\s*['"`]\/admin/gi, type: 'Admin route', severity: 'high' as const },
      { pattern: /\.findByIdAndUpdate\s*\(\s*req\.params/gi, type: 'Direct ID update', severity: 'high' as const },
      { pattern: /\.findByIdAndDelete\s*\(\s*req\.params/gi, type: 'Direct ID delete', severity: 'high' as const },
      { pattern: /\.destroy\s*\(\s*\{\s*where\s*:\s*\{\s*id\s*:\s*req\.params/gi, type: 'Direct destroy', severity: 'high' as const },
      { pattern: /req\.user\.id\s*!==?\s*req\.params\.id/gi, type: 'Ownership check found', severity: 'info' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-862-${findings.length + 1}`,
            ruleId: 'cwe-862-missing-auth',
            severity,
            message: `Authorization - ${type}: Verify user has permission`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['862'],
            owasp: ['A01:2021'],
            suggestion: {
              description: 'Add authorization middleware',
              example: `// Check ownership before update
if (resource.userId !== req.user.id) {
  return res.status(403).json({ error: 'Forbidden' });
}`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe862MissingAuth;
