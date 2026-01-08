/**
 * @fileoverview CWE-863: Incorrect Authorization
 * @module @nahisaho/musubix-security/rules/cwe/cwe-863-incorrect-auth
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe863IncorrectAuth: SecurityRule = {
  id: 'cwe-863-incorrect-auth',
  name: 'CWE-863: Incorrect Authorization',
  description: 'Detects incorrect authorization implementation patterns',
  defaultSeverity: 'high',
  category: 'authorization',
  tags: ['cwe', 'authorization', 'access-control', 'security'],
  cwe: ['863'],
  owasp: ['A01:2021'],
  references: [
    { title: 'CWE-863', url: 'https://cwe.mitre.org/data/definitions/863.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /if\s*\(\s*user\.id\s*===?\s*req\.params/gi, type: 'Client-side ID comparison', severity: 'high' as const },
      { pattern: /req\.user\.role\s*===?\s*['"`]admin['"`]\s*\|\|/gi, type: 'OR-based permission check', severity: 'medium' as const },
      { pattern: /\.findById\s*\(\s*req\.params/gi, type: 'Direct ID access without ownership', severity: 'high' as const },
      { pattern: /canAccess\s*=\s*true/gi, type: 'Hardcoded access grant', severity: 'high' as const },
      { pattern: /authorization.*skip|bypass.*auth/gi, type: 'Authorization bypass', severity: 'critical' as const },
      { pattern: /user\.permissions\.includes\s*\(\s*req\./gi, type: 'Permission from user input', severity: 'critical' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-863-${findings.length + 1}`,
            ruleId: 'cwe-863-incorrect-auth',
            severity,
            message: `Incorrect Authorization - ${type}: Implement proper access control`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['863'],
            owasp: ['A01:2021'],
            suggestion: {
              description: 'Use centralized authorization with ownership checks',
              example: `// Proper authorization
const resource = await Resource.findById(id);
if (!resource) throw new NotFoundError();
if (resource.ownerId !== user.id && !user.isAdmin) {
  throw new ForbiddenError();
}`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe863IncorrectAuth;
