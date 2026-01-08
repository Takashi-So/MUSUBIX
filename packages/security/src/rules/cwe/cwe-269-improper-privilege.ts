/**
 * @fileoverview CWE-269: Improper Privilege Management
 * @module @nahisaho/musubix-security/rules/cwe/cwe-269-improper-privilege
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe269ImproperPrivilege: SecurityRule = {
  id: 'cwe-269-improper-privilege',
  name: 'CWE-269: Improper Privilege Management',
  description: 'Detects improper privilege assignment and escalation risks',
  defaultSeverity: 'high',
  category: 'authorization',
  tags: ['cwe', 'privilege', 'escalation', 'security'],
  cwe: ['269'],
  owasp: ['A01:2021'],
  references: [
    { title: 'CWE-269', url: 'https://cwe.mitre.org/data/definitions/269.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /role\s*[:=]\s*['"`]admin['"`]/gi, type: 'Direct admin role assignment', severity: 'high' as const },
      { pattern: /isAdmin\s*[:=]\s*true/gi, type: 'Direct admin flag set', severity: 'high' as const },
      { pattern: /setuid|setgid|seteuid/gi, type: 'Privilege elevation function', severity: 'critical' as const },
      { pattern: /sudo|runas/gi, type: 'Privilege escalation command', severity: 'critical' as const },
      { pattern: /chmod\s*\(\s*['"`]?0?7/gi, type: 'Overly permissive chmod', severity: 'high' as const },
      { pattern: /user\.role\s*=\s*req\./gi, type: 'Role from user input', severity: 'critical' as const },
      { pattern: /\.grant\s*\(\s*['"`]\*/gi, type: 'Wildcard permission grant', severity: 'high' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-269-${findings.length + 1}`,
            ruleId: 'cwe-269-improper-privilege',
            severity,
            message: `Privilege Management - ${type}: Follow least privilege principle`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['269'],
            owasp: ['A01:2021'],
            suggestion: {
              description: 'Apply least privilege principle',
              example: `// Use role-based access control
const permissions = rbac.getPermissions(user.role);
if (!permissions.includes('admin:write')) {
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

export default cwe269ImproperPrivilege;
