/**
 * @fileoverview CWE-276: Incorrect Default Permissions
 * @module @nahisaho/musubix-security/rules/cwe/cwe-276-default-permissions
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe276DefaultPermissions: SecurityRule = {
  id: 'cwe-276-default-permissions',
  name: 'CWE-276: Incorrect Default Permissions',
  description: 'Detects overly permissive default file/resource permissions',
  defaultSeverity: 'medium',
  category: 'configuration',
  tags: ['cwe', 'permissions', 'configuration', 'security'],
  cwe: ['276'],
  references: [
    { title: 'CWE-276', url: 'https://cwe.mitre.org/data/definitions/276.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /chmod\s*\(\s*['"`]?0?777/gi, type: 'World-writable permissions', severity: 'critical' as const },
      { pattern: /chmod\s*\(\s*['"`]?0?666/gi, type: 'World-readable/writable file', severity: 'high' as const },
      { pattern: /umask\s*\(\s*0*0*0\s*\)/gi, type: 'No umask restriction', severity: 'high' as const },
      { pattern: /mode\s*:\s*0o?777/gi, type: 'Mode 777 in options', severity: 'critical' as const },
      { pattern: /fs\.chmod.*0o?7[0-7][0-7]/gi, type: 'fs.chmod with execute for all', severity: 'high' as const },
      { pattern: /writeFile.*\{\s*mode\s*:\s*0o?[67]/gi, type: 'writeFile with permissive mode', severity: 'medium' as const },
      { pattern: /mkdir.*\{\s*mode\s*:\s*0o?777/gi, type: 'mkdir with 777', severity: 'critical' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-276-${findings.length + 1}`,
            ruleId: 'cwe-276-default-permissions',
            severity,
            message: `Default Permissions - ${type}: Use restrictive permissions`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['276'],
            suggestion: {
              description: 'Use least privilege permissions',
              example: `// Use restrictive permissions
fs.writeFileSync(path, data, { mode: 0o600 }); // Owner only
fs.mkdirSync(dir, { mode: 0o700 }); // Owner only`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe276DefaultPermissions;
