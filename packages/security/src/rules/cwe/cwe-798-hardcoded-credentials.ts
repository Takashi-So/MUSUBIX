/**
 * @fileoverview CWE-798: Use of Hard-coded Credentials
 * @module @nahisaho/musubix-security/rules/cwe/cwe-798-hardcoded-credentials
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe798HardcodedCredentials: SecurityRule = {
  id: 'cwe-798-hardcoded-credentials',
  name: 'CWE-798: Hard-coded Credentials',
  description: 'Detects hard-coded passwords, API keys, and secrets',
  defaultSeverity: 'critical',
  category: 'secrets',
  tags: ['cwe', 'credentials', 'secrets', 'security'],
  cwe: ['798'],
  owasp: ['A07:2021'],
  references: [
    { title: 'CWE-798', url: 'https://cwe.mitre.org/data/definitions/798.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /password\s*[:=]\s*['"`][^'"`]{4,}['"`]/gi, type: 'Hardcoded password', severity: 'critical' as const },
      { pattern: /api[_-]?key\s*[:=]\s*['"`][^'"`]{8,}['"`]/gi, type: 'Hardcoded API key', severity: 'critical' as const },
      { pattern: /secret\s*[:=]\s*['"`][^'"`]{8,}['"`]/gi, type: 'Hardcoded secret', severity: 'critical' as const },
      { pattern: /token\s*[:=]\s*['"`][A-Za-z0-9_-]{20,}['"`]/gi, type: 'Hardcoded token', severity: 'critical' as const },
      { pattern: /private[_-]?key\s*[:=]\s*['"`]/gi, type: 'Hardcoded private key', severity: 'critical' as const },
      { pattern: /-----BEGIN\s+(?:RSA\s+)?PRIVATE\s+KEY-----/gi, type: 'Embedded private key', severity: 'critical' as const },
      { pattern: /aws[_-]?(?:access|secret)[_-]?key\s*[:=]/gi, type: 'AWS credentials', severity: 'critical' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-798-${findings.length + 1}`,
            ruleId: 'cwe-798-hardcoded-credentials',
            severity,
            message: `Hardcoded Credentials - ${type}: Use environment variables`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['798'],
            owasp: ['A07:2021'],
            suggestion: {
              description: 'Use environment variables or secrets manager',
              example: `// Use environment variables
const apiKey = process.env.API_KEY;

// Or use a secrets manager
const secret = await secretsManager.getSecret('my-secret');`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe798HardcodedCredentials;
