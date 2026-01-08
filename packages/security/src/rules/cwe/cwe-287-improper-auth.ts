/**
 * @fileoverview CWE-287: Improper Authentication
 * @module @nahisaho/musubix-security/rules/cwe/cwe-287-improper-auth
 * @trace TSK-RULE-005
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe287ImproperAuth: SecurityRule = {
  id: 'cwe-287-improper-auth',
  name: 'CWE-287: Improper Authentication',
  description: 'Detects weak or improper authentication patterns',
  defaultSeverity: 'high',
  category: 'authentication',
  tags: ['cwe', 'authentication', 'security'],
  owasp: ['A07:2021'],
  cwe: ['287'],
  references: [
    { title: 'CWE-287', url: 'https://cwe.mitre.org/data/definitions/287.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /password\s*===?\s*['"`]\w+['"`]/gi, type: 'Hardcoded password check', severity: 'critical' as const },
      { pattern: /if\s*\(\s*req\.headers\.authorization\s*\)/gi, type: 'Simple auth header check', severity: 'medium' as const },
      { pattern: /\.compare\s*\(\s*password\s*,\s*password/gi, type: 'Password compared to itself', severity: 'high' as const },
      { pattern: /jwt\.verify\s*\([^)]*\{\s*\}\s*\)/gi, type: 'JWT verify without options', severity: 'high' as const },
      { pattern: /algorithms\s*:\s*\[\s*['"`]none['"`]/gi, type: 'JWT none algorithm', severity: 'critical' as const },
      { pattern: /session\.cookie\.secure\s*=\s*false/gi, type: 'Insecure session cookie', severity: 'high' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-287-${findings.length + 1}`,
            ruleId: 'cwe-287-improper-auth',
            severity,
            message: `Authentication - ${type}: Use secure authentication`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['287'],
            owasp: ['A07:2021'],
            suggestion: {
              description: 'Use proper authentication libraries',
              example: `// Use bcrypt for password comparison
const isValid = await bcrypt.compare(inputPassword, hashedPassword);

// JWT with proper options
jwt.verify(token, secret, { algorithms: ['HS256'] });`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe287ImproperAuth;
