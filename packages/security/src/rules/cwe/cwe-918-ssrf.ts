/**
 * @fileoverview CWE-918: Server-Side Request Forgery (SSRF)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-918-ssrf
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe918SSRF: SecurityRule = {
  id: 'cwe-918-ssrf',
  name: 'CWE-918: Server-Side Request Forgery',
  description: 'Detects SSRF vulnerabilities where user input controls URLs',
  defaultSeverity: 'high',
  category: 'injection',
  tags: ['cwe', 'ssrf', 'network', 'security'],
  cwe: ['918'],
  owasp: ['A10:2021'],
  references: [
    { title: 'CWE-918', url: 'https://cwe.mitre.org/data/definitions/918.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /fetch\s*\(\s*req\./gi, type: 'fetch with request URL', severity: 'high' as const },
      { pattern: /axios\s*\.\s*get\s*\(\s*\w+\)/gi, type: 'axios with variable URL', severity: 'high' as const },
      { pattern: /http\.request\s*\(\s*\{[^}]*url\s*:\s*\w+/gi, type: 'http.request with variable', severity: 'high' as const },
      { pattern: /new\s+URL\s*\(\s*req\./gi, type: 'URL from request', severity: 'high' as const },
      { pattern: /redirect\s*\(\s*req\./gi, type: 'Redirect from request', severity: 'medium' as const },
      { pattern: /got\s*\(\s*\w+\)/gi, type: 'got with variable URL', severity: 'high' as const },
      { pattern: /request\s*\(\s*\{[^}]*uri\s*:\s*\w+/gi, type: 'request with variable URI', severity: 'high' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-918-${findings.length + 1}`,
            ruleId: 'cwe-918-ssrf',
            severity,
            message: `SSRF - ${type}: Validate and allowlist URLs`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['918'],
            owasp: ['A10:2021'],
            suggestion: {
              description: 'Validate URLs against an allowlist',
              example: `// Use URL allowlist
const allowedHosts = ['api.example.com'];
const url = new URL(userUrl);
if (!allowedHosts.includes(url.hostname)) {
  throw new Error('URL not allowed');
}`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe918SSRF;
