/**
 * @nahisaho/musubix-expert-delegation
 * Security Analyst Expert
 *
 * DES-EXP-001
 * Traces to: REQ-EXP-001
 */

import type { Expert } from '../types/index.js';

/**
 * Security Analyst Expert
 *
 * セキュリティの分析・脆弱性検出を行うエキスパート。
 */
export const securityAnalystExpert: Expert = {
  type: 'security-analyst',
  name: 'Security Analyst Expert',
  description:
    'セキュリティ分析、脆弱性検出、セキュリティベストプラクティスの提案を行います。',

  systemPrompt: `You are a senior security analyst with deep expertise in:
- OWASP Top 10 vulnerabilities
- Secure coding practices
- Authentication and authorization
- Cryptography and data protection
- Threat modeling
- Security testing and penetration testing
- Compliance (GDPR, SOC2, etc.)

When analyzing security:
1. Identify potential vulnerabilities and attack vectors
2. Assess risk severity (Critical/High/Medium/Low)
3. Provide specific remediation steps
4. Consider defense in depth strategies
5. Reference relevant security standards

Always prioritize findings by risk and provide actionable fixes.
Format: [SEVERITY] Description | Location | Fix`,

  triggers: [
    { pattern: 'is this secure', language: 'en', priority: 80 },
    { pattern: 'secure', language: 'en', priority: 65 },
    { pattern: 'security', language: 'en', priority: 70 },
    { pattern: 'vulnerability', language: 'en', priority: 85 },
    { pattern: 'exploit', language: 'en', priority: 85 },
    { pattern: 'injection', language: 'en', priority: 80 },
    { pattern: 'authentication', language: 'en', priority: 60 },
    { pattern: 'セキュリティ', language: 'ja', priority: 80 },
    { pattern: '脆弱性', language: 'ja', priority: 85 },
    { pattern: '安全', language: 'ja', priority: 50 },
    { pattern: '認証', language: 'ja', priority: 60 },
  ],

  ontologyClass: 'sdd:SecurityAnalyst',

  capabilities: [
    {
      name: 'analyze',
      mode: 'advisory',
      description: 'セキュリティ分析・脆弱性検出',
    },
    {
      name: 'review',
      mode: 'advisory',
      description: 'セキュリティレビュー',
    },
    {
      name: 'fix',
      mode: 'implementation',
      description: 'セキュリティ修正コード生成',
    },
  ],
};
