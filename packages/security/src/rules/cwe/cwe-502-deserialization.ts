/**
 * @fileoverview CWE-502: Deserialization of Untrusted Data
 * @module @nahisaho/musubix-security/rules/cwe/cwe-502-deserialization
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe502Deserialization: SecurityRule = {
  id: 'cwe-502-deserialization',
  name: 'CWE-502: Deserialization of Untrusted Data',
  description: 'Detects unsafe deserialization patterns',
  defaultSeverity: 'critical',
  category: 'injection',
  tags: ['cwe', 'deserialization', 'rce', 'security'],
  cwe: ['502'],
  owasp: ['A08:2021'],
  references: [
    { title: 'CWE-502', url: 'https://cwe.mitre.org/data/definitions/502.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /JSON\.parse\s*\(\s*req\./gi, type: 'JSON.parse on request data', severity: 'high' as const },
      { pattern: /eval\s*\(\s*JSON/gi, type: 'eval on JSON data', severity: 'critical' as const },
      { pattern: /node-serialize|serialize-javascript/gi, type: 'Unsafe serialization library', severity: 'critical' as const },
      { pattern: /yaml\.load\s*\(/gi, type: 'Unsafe YAML load', severity: 'critical' as const },
      { pattern: /pickle|marshal/gi, type: 'Unsafe serialization format', severity: 'high' as const },
      { pattern: /unserialize\s*\(/gi, type: 'PHP-style unserialize', severity: 'critical' as const },
      { pattern: /ObjectInputStream/gi, type: 'Java ObjectInputStream pattern', severity: 'high' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-502-${findings.length + 1}`,
            ruleId: 'cwe-502-deserialization',
            severity,
            message: `Deserialization - ${type}: Validate before deserializing`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['502'],
            owasp: ['A08:2021'],
            suggestion: {
              description: 'Use safe deserialization with schema validation',
              example: `// Use schema validation
import { z } from 'zod';
const schema = z.object({ name: z.string() });
const data = schema.parse(JSON.parse(input));`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe502Deserialization;
