/**
 * @fileoverview CWE-476: NULL Pointer Dereference
 * @module @nahisaho/musubix-security/rules/cwe/cwe-476-null-deref
 * @trace TSK-RULE-005
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe476NullDeref: SecurityRule = {
  id: 'cwe-476-null-deref',
  name: 'CWE-476: NULL Pointer Dereference',
  description: 'Detects potential null/undefined dereference patterns',
  defaultSeverity: 'medium',
  category: 'error-handling',
  tags: ['cwe', 'null', 'undefined', 'security'],
  cwe: ['476'],
  references: [
    { title: 'CWE-476', url: 'https://cwe.mitre.org/data/definitions/476.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /\w+\.(?:find|findOne)\s*\([^)]+\)\s*\.\w+/gi, type: 'Chained call after find', severity: 'medium' as const },
      { pattern: /JSON\.parse\s*\([^)]+\)\.\w+/gi, type: 'Property access after parse', severity: 'medium' as const },
      { pattern: /await\s+\w+\s*;[^}]*\w+\.\w+/gi, type: 'Access after await without check', severity: 'low' as const },
      { pattern: /\w+\[\d+\]\.\w+/gi, type: 'Property access on array element', severity: 'low' as const },
      { pattern: /\.match\s*\([^)]+\)\[\d+\]/gi, type: 'Index access on match result', severity: 'medium' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-476-${findings.length + 1}`,
            ruleId: 'cwe-476-null-deref',
            severity,
            message: `Null Dereference - ${type}: Check for null/undefined`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['476'],
            suggestion: {
              description: 'Use optional chaining or null checks',
              example: `// Use optional chaining
const value = obj?.property?.nested;

// Or explicit check
const result = await db.findOne(query);
if (!result) throw new Error('Not found');`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe476NullDeref;
