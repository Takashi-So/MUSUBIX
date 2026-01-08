/**
 * @fileoverview CWE-362: Concurrent Execution Using Shared Resource (Race Condition)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-362-race-condition
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe362RaceCondition: SecurityRule = {
  id: 'cwe-362-race-condition',
  name: 'CWE-362: Race Condition',
  description: 'Detects potential race condition vulnerabilities',
  defaultSeverity: 'medium',
  category: 'concurrency',
  tags: ['cwe', 'race-condition', 'concurrency', 'security'],
  cwe: ['362'],
  references: [
    { title: 'CWE-362', url: 'https://cwe.mitre.org/data/definitions/362.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /if\s*\(.*exists.*\).*\{[^}]*(?:write|create|delete)/gis, type: 'Check-then-act pattern', severity: 'high' as const },
      { pattern: /fs\.existsSync.*fs\.(?:write|unlink|mkdir)/gi, type: 'File TOCTOU', severity: 'high' as const },
      { pattern: /\.findOne\s*\([^)]+\).*\.save\s*\(\)/gi, type: 'Read-modify-write pattern', severity: 'medium' as const },
      { pattern: /let\s+\w+\s*=.*;\s*(?:setTimeout|setInterval)/gi, type: 'Shared state with timer', severity: 'medium' as const },
      { pattern: /global\.\w+\s*=|globalThis\.\w+\s*=/gi, type: 'Global state modification', severity: 'medium' as const },
      { pattern: /Promise\.all.*(?:update|write|delete)/gi, type: 'Concurrent mutations', severity: 'medium' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-362-${findings.length + 1}`,
            ruleId: 'cwe-362-race-condition',
            severity,
            message: `Race Condition - ${type}: Use atomic operations or locks`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['362'],
            suggestion: {
              description: 'Use atomic operations or proper locking',
              example: `// Use atomic operation or transaction
await db.transaction(async (tx) => {
  const item = await tx.findOne(query);
  if (item) await tx.update(item.id, data);
});`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe362RaceCondition;
