/**
 * @fileoverview CWE-190: Integer Overflow or Wraparound
 * @module @nahisaho/musubix-security/rules/cwe/cwe-190-integer-overflow
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe190IntegerOverflow: SecurityRule = {
  id: 'cwe-190-integer-overflow',
  name: 'CWE-190: Integer Overflow or Wraparound',
  description: 'Detects potential integer overflow vulnerabilities',
  defaultSeverity: 'high',
  category: 'numeric',
  tags: ['cwe', 'integer', 'overflow', 'security'],
  cwe: ['190'],
  references: [
    { title: 'CWE-190', url: 'https://cwe.mitre.org/data/definitions/190.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /\w+\s*\+\s*\w+\s*>\s*Number\.MAX_SAFE_INTEGER/gi, type: 'Unchecked addition overflow', severity: 'high' as const },
      { pattern: /parseInt\s*\([^)]+\)\s*\*\s*\d+/gi, type: 'Parsed int multiplication', severity: 'medium' as const },
      { pattern: /\w+\s*\*\s*\w+\s*(?!.*(?:BigInt|overflow|check))/gi, type: 'Unchecked multiplication', severity: 'low' as const },
      { pattern: /Math\.pow\s*\([^)]+\)/gi, type: 'Power operation without bounds', severity: 'medium' as const },
      { pattern: /<<\s*\d{2,}/gi, type: 'Large bit shift', severity: 'high' as const },
      { pattern: /new\s+(?:Int8|Int16|Int32|Uint8|Uint16|Uint32)Array/gi, type: 'TypedArray boundary', severity: 'low' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-190-${findings.length + 1}`,
            ruleId: 'cwe-190-integer-overflow',
            severity,
            message: `Integer Overflow - ${type}: Validate numeric bounds`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['190'],
            suggestion: {
              description: 'Use BigInt or bounds checking',
              example: `// Use BigInt for large numbers
const result = BigInt(a) * BigInt(b);

// Or check bounds
if (a > Number.MAX_SAFE_INTEGER - b) throw new Error('Overflow');`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe190IntegerOverflow;
