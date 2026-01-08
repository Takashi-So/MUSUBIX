/**
 * @fileoverview CWE-119: Improper Restriction of Operations within Bounds of Memory Buffer
 * @module @nahisaho/musubix-security/rules/cwe/cwe-119-buffer-overflow
 * @trace TSK-RULE-006
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

export const cwe119BufferOverflow: SecurityRule = {
  id: 'cwe-119-buffer-overflow',
  name: 'CWE-119: Buffer Overflow',
  description: 'Detects improper buffer boundary operations',
  defaultSeverity: 'high',
  category: 'memory-safety',
  tags: ['cwe', 'buffer', 'memory', 'security'],
  cwe: ['119'],
  references: [
    { title: 'CWE-119', url: 'https://cwe.mitre.org/data/definitions/119.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const lines = context.sourceCode.split('\n');

    const patterns = [
      { pattern: /Buffer\.from\s*\([^)]+\)\.copy\s*\(/gi, type: 'Buffer copy without bounds', severity: 'high' as const },
      { pattern: /\.slice\s*\(\s*\w+\s*,\s*\w+\s*\)/gi, type: 'Dynamic slice bounds', severity: 'medium' as const },
      { pattern: /new\s+ArrayBuffer\s*\(\s*\w+\s*\)/gi, type: 'Dynamic ArrayBuffer size', severity: 'medium' as const },
      { pattern: /\.set\s*\([^)]+,\s*\w+\s*\)/gi, type: 'TypedArray set with offset', severity: 'medium' as const },
      { pattern: /memcpy|memmove|strcpy|strcat/gi, type: 'C-style memory function', severity: 'critical' as const },
      { pattern: /\.subarray\s*\(\s*-/gi, type: 'Negative subarray index', severity: 'high' as const },
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const { pattern, type, severity } of patterns) {
        pattern.lastIndex = 0;
        if (pattern.test(lines[i])) {
          findings.push({
            id: `cwe-119-${findings.length + 1}`,
            ruleId: 'cwe-119-buffer-overflow',
            severity,
            message: `Buffer Overflow - ${type}: Validate buffer boundaries`,
            location: { file: context.filePath, startLine: i + 1, endLine: i + 1 },
            cwe: ['119'],
            suggestion: {
              description: 'Always validate buffer bounds before operations',
              example: `// Validate bounds before copy
if (offset + length <= buffer.length) {
  source.copy(buffer, offset, 0, length);
}`,
            },
          });
        }
      }
    }
    return findings;
  },
};

export default cwe119BufferOverflow;
