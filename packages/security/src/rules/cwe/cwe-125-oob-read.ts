/**
 * @fileoverview CWE-125: Out-of-bounds Read
 * @module @nahisaho/musubix-security/rules/cwe/cwe-125-oob-read
 * @trace TSK-RULE-005
 *
 * Detects:
 * - Buffer read beyond bounds
 * - Array access with unchecked index
 * - String operations with invalid offsets
 * - TypedArray read violations
 *
 * CWE-125 is #7 in CWE Top 25 2023.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-125 - Out-of-bounds Read
 */
export const cwe125OutOfBoundsRead: SecurityRule = {
  id: 'cwe-125-oob-read',
  name: 'CWE-125: Out-of-bounds Read',
  description:
    'Detects potential out-of-bounds read vulnerabilities',
  defaultSeverity: 'medium',
  category: 'memory-safety',
  tags: ['cwe', 'memory', 'buffer', 'array', 'security'],
  cwe: ['125'],
  references: [
    {
      title: 'CWE-125: Out-of-bounds Read',
      url: 'https://cwe.mitre.org/data/definitions/125.html',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkBufferReadPatterns(context, sourceCode, findings);
    checkArrayReadPatterns(context, sourceCode, findings);
    checkStringReadPatterns(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for buffer read patterns
 */
function checkBufferReadPatterns(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const bufferPatterns = [
    {
      pattern: /\.read(?:UInt|Int)(?:8|16|32)(?:BE|LE)?\s*\(\s*(?:\w+|[^)]+)\s*\)/gi,
      type: 'Buffer typed read with dynamic offset',
      message: 'Buffer read with dynamic offset needs bounds checking',
      severity: 'medium' as const,
    },
    {
      pattern: /\.readBigInt64(?:BE|LE)?\s*\(\s*\w+\s*\)/gi,
      type: 'Buffer BigInt read',
      message: 'BigInt buffer read with variable offset needs validation',
      severity: 'medium' as const,
    },
    {
      pattern: /\.slice\s*\(\s*(?:\w+|\d+)\s*,\s*(?:\w+|\d+)\s*\)/gi,
      type: 'Buffer/Array slice with dynamic bounds',
      message: 'Slice with dynamic bounds may read beyond buffer',
      severity: 'low' as const,
    },
    {
      pattern: /\.subarray\s*\(\s*(?:\w+)\s*(?:,\s*\w+)?\s*\)/gi,
      type: 'Subarray with dynamic offset',
      message: 'Subarray with dynamic offset may exceed bounds',
      severity: 'low' as const,
    },
    {
      pattern: /\.toString\s*\(\s*['"`]\w+['"`]\s*,\s*\w+\s*,\s*\w+\s*\)/gi,
      type: 'Buffer toString with dynamic range',
      message: 'Buffer toString with dynamic range needs validation',
      severity: 'low' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of bufferPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-125-buffer-${findings.length + 1}`,
          ruleId: 'cwe-125-oob-read',
          severity,
          message: `Out-of-bounds Read - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['125'],
          suggestion: {
            description: 'Validate offset and length before buffer read',
            example: `// Check bounds before reading
if (offset >= 0 && offset + 4 <= buffer.length) {
  const value = buffer.readInt32LE(offset);
}

// Safe slice
const safeEnd = Math.min(end, buffer.length);
const slice = buffer.slice(start, safeEnd);`,
          },
        });
      }
    }
  }
}

/**
 * Check for array read patterns
 */
function checkArrayReadPatterns(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const arrayPatterns = [
    {
      pattern: /\[\s*(?:req\.|params\.|query\.|body\.)\w+\s*\]/gi,
      type: 'Array access with user-controlled index',
      message: 'User-controlled array index may cause out-of-bounds read',
      severity: 'medium' as const,
    },
    {
      pattern: /\[\s*\w+\s*-\s*\d+\s*\]/gi,
      type: 'Array access with subtraction',
      message: 'Array index subtraction may result in negative index',
      severity: 'low' as const,
    },
    {
      pattern: /\.at\s*\(\s*-?\d+\s*\)/gi,
      type: 'Array.at usage',
      message: 'Array.at returns undefined for out-of-bounds, verify handling',
      severity: 'info' as const,
    },
    {
      pattern: /for\s*\([^)]*<\s*\w+\.length\s*\+\s*\d+/gi,
      type: 'Loop beyond array length',
      message: 'Loop condition exceeds array length',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of arrayPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-125-array-${findings.length + 1}`,
          ruleId: 'cwe-125-oob-read',
          severity,
          message: `Out-of-bounds Read - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['125'],
          suggestion: {
            description: 'Validate array index before access',
            example: `// Check bounds before access
if (index >= 0 && index < array.length) {
  const value = array[index];
}

// Use optional chaining for safety
const value = array[index] ?? defaultValue;

// Use Array.at with null check
const item = array.at(index);
if (item !== undefined) { }`,
          },
        });
      }
    }
  }
}

/**
 * Check for string read patterns
 */
function checkStringReadPatterns(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const stringPatterns = [
    {
      pattern: /\.charAt\s*\(\s*(?:\w+|[^)]+)\s*\)/gi,
      type: 'charAt with dynamic index',
      message: 'charAt returns empty string for invalid index',
      severity: 'info' as const,
    },
    {
      pattern: /\.charCodeAt\s*\(\s*(?:\w+|[^)]+)\s*\)/gi,
      type: 'charCodeAt with dynamic index',
      message: 'charCodeAt returns NaN for invalid index',
      severity: 'low' as const,
    },
    {
      pattern: /\.substring\s*\(\s*\w+\s*,\s*\w+\s*\)/gi,
      type: 'substring with dynamic bounds',
      message: 'Ensure substring bounds are validated',
      severity: 'info' as const,
    },
    {
      pattern: /\.codePointAt\s*\(\s*\w+\s*\)/gi,
      type: 'codePointAt with dynamic index',
      message: 'codePointAt returns undefined for invalid index',
      severity: 'info' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of stringPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-125-string-${findings.length + 1}`,
          ruleId: 'cwe-125-oob-read',
          severity,
          message: `Out-of-bounds Read - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['125'],
          suggestion: {
            description: 'Check string length before character access',
            example: `// Check length before access
if (index < str.length) {
  const char = str.charAt(index);
}

// Handle edge cases
const code = str.charCodeAt(index);
if (!Number.isNaN(code)) {
  // valid code point
}`,
          },
        });
      }
    }
  }
}

export default cwe125OutOfBoundsRead;
