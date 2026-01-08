/**
 * @fileoverview CWE-787: Out-of-bounds Write
 * @module @nahisaho/musubix-security/rules/cwe/cwe-787-oob-write
 * @trace TSK-RULE-005
 *
 * Detects:
 * - Buffer overflow patterns
 * - Array index out of bounds
 * - Unsafe array operations
 * - TypedArray boundary violations
 * - Unchecked array growth
 *
 * CWE-787 is #1 in CWE Top 25 2023.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-787 - Out-of-bounds Write
 */
export const cwe787OutOfBoundsWrite: SecurityRule = {
  id: 'cwe-787-oob-write',
  name: 'CWE-787: Out-of-bounds Write',
  description:
    'Detects potential out-of-bounds write vulnerabilities including buffer overflows and unsafe array access',
  defaultSeverity: 'high',
  category: 'memory-safety',
  tags: ['cwe', 'memory', 'buffer-overflow', 'array', 'security'],
  cwe: ['787'],
  references: [
    {
      title: 'CWE-787: Out-of-bounds Write',
      url: 'https://cwe.mitre.org/data/definitions/787.html',
    },
    {
      title: 'CWE Top 25 2023',
      url: 'https://cwe.mitre.org/top25/archive/2023/2023_top25_list.html',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkBufferOverflowPatterns(context, sourceCode, findings);
    checkUnsafeArrayAccess(context, sourceCode, findings);
    checkTypedArrayViolations(context, sourceCode, findings);
    checkUncheckedArrayGrowth(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for buffer overflow patterns (Node.js Buffer operations)
 */
function checkBufferOverflowPatterns(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const bufferPatterns = [
    {
      pattern: /Buffer\.allocUnsafe\s*\(/gi,
      type: 'Buffer.allocUnsafe usage',
      message:
        'Buffer.allocUnsafe creates uninitialized memory that may contain sensitive data',
      severity: 'medium' as const,
    },
    {
      pattern: /Buffer\.allocUnsafeSlow\s*\(/gi,
      type: 'Buffer.allocUnsafeSlow usage',
      message:
        'Buffer.allocUnsafeSlow creates uninitialized memory without pooling',
      severity: 'medium' as const,
    },
    {
      pattern: /new\s+Buffer\s*\(/gi,
      type: 'Deprecated Buffer constructor',
      message:
        'new Buffer() is deprecated and can cause security issues. Use Buffer.from() or Buffer.alloc()',
      severity: 'high' as const,
    },
    {
      pattern: /\.copy\s*\([^)]*,\s*\d+\s*,\s*\d+\s*,\s*\d+\s*\)/gi,
      type: 'Buffer.copy with manual offsets',
      message: 'Manual buffer copy offsets may cause out-of-bounds writes',
      severity: 'medium' as const,
    },
    {
      pattern: /\.write\s*\([^)]+,\s*(?:offset|index|\w+)\s*[,)]/gi,
      type: 'Buffer.write with dynamic offset',
      message: 'Buffer write with dynamic offset requires bounds checking',
      severity: 'medium' as const,
    },
    {
      pattern: /\.writeUInt(?:8|16|32)(?:BE|LE)?\s*\([^)]+,\s*(?:\w+)\s*\)/gi,
      type: 'Buffer typed write with variable offset',
      message:
        'Buffer typed write operations with variable offsets need bounds validation',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of bufferPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-787-buffer-${findings.length + 1}`,
          ruleId: 'cwe-787-oob-write',
          severity,
          message: `${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['787'],
          suggestion: {
            description: 'Use safe buffer allocation and validate offsets',
            example: `// Use Buffer.alloc() for zero-filled buffers
const buf = Buffer.alloc(size);

// Validate offsets before writing
if (offset >= 0 && offset + dataLength <= buf.length) {
  buf.write(data, offset);
}`,
          },
        });
      }
    }
  }
}

/**
 * Check for unsafe array access patterns
 */
function checkUnsafeArrayAccess(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const arrayPatterns = [
    {
      // arr[userInput] = value (assignment with user-controlled index)
      pattern:
        /\w+\s*\[\s*(?:req\.|params\.|query\.|body\.|user\.|input\.)\w+\s*\]\s*=/gi,
      type: 'Array write with user-controlled index',
      message:
        'Writing to array with user-controlled index can cause out-of-bounds access',
      severity: 'high' as const,
    },
    {
      // arr[i] = value without bounds check in loop
      pattern: /for\s*\([^)]*;\s*[^;]*;\s*\w+\+\+\s*\)[^{]*\{[^}]*\[\w+\]\s*=/gi,
      type: 'Array write in loop without explicit bounds check',
      message:
        'Array writes in loops should have explicit bounds checking',
      severity: 'low' as const,
    },
    {
      // Direct index assignment with arithmetic
      pattern: /\[\s*\w+\s*[\+\-\*]\s*\d+\s*\]\s*=/gi,
      type: 'Array write with index arithmetic',
      message: 'Array index arithmetic may cause out-of-bounds writes',
      severity: 'low' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of arrayPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-787-array-${findings.length + 1}`,
          ruleId: 'cwe-787-oob-write',
          severity,
          message: `${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['787'],
          suggestion: {
            description: 'Validate array indices before writing',
            example: `// Always validate index before array write
if (index >= 0 && index < arr.length) {
  arr[index] = value;
}

// Or use safe array methods
arr.splice(index, 0, value); // Will handle bounds automatically`,
          },
        });
      }
    }
  }
}

/**
 * Check for TypedArray boundary violations
 */
function checkTypedArrayViolations(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const typedArrayPatterns = [
    {
      pattern:
        /new\s+(?:Int8Array|Uint8Array|Int16Array|Uint16Array|Int32Array|Uint32Array|Float32Array|Float64Array|BigInt64Array|BigUint64Array)\s*\(\s*(?:\w+|[^)]+)\s*\)/gi,
      type: 'TypedArray with dynamic size',
      message:
        'TypedArray creation with dynamic size should validate the size parameter',
      severity: 'low' as const,
    },
    {
      pattern:
        /(?:Int8Array|Uint8Array|Int16Array|Uint16Array|Int32Array|Uint32Array|Float32Array|Float64Array)\s*\.\s*from\s*\(/gi,
      type: 'TypedArray.from usage',
      message:
        'TypedArray.from may cause issues if source is larger than expected',
      severity: 'info' as const,
    },
    {
      pattern: /\.set\s*\(\s*\w+\s*,\s*\w+\s*\)/gi,
      type: 'TypedArray.set with offset',
      message:
        'TypedArray.set with offset requires bounds validation to prevent overflow',
      severity: 'medium' as const,
    },
    {
      pattern: /new\s+DataView\s*\([^)]+\)/gi,
      type: 'DataView creation',
      message: 'DataView operations require careful bounds management',
      severity: 'low' as const,
    },
    {
      pattern: /\.setInt(?:8|16|32)\s*\([^)]+\)|\.setUint(?:8|16|32)\s*\([^)]+\)|\.setFloat(?:32|64)\s*\([^)]+\)/gi,
      type: 'DataView typed write',
      message:
        'DataView typed writes can cause out-of-bounds access if offset is not validated',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of typedArrayPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-787-typed-${findings.length + 1}`,
          ruleId: 'cwe-787-oob-write',
          severity,
          message: `${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['787'],
          suggestion: {
            description: 'Validate bounds before TypedArray operations',
            example: `// Validate before TypedArray.set
const targetOffset = 10;
if (targetOffset + sourceArray.length <= targetArray.length) {
  targetArray.set(sourceArray, targetOffset);
}

// DataView with bounds check
const view = new DataView(buffer);
if (offset + 4 <= buffer.byteLength) {
  view.setInt32(offset, value);
}`,
          },
        });
      }
    }
  }
}

/**
 * Check for unchecked array growth patterns
 */
function checkUncheckedArrayGrowth(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const growthPatterns = [
    {
      // arr.length = newLength (direct length manipulation)
      pattern: /\.length\s*=\s*(?:\w+|[^;]+)/gi,
      type: 'Direct array length manipulation',
      message:
        'Direct array length manipulation can truncate data or create sparse arrays',
      severity: 'medium' as const,
    },
    {
      // Unbounded push in loop
      pattern: /while\s*\([^)]*\)[^{]*\{[^}]*\.push\s*\(/gi,
      type: 'Unbounded array growth in while loop',
      message:
        'Array growth in while loop without size limit may cause memory exhaustion',
      severity: 'medium' as const,
    },
    {
      // Array spread with unknown size
      pattern: /\[\s*\.\.\.\w+\s*,\s*\.\.\.\w+\s*\]/gi,
      type: 'Multiple array spreads',
      message:
        'Spreading multiple arrays without size validation may cause memory issues',
      severity: 'low' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of growthPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-787-growth-${findings.length + 1}`,
          ruleId: 'cwe-787-oob-write',
          severity,
          message: `${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['787'],
          suggestion: {
            description: 'Limit array size and validate before modification',
            example: `// Limit array size
const MAX_SIZE = 10000;
if (arr.length < MAX_SIZE) {
  arr.push(item);
}

// Safe length modification
const newLength = Math.min(desiredLength, MAX_ALLOWED_LENGTH);
arr.length = newLength;`,
          },
        });
      }
    }
  }
}

export default cwe787OutOfBoundsWrite;
