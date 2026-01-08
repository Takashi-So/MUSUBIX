/**
 * @fileoverview CWE-20: Improper Input Validation
 * @module @nahisaho/musubix-security/rules/cwe/cwe-20-input-validation
 * @trace TSK-RULE-005
 *
 * Detects:
 * - Missing input validation
 * - Insufficient type checking
 * - Missing length/size limits
 * - Unsafe type coercion
 * - Missing sanitization
 *
 * CWE-20 is #6 in CWE Top 25 2023.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-20 - Improper Input Validation
 */
export const cwe20InputValidation: SecurityRule = {
  id: 'cwe-20-input-validation',
  name: 'CWE-20: Improper Input Validation',
  description:
    'Detects missing or insufficient input validation patterns',
  defaultSeverity: 'medium',
  category: 'input-validation',
  tags: ['cwe', 'input', 'validation', 'security'],
  cwe: ['20'],
  references: [
    {
      title: 'CWE-20: Improper Input Validation',
      url: 'https://cwe.mitre.org/data/definitions/20.html',
    },
    {
      title: 'OWASP Input Validation Cheat Sheet',
      url: 'https://cheatsheetseries.owasp.org/cheatsheets/Input_Validation_Cheat_Sheet.html',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkDirectUserInput(context, sourceCode, findings);
    checkTypeCoercion(context, sourceCode, findings);
    checkMissingLengthChecks(context, sourceCode, findings);
    checkRegexValidation(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for direct use of user input without validation
 */
function checkDirectUserInput(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const inputPatterns = [
    {
      pattern: /const\s+\w+\s*=\s*req\.body\.\w+\s*;/gi,
      type: 'Direct body access',
      message: 'Request body field used without validation',
      severity: 'medium' as const,
    },
    {
      pattern: /const\s+\w+\s*=\s*req\.query\.\w+\s*;/gi,
      type: 'Direct query access',
      message: 'Query parameter used without validation',
      severity: 'medium' as const,
    },
    {
      pattern: /const\s+\w+\s*=\s*req\.params\.\w+\s*;/gi,
      type: 'Direct params access',
      message: 'URL parameter used without validation',
      severity: 'medium' as const,
    },
    {
      pattern: /const\s*\{[^}]+\}\s*=\s*req\.body\s*;/gi,
      type: 'Destructured body',
      message: 'Destructuring body without validation schema',
      severity: 'low' as const,
    },
    {
      pattern: /JSON\.parse\s*\(\s*(?:req\.|body|data|input)/gi,
      type: 'JSON.parse with user input',
      message: 'JSON.parse with user input should have error handling',
      severity: 'medium' as const,
    },
    {
      pattern: /parseInt\s*\(\s*(?:req\.|params\.|query\.)/gi,
      type: 'parseInt with user input',
      message: 'parseInt with user input may produce unexpected results',
      severity: 'low' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of inputPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-20-input-${findings.length + 1}`,
          ruleId: 'cwe-20-input-validation',
          severity,
          message: `Input Validation - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['20'],
          suggestion: {
            description: 'Use validation library like Zod, Joi, or Yup',
            example: `// Use Zod for validation
import { z } from 'zod';

const schema = z.object({
  email: z.string().email(),
  age: z.number().min(0).max(120),
});

const result = schema.safeParse(req.body);
if (!result.success) {
  return res.status(400).json({ errors: result.error.issues });
}
const { email, age } = result.data;`,
          },
        });
      }
    }
  }
}

/**
 * Check for unsafe type coercion
 */
function checkTypeCoercion(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const coercionPatterns = [
    {
      pattern: /==\s*(?:null|undefined|true|false|['"`]\w*['"`]|\d+)/gi,
      type: 'Loose equality comparison',
      message: 'Loose equality (==) can cause type coercion issues',
      severity: 'low' as const,
    },
    {
      pattern: /!=\s*(?:null|undefined)/gi,
      type: 'Loose inequality',
      message: 'Loose inequality (!=) can cause type coercion issues',
      severity: 'low' as const,
    },
    {
      pattern: /Number\s*\(\s*(?:req\.|params\.|query\.)/gi,
      type: 'Number coercion of user input',
      message: 'Number() coercion may return NaN for invalid input',
      severity: 'low' as const,
    },
    {
      pattern: /\+\s*(?:req\.|params\.|query\.)\w+/gi,
      type: 'Unary plus coercion',
      message: 'Unary plus for number conversion is implicit and error-prone',
      severity: 'low' as const,
    },
    {
      pattern: /Boolean\s*\(\s*(?:req\.|params\.|query\.)/gi,
      type: 'Boolean coercion',
      message: 'Boolean coercion treats empty string as false',
      severity: 'info' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of coercionPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-20-coerce-${findings.length + 1}`,
          ruleId: 'cwe-20-input-validation',
          severity,
          message: `Type Coercion - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['20'],
          suggestion: {
            description: 'Use strict equality and explicit type checking',
            example: `// Use strict equality
if (value === null || value === undefined) { }

// Explicit number parsing with validation
const num = Number.parseInt(input, 10);
if (Number.isNaN(num)) {
  throw new Error('Invalid number');
}

// Boolean from string
const boolValue = input === 'true';`,
          },
        });
      }
    }
  }
}

/**
 * Check for missing length/size checks
 */
function checkMissingLengthChecks(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const lengthPatterns = [
    {
      pattern: /req\.body\.\w+\.(?:split|slice|substring|substr)\s*\(/gi,
      type: 'String operation without length check',
      message: 'String operation on user input without length validation',
      severity: 'low' as const,
    },
    {
      pattern: /\.forEach\s*\(\s*(?:async\s*)?\([^)]*\)\s*=>\s*\{[^}]*await/gi,
      type: 'Async forEach on user array',
      message: 'Unbounded iteration over user input may cause DoS',
      severity: 'medium' as const,
    },
    {
      pattern: /req\.files?\.\w+\s*(?:;|$)/gi,
      type: 'File access without size check',
      message: 'File upload accessed without size validation',
      severity: 'medium' as const,
    },
    {
      pattern: /\.repeat\s*\(\s*(?:req\.|params\.|query\.|Number\()/gi,
      type: 'String repeat with user input',
      message: 'String.repeat with user input can cause memory exhaustion',
      severity: 'high' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of lengthPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-20-length-${findings.length + 1}`,
          ruleId: 'cwe-20-input-validation',
          severity,
          message: `Missing Length Check - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['20'],
          suggestion: {
            description: 'Add length/size limits to user input',
            example: `// Limit string length
const MAX_LENGTH = 1000;
if (input.length > MAX_LENGTH) {
  throw new Error('Input too long');
}

// Limit array operations
const MAX_ITEMS = 100;
const items = userArray.slice(0, MAX_ITEMS);

// Limit file size
const MAX_FILE_SIZE = 5 * 1024 * 1024; // 5MB
if (req.file.size > MAX_FILE_SIZE) {
  throw new Error('File too large');
}`,
          },
        });
      }
    }
  }
}

/**
 * Check for regex validation issues
 */
function checkRegexValidation(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const regexPatterns = [
    {
      pattern: /new\s+RegExp\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'RegExp from user input',
      message: 'Creating RegExp from user input can cause ReDoS',
      severity: 'high' as const,
    },
    {
      pattern: /\.match\s*\(\s*new\s+RegExp\s*\(/gi,
      type: 'Dynamic regex in match',
      message: 'Dynamic regex pattern may be vulnerable to ReDoS',
      severity: 'medium' as const,
    },
    {
      pattern: /\.replace\s*\(\s*new\s+RegExp\s*\(/gi,
      type: 'Dynamic regex in replace',
      message: 'Dynamic regex pattern in replace may be vulnerable',
      severity: 'medium' as const,
    },
    {
      pattern: /\.test\s*\(\s*\w+\s*\)\s*(?:;|\))/gi,
      type: 'Regex test without anchors',
      message: 'Regex validation without ^ and $ anchors may be bypassed',
      severity: 'low' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of regexPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-20-regex-${findings.length + 1}`,
          ruleId: 'cwe-20-input-validation',
          severity,
          message: `Regex Validation - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['20', '1333'],
          suggestion: {
            description: 'Use safe regex patterns and avoid user-controlled regex',
            example: `// Never create RegExp from user input
// Instead, use fixed patterns:
const emailRegex = /^[^s@]+@[^s@]+.[^s@]+$/;
if (!emailRegex.test(email)) {
  throw new Error('Invalid email');
}

// For search, escape special chars:
function escapeRegex(s) { return s.replace(/[.*+?^\${}()|[\\]]/g, '-'); }
const safePattern = new RegExp(escapeRegex(userInput), 'i');`,
          },
        });
      }
    }
  }
}

export default cwe20InputValidation;
