/**
 * @fileoverview CWE-22: Improper Limitation of a Pathname to a Restricted Directory (Path Traversal)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-22-path-traversal
 * @trace TSK-RULE-005
 *
 * Detects:
 * - Path concatenation with user input
 * - Missing path normalization
 * - Directory escape attempts
 * - Symlink attacks
 *
 * CWE-22 is #8 in CWE Top 25 2023.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-22 - Path Traversal
 */
export const cwe22PathTraversal: SecurityRule = {
  id: 'cwe-22-path-traversal',
  name: 'CWE-22: Path Traversal',
  description:
    'Detects path traversal vulnerabilities from unsafe path construction',
  defaultSeverity: 'high',
  category: 'file-system',
  tags: ['cwe', 'path', 'traversal', 'lfi', 'security'],
  cwe: ['22'],
  references: [
    {
      title: 'CWE-22: Path Traversal',
      url: 'https://cwe.mitre.org/data/definitions/22.html',
    },
    {
      title: 'OWASP Path Traversal',
      url: 'https://owasp.org/www-community/attacks/Path_Traversal',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkPathConcatenation(context, sourceCode, findings);
    checkFileOperations(context, sourceCode, findings);
    checkPathNormalization(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for path concatenation with user input
 */
function checkPathConcatenation(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const pathPatterns = [
    {
      pattern: /path\.join\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'path.join with user input',
      message: 'path.join with user input allows path traversal',
      severity: 'high' as const,
    },
    {
      pattern: /path\.resolve\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'path.resolve with user input',
      message: 'path.resolve with user input allows path traversal',
      severity: 'high' as const,
    },
    {
      pattern: /['"`]\/.*['"`]\s*\+\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'String path concatenation',
      message: 'Path string concatenation with user input is vulnerable',
      severity: 'critical' as const,
    },
    {
      pattern: /`[^`]*\/[^`]*\$\{(?:req\.|params\.|query\.|body\.)/gi,
      type: 'Template path with user input',
      message: 'Template literal path with user input is vulnerable',
      severity: 'critical' as const,
    },
    {
      pattern: /__dirname\s*\+\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: '__dirname concatenation',
      message: '__dirname + user input allows path traversal',
      severity: 'high' as const,
    },
    {
      pattern: /process\.cwd\(\)\s*\+\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'process.cwd concatenation',
      message: 'process.cwd() + user input allows path traversal',
      severity: 'high' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of pathPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-22-concat-${findings.length + 1}`,
          ruleId: 'cwe-22-path-traversal',
          severity,
          message: `Path Traversal - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['22'],
          suggestion: {
            description: 'Validate and normalize path, check it stays within allowed directory',
            example: `const path = require('path');
const allowedDir = '/safe/uploads';

function getSafePath(userPath) {
  // Normalize and resolve
  const resolved = path.resolve(allowedDir, userPath);
  
  // Verify it's still within allowed directory
  if (!resolved.startsWith(allowedDir + path.sep)) {
    throw new Error('Path traversal detected');
  }
  
  return resolved;
}`,
          },
        });
      }
    }
  }
}

/**
 * Check for unsafe file operations
 */
function checkFileOperations(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const filePatterns = [
    {
      pattern: /fs\.(?:readFile|readFileSync)\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'readFile with user input',
      message: 'Reading file with user-controlled path allows LFI',
      severity: 'critical' as const,
    },
    {
      pattern: /fs\.(?:writeFile|writeFileSync)\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'writeFile with user input',
      message: 'Writing file with user-controlled path is dangerous',
      severity: 'critical' as const,
    },
    {
      pattern: /fs\.(?:unlink|unlinkSync|rm|rmSync)\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'unlink with user input',
      message: 'Deleting file with user-controlled path is very dangerous',
      severity: 'critical' as const,
    },
    {
      pattern: /fs\.(?:createReadStream|createWriteStream)\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'createStream with user input',
      message: 'Stream creation with user path allows traversal',
      severity: 'high' as const,
    },
    {
      pattern: /fs\.(?:access|stat|lstat)\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'stat with user input',
      message: 'File stat with user path leaks file existence',
      severity: 'medium' as const,
    },
    {
      pattern: /fs\.(?:mkdir|mkdirSync)\s*\([^)]*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'mkdir with user input',
      message: 'Creating directories with user input path',
      severity: 'medium' as const,
    },
    {
      pattern: /require\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'require with user input',
      message: 'Dynamic require with user input allows code execution',
      severity: 'critical' as const,
    },
    {
      pattern: /import\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'dynamic import with user input',
      message: 'Dynamic import with user input allows code execution',
      severity: 'critical' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of filePatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-22-file-${findings.length + 1}`,
          ruleId: 'cwe-22-path-traversal',
          severity,
          message: `Path Traversal - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['22'],
          suggestion: {
            description: 'Validate path before file operations',
            example: `const path = require('path');
const fs = require('fs').promises;

async function safeReadFile(baseDir, userFilename) {
  // Remove any path components
  const basename = path.basename(userFilename);
  
  // Construct safe path
  const safePath = path.join(baseDir, basename);
  
  // Verify within allowed directory
  const realPath = await fs.realpath(safePath);
  if (!realPath.startsWith(await fs.realpath(baseDir))) {
    throw new Error('Access denied');
  }
  
  return fs.readFile(safePath);
}`,
          },
        });
      }
    }
  }
}

/**
 * Check for path normalization issues
 */
function checkPathNormalization(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const normPatterns = [
    {
      pattern: /\.\.\/|\.\.\\|\.\.\%2f|\.\.\%5c/gi,
      type: 'Path traversal sequence',
      message: 'Literal path traversal sequence detected',
      severity: 'info' as const,
    },
    {
      pattern: /decodeURIComponent\s*\([^)]*\)[^;]*(?:fs\.|path\.)/gi,
      type: 'URL decode before path operation',
      message: 'URL decoding before path operation may bypass filters',
      severity: 'medium' as const,
    },
    {
      pattern: /\.replace\s*\(\s*['"`]\.\.['"`]\s*,/gi,
      type: 'Simple .. replacement',
      message: 'Simple string replacement for .. can be bypassed',
      severity: 'medium' as const,
    },
    {
      pattern: /\.includes\s*\(\s*['"`]\.\.['"`]\s*\)/gi,
      type: 'Simple .. check',
      message: 'Simple includes check for .. can be bypassed',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of normPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-22-norm-${findings.length + 1}`,
          ruleId: 'cwe-22-path-traversal',
          severity,
          message: `Path Normalization - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['22'],
          suggestion: {
            description: 'Use path.normalize and realpath for proper validation',
            example: `const path = require('path');
const fs = require('fs').promises;

async function validatePath(baseDir, userPath) {
  // Normalize path
  const normalized = path.normalize(userPath);
  const fullPath = path.join(baseDir, normalized);
  
  // Resolve symlinks and get real path
  try {
    const realPath = await fs.realpath(fullPath);
    const realBase = await fs.realpath(baseDir);
    
    // Ensure resolved path is within base
    if (!realPath.startsWith(realBase + path.sep)) {
      throw new Error('Path traversal attempt');
    }
    return realPath;
  } catch (err) {
    throw new Error('Invalid path');
  }
}`,
          },
        });
      }
    }
  }
}

export default cwe22PathTraversal;
