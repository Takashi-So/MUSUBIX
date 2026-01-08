/**
 * @fileoverview CWE-78: Improper Neutralization of Special Elements used in an OS Command (OS Command Injection)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-78-command-injection
 * @trace TSK-RULE-005
 *
 * Detects:
 * - exec/execSync with user input
 * - spawn/spawnSync with shell:true
 * - Template literals in commands
 * - Child process with unsanitized arguments
 *
 * CWE-78 is #5 in CWE Top 25 2023.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-78 - OS Command Injection
 */
export const cwe78CommandInjection: SecurityRule = {
  id: 'cwe-78-command-injection',
  name: 'CWE-78: OS Command Injection',
  description:
    'Detects OS command injection vulnerabilities from unsafe command execution',
  defaultSeverity: 'critical',
  category: 'injection',
  tags: ['cwe', 'command', 'injection', 'shell', 'security'],
  owasp: ['A03:2021'],
  cwe: ['78'],
  references: [
    {
      title: 'CWE-78: OS Command Injection',
      url: 'https://cwe.mitre.org/data/definitions/78.html',
    },
    {
      title: 'OWASP Command Injection',
      url: 'https://owasp.org/www-community/attacks/Command_Injection',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkExecUsage(context, sourceCode, findings);
    checkSpawnUsage(context, sourceCode, findings);
    checkShellExecution(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for exec/execSync with user input
 */
function checkExecUsage(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const execPatterns = [
    {
      pattern: /exec\s*\(\s*['"`].*\+\s*(?:req\.|params\.|query\.|body\.|user)/gi,
      type: 'exec with user input concatenation',
      message: 'exec() with user input allows command injection',
      severity: 'critical' as const,
    },
    {
      pattern: /exec\s*\(\s*`[^`]*\$\{(?:req\.|params\.|query\.|body\.)/gi,
      type: 'exec with user input interpolation',
      message: 'exec() with template literal user input is vulnerable',
      severity: 'critical' as const,
    },
    {
      pattern: /execSync\s*\(\s*['"`].*\+/gi,
      type: 'execSync with concatenation',
      message: 'execSync() with string concatenation may allow injection',
      severity: 'high' as const,
    },
    {
      pattern: /execSync\s*\(\s*`[^`]*\$\{/gi,
      type: 'execSync with interpolation',
      message: 'execSync() with template interpolation is risky',
      severity: 'high' as const,
    },
    {
      pattern: /execFile\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'execFile with user-controlled command',
      message: 'execFile() with user-controlled command path is dangerous',
      severity: 'critical' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of execPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-78-exec-${findings.length + 1}`,
          ruleId: 'cwe-78-command-injection',
          severity,
          message: `Command Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['78'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use execFile with argument array or sanitize input',
            example: `// Use execFile with separate arguments (no shell)
const { execFile } = require('child_process');
execFile('ls', ['-la', safeDir], (err, stdout) => {});

// Or validate/whitelist commands
const allowedCommands = ['list', 'status'];
if (!allowedCommands.includes(userCommand)) {
  throw new Error('Invalid command');
}`,
          },
        });
      }
    }
  }
}

/**
 * Check for spawn with shell:true
 */
function checkSpawnUsage(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const spawnPatterns = [
    {
      pattern: /spawn\s*\([^)]*shell\s*:\s*true/gi,
      type: 'spawn with shell:true',
      message: 'spawn() with shell:true enables shell command injection',
      severity: 'high' as const,
    },
    {
      pattern: /spawnSync\s*\([^)]*shell\s*:\s*true/gi,
      type: 'spawnSync with shell:true',
      message: 'spawnSync() with shell:true enables shell command injection',
      severity: 'high' as const,
    },
    {
      pattern: /spawn\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'spawn with user-controlled command',
      message: 'spawn() with user-controlled command is dangerous',
      severity: 'critical' as const,
    },
    {
      pattern: /spawn\s*\(\s*['"`]\w+['"`]\s*,\s*\[.*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'spawn with user-controlled arguments',
      message: 'spawn() arguments from user input should be validated',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of spawnPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-78-spawn-${findings.length + 1}`,
          ruleId: 'cwe-78-command-injection',
          severity,
          message: `Command Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['78'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Avoid shell:true and validate arguments',
            example: `// Use spawn without shell (default)
const { spawn } = require('child_process');
spawn('git', ['status']);

// Validate user arguments
const allowedArgs = ['--version', '--help'];
const safeArgs = userArgs.filter(arg => 
  allowedArgs.includes(arg) || /^[a-zA-Z0-9_-]+$/.test(arg)
);
spawn('command', safeArgs);`,
          },
        });
      }
    }
  }
}

/**
 * Check for other shell execution patterns
 */
function checkShellExecution(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const shellPatterns = [
    {
      pattern: /child_process.*require.*exec/gi,
      type: 'child_process exec import',
      message: 'child_process exec should be used carefully',
      severity: 'info' as const,
    },
    {
      pattern: /\$\(\s*['"`][^'"`]*(?:req\.|params\.|query\.)/gi,
      type: 'Shell substitution with user input',
      message: 'Shell substitution with user input is vulnerable',
      severity: 'critical' as const,
    },
    {
      pattern: /eval\s*\(\s*['"`].*(?:sh|bash|cmd|powershell)/gi,
      type: 'eval with shell command',
      message: 'eval() containing shell commands is extremely dangerous',
      severity: 'critical' as const,
    },
    {
      pattern: /\.run\s*\(\s*['"`](?:sh|bash|cmd)\s+/gi,
      type: 'Direct shell invocation',
      message: 'Direct shell invocation is risky',
      severity: 'high' as const,
    },
    {
      pattern: /shelljs|execa|cross-spawn.*(?:req\.|params\.|query\.)/gi,
      type: 'Shell library with user input',
      message: 'Shell execution library with user input needs validation',
      severity: 'high' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of shellPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-78-shell-${findings.length + 1}`,
          ruleId: 'cwe-78-command-injection',
          severity,
          message: `Command Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['78'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use safe alternatives to shell execution',
            example: `// Use specific APIs instead of shell commands
// Instead of: exec('rm -rf ' + dir)
const fs = require('fs');
fs.rmSync(dir, { recursive: true });

// For git operations, use a library
const simpleGit = require('simple-git');
await git.status();`,
          },
        });
      }
    }
  }
}

export default cwe78CommandInjection;
