/**
 * @fileoverview Command execution sink definitions
 * @module @nahisaho/musubix-security/analysis/sinks/command-exec
 * @trace REQ-SEC-001
 */

import type { SinkDefinition } from './types.js';

/**
 * Command injection sinks
 * @trace REQ-SEC-001
 */
export const COMMAND_EXEC_SINKS: readonly SinkDefinition[] = [
  // child_process exec
  {
    id: 'SNK-CMD-001',
    name: 'OS Command Execution (exec)',
    category: 'command-exec',
    severity: 'critical',
    framework: 'node',
    patterns: [
      { receiver: 'child_process', method: 'exec', vulnerableArg: 0 },
      { method: 'exec', vulnerableArg: 0 },
      { method: 'execSync', vulnerableArg: 0 },
      {
        importPattern: { module: 'child_process', named: ['exec', 'execSync'] },
        method: ['exec', 'execSync'],
        vulnerableArg: 0,
      },
    ],
    expectedSanitizers: ['quote', 'escape', 'shell-quote'],
    description: 'OS command execution via shell - highly vulnerable to injection',
    enabled: true,
    tags: ['command', 'injection', 'shell', 'os'],
    relatedCWE: ['CWE-78', 'CWE-77'],
    owaspCategory: 'A03:2021-Injection',
  },

  // child_process spawn (safer but still vulnerable)
  {
    id: 'SNK-CMD-010',
    name: 'OS Command Execution (spawn)',
    category: 'command-exec',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'child_process', method: 'spawn', vulnerableArg: 0 },
      { receiver: 'child_process', method: 'spawn', vulnerableArgs: [0, 1] },
      { method: 'spawn', vulnerableArg: 0 },
      { method: 'spawnSync', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validateCommand', 'whitelist'],
    description: 'OS command execution via spawn - arguments passed directly',
    enabled: true,
    tags: ['command', 'injection', 'spawn', 'os'],
    relatedCWE: ['CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },

  // child_process execFile
  {
    id: 'SNK-CMD-020',
    name: 'OS Command Execution (execFile)',
    category: 'command-exec',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'child_process', method: 'execFile', vulnerableArg: 0 },
      { receiver: 'child_process', method: 'execFile', vulnerableArgs: [0, 1] },
      { method: 'execFile', vulnerableArg: 0 },
      { method: 'execFileSync', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validateCommand', 'whitelist'],
    description: 'OS command execution via execFile',
    enabled: true,
    tags: ['command', 'injection', 'execFile', 'os'],
    relatedCWE: ['CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },

  // child_process fork
  {
    id: 'SNK-CMD-030',
    name: 'Child Process Fork',
    category: 'command-exec',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'child_process', method: 'fork', vulnerableArg: 0 },
      { method: 'fork', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validatePath', 'whitelist'],
    description: 'Node.js child process fork - script path vulnerability',
    enabled: true,
    tags: ['command', 'injection', 'fork', 'os'],
    relatedCWE: ['CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },

  // execa (popular npm package)
  {
    id: 'SNK-CMD-040',
    name: 'Execa Command Execution',
    category: 'command-exec',
    severity: 'critical',
    framework: 'execa',
    patterns: [
      { method: 'execa', vulnerableArg: 0 },
      { method: 'execaSync', vulnerableArg: 0 },
      { method: 'execaCommand', vulnerableArg: 0 },
      { method: 'execaCommandSync', vulnerableArg: 0 },
      { method: '$', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escape', 'validateCommand'],
    description: 'Execa command execution',
    enabled: true,
    tags: ['command', 'injection', 'execa', 'os'],
    relatedCWE: ['CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },

  // shelljs
  {
    id: 'SNK-CMD-050',
    name: 'ShellJS Command Execution',
    category: 'command-exec',
    severity: 'critical',
    framework: 'shelljs',
    patterns: [
      { receiver: 'shell', method: 'exec', vulnerableArg: 0 },
      { receiver: 'shelljs', method: 'exec', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escape', 'quote'],
    description: 'ShellJS command execution',
    enabled: true,
    tags: ['command', 'injection', 'shelljs', 'os'],
    relatedCWE: ['CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },

  // SSH command execution
  {
    id: 'SNK-CMD-060',
    name: 'SSH Command Execution',
    category: 'command-exec',
    severity: 'critical',
    framework: 'ssh',
    patterns: [
      { receiver: 'ssh', method: 'exec', vulnerableArg: 0 },
      { receiver: 'conn', method: 'exec', vulnerableArg: 0 },
      { receiver: 'client', method: 'exec', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escape', 'quote', 'validateCommand'],
    description: 'Remote SSH command execution',
    enabled: true,
    tags: ['command', 'injection', 'ssh', 'remote'],
    relatedCWE: ['CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Docker command execution
  {
    id: 'SNK-CMD-070',
    name: 'Docker Command Execution',
    category: 'command-exec',
    severity: 'critical',
    framework: 'docker',
    patterns: [
      { receiver: 'container', method: 'exec', vulnerableArg: 0 },
      { receiver: 'docker', method: 'run', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validateImage', 'validateCommand'],
    description: 'Docker container command execution',
    enabled: true,
    tags: ['command', 'injection', 'docker', 'container'],
    relatedCWE: ['CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Template engine command execution
  {
    id: 'SNK-CMD-080',
    name: 'Template Command Execution',
    category: 'command-exec',
    severity: 'high',
    patterns: [
      { method: 'compile', vulnerableArg: 0 },
      { method: 'render', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeHtml', 'sandbox'],
    description: 'Template engine with potential command execution',
    enabled: true,
    tags: ['command', 'injection', 'template', 'ssti'],
    relatedCWE: ['CWE-94', 'CWE-78'],
    owaspCategory: 'A03:2021-Injection',
  },
] as const;
