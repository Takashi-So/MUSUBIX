/**
 * @fileoverview Command execution sanitizer definitions
 * @module @nahisaho/musubix-security/analysis/sanitizers/command-sanitizers
 * @trace REQ-SEC-001
 */

import type { SanitizerDefinition } from './types.js';

/**
 * Command injection sanitizers
 * @trace REQ-SEC-001
 */
export const COMMAND_SANITIZERS: readonly SanitizerDefinition[] = [
  // shell-quote package
  {
    id: 'SAN-CMD-001',
    name: 'quote',
    package: 'shell-quote',
    protects: ['command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'shell-quote quote function - escapes shell arguments',
    enabled: true,
    tags: ['command', 'shell', 'quote'],
  },
  {
    id: 'SAN-CMD-002',
    name: 'escape',
    package: 'shell-quote',
    protects: ['command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'shell-quote escape function',
    enabled: true,
    tags: ['command', 'shell', 'escape'],
  },

  // shell-escape package
  {
    id: 'SAN-CMD-010',
    name: 'shellEscape',
    aliases: ['shell-escape'],
    package: 'shell-escape',
    protects: ['command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'shell-escape package',
    enabled: true,
    tags: ['command', 'shell', 'escape'],
  },

  // any-shell-escape
  {
    id: 'SAN-CMD-020',
    name: 'shellescape',
    package: 'any-shell-escape',
    protects: ['command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'any-shell-escape package',
    enabled: true,
    tags: ['command', 'shell', 'escape'],
  },

  // Generic escape patterns
  {
    id: 'SAN-CMD-030',
    name: 'escapeShell',
    aliases: ['escapeShellArg', 'escapeShellCmd'],
    protects: ['command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Generic shell escape function',
    enabled: true,
    tags: ['command', 'shell', 'escape'],
  },

  // Argument array (spawn-style - safer)
  {
    id: 'SAN-CMD-040',
    name: 'spawn',
    aliases: ['spawnSync'],
    protects: ['command-exec'],
    completeness: 'conditional',
    returnsClean: false,
    description: 'Using spawn with argument array instead of exec',
    caveats: 'Only safe if shell option is false and args are separate',
    enabled: true,
    tags: ['command', 'spawn', 'array'],
  },

  // execFile (safer than exec)
  {
    id: 'SAN-CMD-050',
    name: 'execFile',
    aliases: ['execFileSync'],
    protects: ['command-exec'],
    completeness: 'conditional',
    returnsClean: false,
    description: 'Using execFile with argument array',
    caveats: 'Only safe if file path is controlled and args are separate',
    enabled: true,
    tags: ['command', 'execFile', 'array'],
  },

  // Command whitelist pattern
  {
    id: 'SAN-CMD-060',
    name: 'validateCommand',
    aliases: ['allowedCommands', 'commandWhitelist'],
    protects: ['command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Command whitelist validation',
    enabled: true,
    tags: ['command', 'whitelist', 'validate'],
  },

  // Execa options
  {
    id: 'SAN-CMD-070',
    name: 'execa',
    package: 'execa',
    protects: ['command-exec'],
    completeness: 'conditional',
    returnsClean: false,
    description: 'Execa with array arguments',
    caveats: 'Only safe when using array form, not string command',
    enabled: true,
    tags: ['command', 'execa', 'array'],
  },
] as const;
