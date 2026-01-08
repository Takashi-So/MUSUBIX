/**
 * @fileoverview Environment source definitions
 * @module @nahisaho/musubix-security/analysis/sources/environment
 * @trace REQ-SEC-001
 */

import type { SourceDefinition } from './types.js';

/**
 * Environment sources - environment variables, CLI args
 * @trace REQ-SEC-001
 */
export const ENVIRONMENT_SOURCES: readonly SourceDefinition[] = [
  // Process environment
  {
    id: 'SRC-ENV-001',
    name: 'Environment Variables',
    category: 'environment',
    framework: 'node',
    patterns: [
      { receiver: 'process', property: 'env', taintedReturn: true },
    ],
    description: 'Node.js process.env environment variables',
    confidence: 0.6,
    enabled: true,
    tags: ['environment', 'node', 'env'],
    relatedCWE: ['CWE-20', 'CWE-78'],
  },

  // CLI arguments
  {
    id: 'SRC-ENV-010',
    name: 'CLI Arguments',
    category: 'cli-args',
    framework: 'node',
    patterns: [
      { receiver: 'process', property: 'argv', taintedReturn: true },
    ],
    description: 'Command line arguments',
    confidence: 0.8,
    enabled: true,
    tags: ['environment', 'node', 'argv', 'cli'],
    relatedCWE: ['CWE-20', 'CWE-78', 'CWE-88'],
  },

  // yargs
  {
    id: 'SRC-ENV-020',
    name: 'Yargs Arguments',
    category: 'cli-args',
    framework: 'yargs',
    patterns: [
      { receiver: 'yargs', method: 'parse', taintedReturn: true },
      { receiver: 'yargs', method: 'argv', taintedReturn: true },
      { property: 'argv', taintedReturn: true },
    ],
    description: 'Yargs parsed arguments',
    confidence: 0.8,
    enabled: true,
    tags: ['environment', 'yargs', 'cli'],
    relatedCWE: ['CWE-20', 'CWE-78', 'CWE-88'],
  },

  // commander
  {
    id: 'SRC-ENV-030',
    name: 'Commander Arguments',
    category: 'cli-args',
    framework: 'commander',
    patterns: [
      { receiver: 'program', method: 'opts', taintedReturn: true },
      { receiver: 'program', property: 'args', taintedReturn: true },
      { receiver: 'command', method: 'opts', taintedReturn: true },
    ],
    description: 'Commander parsed arguments',
    confidence: 0.8,
    enabled: true,
    tags: ['environment', 'commander', 'cli'],
    relatedCWE: ['CWE-20', 'CWE-78', 'CWE-88'],
  },

  // minimist
  {
    id: 'SRC-ENV-040',
    name: 'Minimist Arguments',
    category: 'cli-args',
    framework: 'minimist',
    patterns: [
      { method: 'minimist', taintedReturn: true },
    ],
    description: 'Minimist parsed arguments',
    confidence: 0.8,
    enabled: true,
    tags: ['environment', 'minimist', 'cli'],
    relatedCWE: ['CWE-20', 'CWE-78', 'CWE-88'],
  },

  // dotenv
  {
    id: 'SRC-ENV-050',
    name: 'Dotenv Variables',
    category: 'environment',
    framework: 'dotenv',
    patterns: [
      { receiver: 'dotenv', method: 'config', taintedReturn: true },
      { receiver: 'dotenv', method: 'parse', taintedReturn: true },
    ],
    description: 'Dotenv parsed environment variables',
    confidence: 0.6,
    enabled: true,
    tags: ['environment', 'dotenv'],
    relatedCWE: ['CWE-20'],
  },

  // Stdin
  {
    id: 'SRC-ENV-060',
    name: 'Standard Input',
    category: 'cli-args',
    framework: 'node',
    patterns: [
      { receiver: 'process', property: 'stdin', taintedReturn: true },
      { receiver: 'stdin', method: 'on', taintedArg: 1 },
      { receiver: 'readline', method: 'question', taintedArg: 1 },
    ],
    description: 'Standard input data',
    confidence: 0.9,
    enabled: true,
    tags: ['environment', 'stdin', 'cli'],
    relatedCWE: ['CWE-20', 'CWE-78'],
  },

  // Electron
  {
    id: 'SRC-ENV-070',
    name: 'Electron App Path',
    category: 'environment',
    framework: 'electron',
    patterns: [
      { receiver: 'app', method: 'getPath', taintedReturn: true },
      { receiver: 'app', method: 'getAppPath', taintedReturn: true },
    ],
    description: 'Electron app path functions',
    confidence: 0.5,
    enabled: true,
    tags: ['environment', 'electron'],
    relatedCWE: ['CWE-20', 'CWE-22'],
  },

  // OS module
  {
    id: 'SRC-ENV-080',
    name: 'OS Information',
    category: 'environment',
    framework: 'node',
    patterns: [
      { receiver: 'os', method: 'hostname', taintedReturn: true },
      { receiver: 'os', method: 'userInfo', taintedReturn: true },
      { receiver: 'os', method: 'homedir', taintedReturn: true },
      { receiver: 'os', method: 'tmpdir', taintedReturn: true },
    ],
    description: 'OS module information',
    confidence: 0.4,
    enabled: true,
    tags: ['environment', 'os', 'node'],
    relatedCWE: ['CWE-200'],
  },
] as const;
