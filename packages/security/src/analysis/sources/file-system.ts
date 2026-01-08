/**
 * @fileoverview File system source definitions
 * @module @nahisaho/musubix-security/analysis/sources/file-system
 * @trace REQ-SEC-001
 */

import type { SourceDefinition } from './types.js';

/**
 * File system sources - file reads that may contain user-controlled data
 * @trace REQ-SEC-001
 */
export const FILE_SYSTEM_SOURCES: readonly SourceDefinition[] = [
  // Node.js fs module
  {
    id: 'SRC-FS-001',
    name: 'Node.js File Read',
    category: 'file-system',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'readFile', taintedReturn: true },
      { receiver: 'fs', method: 'readFileSync', taintedReturn: true },
      { receiver: 'fs', method: 'read', taintedReturn: true },
      { receiver: 'fs', method: 'readSync', taintedReturn: true },
      {
        importPattern: { module: 'fs', named: ['readFile', 'readFileSync'] },
        method: ['readFile', 'readFileSync'],
        taintedReturn: true,
      },
    ],
    description: 'Node.js fs module file read',
    confidence: 0.75,
    enabled: true,
    tags: ['filesystem', 'node', 'read'],
    relatedCWE: ['CWE-20', 'CWE-22'],
  },

  // Node.js fs/promises
  {
    id: 'SRC-FS-002',
    name: 'Node.js Promise File Read',
    category: 'file-system',
    framework: 'node',
    patterns: [
      { receiver: 'fsPromises', method: 'readFile', taintedReturn: true },
      { receiver: 'fs', method: 'readFile', taintedReturn: true },
      {
        importPattern: { module: 'fs/promises', named: ['readFile'] },
        method: 'readFile',
        taintedReturn: true,
      },
    ],
    description: 'Node.js fs/promises file read',
    confidence: 0.75,
    enabled: true,
    tags: ['filesystem', 'node', 'read', 'promise'],
    relatedCWE: ['CWE-20', 'CWE-22'],
  },

  // Stream reads
  {
    id: 'SRC-FS-010',
    name: 'Node.js Stream Read',
    category: 'file-system',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'createReadStream', taintedReturn: true },
      { receiver: 'stream', method: 'on', taintedArg: 1 },
      { receiver: 'readable', method: 'read', taintedReturn: true },
    ],
    description: 'Node.js stream file read',
    confidence: 0.7,
    enabled: true,
    tags: ['filesystem', 'node', 'stream'],
    relatedCWE: ['CWE-20', 'CWE-22'],
  },

  // Directory reads
  {
    id: 'SRC-FS-020',
    name: 'Node.js Directory Read',
    category: 'file-system',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'readdir', taintedReturn: true },
      { receiver: 'fs', method: 'readdirSync', taintedReturn: true },
      { receiver: 'fs', method: 'opendir', taintedReturn: true },
      { receiver: 'fs', method: 'opendirSync', taintedReturn: true },
    ],
    description: 'Node.js directory listing',
    confidence: 0.6,
    enabled: true,
    tags: ['filesystem', 'node', 'directory'],
    relatedCWE: ['CWE-20', 'CWE-22'],
  },

  // JSON file reads (common pattern)
  {
    id: 'SRC-FS-030',
    name: 'JSON File Read',
    category: 'file-system',
    framework: 'node',
    patterns: [
      { receiver: 'JSON', method: 'parse', taintedArg: 0 },
    ],
    description: 'JSON.parse of file contents',
    confidence: 0.7,
    enabled: true,
    tags: ['filesystem', 'json', 'parse'],
    relatedCWE: ['CWE-20', 'CWE-502'],
  },

  // Config file reads
  {
    id: 'SRC-FS-040',
    name: 'Config File Read',
    category: 'config',
    framework: 'node',
    patterns: [
      { method: 'require', taintedReturn: true },
      {
        importPattern: { module: /\.(json|ya?ml|toml)$/ },
        taintedReturn: true,
      },
    ],
    description: 'Configuration file imports',
    confidence: 0.5,
    enabled: true,
    tags: ['filesystem', 'config', 'import'],
    relatedCWE: ['CWE-20'],
  },

  // fs-extra
  {
    id: 'SRC-FS-050',
    name: 'fs-extra File Read',
    category: 'file-system',
    framework: 'fs-extra',
    patterns: [
      { receiver: 'fs', method: 'readFile', taintedReturn: true },
      { receiver: 'fs', method: 'readJson', taintedReturn: true },
      { receiver: 'fs', method: 'readJSON', taintedReturn: true },
      { receiver: 'fse', method: 'readFile', taintedReturn: true },
      { receiver: 'fse', method: 'readJson', taintedReturn: true },
    ],
    description: 'fs-extra file read operations',
    confidence: 0.75,
    enabled: true,
    tags: ['filesystem', 'fs-extra', 'read'],
    relatedCWE: ['CWE-20', 'CWE-22'],
  },

  // glob file reads
  {
    id: 'SRC-FS-060',
    name: 'Glob Pattern Result',
    category: 'file-system',
    framework: 'glob',
    patterns: [
      { method: 'glob', taintedReturn: true },
      { method: 'globSync', taintedReturn: true },
      { receiver: 'glob', method: 'sync', taintedReturn: true },
    ],
    description: 'Glob pattern file matching results',
    confidence: 0.6,
    enabled: true,
    tags: ['filesystem', 'glob', 'pattern'],
    relatedCWE: ['CWE-20', 'CWE-22'],
  },

  // File upload (multer, formidable)
  {
    id: 'SRC-FS-070',
    name: 'File Upload Data',
    category: 'file-system',
    framework: 'express',
    patterns: [
      { receiver: 'req', property: 'file', taintedReturn: true },
      { receiver: 'req', property: 'files', taintedReturn: true },
      { property: 'originalname', taintedReturn: true },
      { property: 'filename', taintedReturn: true },
      { property: 'path', taintedReturn: true },
    ],
    description: 'Uploaded file data (multer/formidable)',
    confidence: 0.95,
    enabled: true,
    tags: ['filesystem', 'upload', 'express'],
    relatedCWE: ['CWE-20', 'CWE-22', 'CWE-434'],
  },
] as const;
