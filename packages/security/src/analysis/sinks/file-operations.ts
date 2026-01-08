/**
 * @fileoverview File operation sink definitions
 * @module @nahisaho/musubix-security/analysis/sinks/file-operations
 * @trace REQ-SEC-001
 */

import type { SinkDefinition } from './types.js';

/**
 * File operation sinks (path traversal, arbitrary file write)
 * @trace REQ-SEC-001
 */
export const FILE_OPERATION_SINKS: readonly SinkDefinition[] = [
  // File read (path traversal)
  {
    id: 'SNK-FILE-001',
    name: 'File Read (Path Traversal)',
    category: 'file-read',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'readFile', vulnerableArg: 0 },
      { receiver: 'fs', method: 'readFileSync', vulnerableArg: 0 },
      { receiver: 'fs', method: 'createReadStream', vulnerableArg: 0 },
      { method: 'readFile', vulnerableArg: 0 },
      { method: 'readFileSync', vulnerableArg: 0 },
      {
        importPattern: { module: 'fs', named: ['readFile', 'readFileSync'] },
        method: ['readFile', 'readFileSync'],
        vulnerableArg: 0,
      },
    ],
    expectedSanitizers: ['basename', 'resolve', 'validatePath', 'normalize'],
    description: 'File read with user-controlled path - path traversal risk',
    enabled: true,
    tags: ['file', 'read', 'path-traversal'],
    relatedCWE: ['CWE-22', 'CWE-23'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // File write (arbitrary file write)
  {
    id: 'SNK-FILE-010',
    name: 'File Write (Arbitrary Write)',
    category: 'file-write',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'writeFile', vulnerableArg: 0 },
      { receiver: 'fs', method: 'writeFileSync', vulnerableArg: 0 },
      { receiver: 'fs', method: 'createWriteStream', vulnerableArg: 0 },
      { receiver: 'fs', method: 'appendFile', vulnerableArg: 0 },
      { receiver: 'fs', method: 'appendFileSync', vulnerableArg: 0 },
      { method: 'writeFile', vulnerableArg: 0 },
      { method: 'writeFileSync', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['basename', 'resolve', 'validatePath', 'normalize'],
    description: 'File write with user-controlled path - arbitrary file write risk',
    enabled: true,
    tags: ['file', 'write', 'arbitrary-write'],
    relatedCWE: ['CWE-22', 'CWE-23', 'CWE-73'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // fs-extra operations
  {
    id: 'SNK-FILE-020',
    name: 'fs-extra File Operations',
    category: 'file-write',
    severity: 'high',
    framework: 'fs-extra',
    patterns: [
      { receiver: 'fse', method: 'copy', vulnerableArgs: [0, 1] },
      { receiver: 'fse', method: 'move', vulnerableArgs: [0, 1] },
      { receiver: 'fse', method: 'outputFile', vulnerableArg: 0 },
      { receiver: 'fse', method: 'outputJson', vulnerableArg: 0 },
      { receiver: 'fs', method: 'copy', vulnerableArgs: [0, 1] },
      { receiver: 'fs', method: 'move', vulnerableArgs: [0, 1] },
    ],
    expectedSanitizers: ['validatePath', 'normalize', 'basename'],
    description: 'fs-extra file operations with user-controlled paths',
    enabled: true,
    tags: ['file', 'fs-extra', 'path-traversal'],
    relatedCWE: ['CWE-22', 'CWE-73'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // Directory operations
  {
    id: 'SNK-FILE-030',
    name: 'Directory Creation/Removal',
    category: 'file-write',
    severity: 'medium',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'mkdir', vulnerableArg: 0 },
      { receiver: 'fs', method: 'mkdirSync', vulnerableArg: 0 },
      { receiver: 'fs', method: 'rmdir', vulnerableArg: 0 },
      { receiver: 'fs', method: 'rmdirSync', vulnerableArg: 0 },
      { receiver: 'fs', method: 'rm', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validatePath', 'normalize'],
    description: 'Directory operations with user-controlled paths',
    enabled: true,
    tags: ['file', 'directory', 'path-traversal'],
    relatedCWE: ['CWE-22'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // File deletion
  {
    id: 'SNK-FILE-040',
    name: 'File Deletion',
    category: 'file-write',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'unlink', vulnerableArg: 0 },
      { receiver: 'fs', method: 'unlinkSync', vulnerableArg: 0 },
      { method: 'unlink', vulnerableArg: 0 },
      { method: 'unlinkSync', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validatePath', 'normalize', 'basename'],
    description: 'File deletion with user-controlled path',
    enabled: true,
    tags: ['file', 'delete', 'path-traversal'],
    relatedCWE: ['CWE-22', 'CWE-73'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // File access check (information disclosure)
  {
    id: 'SNK-FILE-050',
    name: 'File Access Check',
    category: 'file-read',
    severity: 'medium',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'access', vulnerableArg: 0 },
      { receiver: 'fs', method: 'accessSync', vulnerableArg: 0 },
      { receiver: 'fs', method: 'stat', vulnerableArg: 0 },
      { receiver: 'fs', method: 'statSync', vulnerableArg: 0 },
      { receiver: 'fs', method: 'lstat', vulnerableArg: 0 },
      { receiver: 'fs', method: 'exists', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validatePath', 'normalize'],
    description: 'File access check - can reveal file existence',
    enabled: true,
    tags: ['file', 'info-disclosure', 'path-traversal'],
    relatedCWE: ['CWE-22', 'CWE-200'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // Path join (common anti-pattern)
  {
    id: 'SNK-FILE-060',
    name: 'Unsafe Path Join',
    category: 'file-read',
    severity: 'medium',
    framework: 'node',
    patterns: [
      { receiver: 'path', method: 'join', vulnerableArg: 1 },
      { receiver: 'path', method: 'resolve', vulnerableArg: 1 },
    ],
    expectedSanitizers: ['basename', 'validatePath'],
    description: 'Path join with user-controlled segment - does not prevent traversal',
    enabled: true,
    tags: ['file', 'path', 'path-traversal'],
    relatedCWE: ['CWE-22'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // Symlink operations
  {
    id: 'SNK-FILE-070',
    name: 'Symlink Creation',
    category: 'file-write',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'symlink', vulnerableArgs: [0, 1] },
      { receiver: 'fs', method: 'symlinkSync', vulnerableArgs: [0, 1] },
      { receiver: 'fs', method: 'link', vulnerableArgs: [0, 1] },
      { receiver: 'fs', method: 'linkSync', vulnerableArgs: [0, 1] },
    ],
    expectedSanitizers: ['validatePath', 'normalize'],
    description: 'Symlink creation - can be used for path traversal attacks',
    enabled: true,
    tags: ['file', 'symlink', 'path-traversal'],
    relatedCWE: ['CWE-59', 'CWE-22'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // File rename/move
  {
    id: 'SNK-FILE-080',
    name: 'File Rename/Move',
    category: 'file-write',
    severity: 'high',
    framework: 'node',
    patterns: [
      { receiver: 'fs', method: 'rename', vulnerableArgs: [0, 1] },
      { receiver: 'fs', method: 'renameSync', vulnerableArgs: [0, 1] },
    ],
    expectedSanitizers: ['validatePath', 'normalize', 'basename'],
    description: 'File rename with user-controlled paths',
    enabled: true,
    tags: ['file', 'rename', 'path-traversal'],
    relatedCWE: ['CWE-22', 'CWE-73'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // Multer/File upload destination
  {
    id: 'SNK-FILE-090',
    name: 'File Upload Destination',
    category: 'file-write',
    severity: 'high',
    framework: 'express',
    patterns: [
      { property: 'destination', vulnerableArg: 0 },
      { property: 'filename', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['sanitizeFilename', 'basename', 'validateExtension'],
    description: 'File upload destination/filename from user input',
    enabled: true,
    tags: ['file', 'upload', 'path-traversal'],
    relatedCWE: ['CWE-22', 'CWE-434'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // Archiver/Zip extraction (Zip Slip)
  {
    id: 'SNK-FILE-100',
    name: 'Archive Extraction (Zip Slip)',
    category: 'file-write',
    severity: 'critical',
    patterns: [
      { method: 'extract', vulnerableArg: 0 },
      { method: 'extractAll', vulnerableArg: 0 },
      { receiver: 'unzipper', method: 'Extract', vulnerableArg: 0 },
      { receiver: 'archiver', method: 'directory', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validatePath', 'checkZipSlip'],
    description: 'Archive extraction - Zip Slip vulnerability',
    enabled: true,
    tags: ['file', 'archive', 'zip-slip'],
    relatedCWE: ['CWE-22'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },
] as const;
