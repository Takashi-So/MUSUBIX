/**
 * @fileoverview Path traversal sanitizer definitions
 * @module @nahisaho/musubix-security/analysis/sanitizers/path-sanitizers
 * @trace REQ-SEC-001
 */

import type { SanitizerDefinition } from './types.js';

/**
 * Path traversal sanitizers
 * @trace REQ-SEC-001
 */
export const PATH_SANITIZERS: readonly SanitizerDefinition[] = [
  // path.basename - removes directory components
  {
    id: 'SAN-PATH-001',
    name: 'basename',
    package: 'path',
    protects: ['file-read', 'file-write'],
    completeness: 'partial',
    returnsClean: true,
    description: 'path.basename - removes directory components',
    caveats: 'Only removes directory path, does not prevent all traversal',
    enabled: true,
    tags: ['path', 'basename', 'traversal'],
  },

  // path.normalize
  {
    id: 'SAN-PATH-010',
    name: 'normalize',
    package: 'path',
    protects: ['file-read', 'file-write'],
    completeness: 'partial',
    returnsClean: true,
    description: 'path.normalize - resolves . and .. segments',
    caveats: 'Resolves .. but does not prevent traversal outside base',
    enabled: true,
    tags: ['path', 'normalize', 'traversal'],
  },

  // path.resolve
  {
    id: 'SAN-PATH-020',
    name: 'resolve',
    package: 'path',
    protects: ['file-read', 'file-write'],
    completeness: 'partial',
    returnsClean: true,
    description: 'path.resolve - resolves to absolute path',
    caveats: 'Creates absolute path but does not prevent traversal',
    enabled: true,
    tags: ['path', 'resolve', 'traversal'],
  },

  // Custom path validation
  {
    id: 'SAN-PATH-030',
    name: 'validatePath',
    aliases: ['isValidPath', 'checkPath', 'sanitizePath'],
    protects: ['file-read', 'file-write'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Custom path validation function',
    enabled: true,
    tags: ['path', 'validate', 'traversal'],
  },

  // startsWith check pattern
  {
    id: 'SAN-PATH-040',
    name: 'startsWith',
    protects: ['file-read', 'file-write'],
    completeness: 'conditional',
    returnsClean: false,
    description: 'Path prefix check with startsWith',
    caveats: 'Must be combined with resolve/normalize to be effective',
    enabled: true,
    tags: ['path', 'startsWith', 'check'],
  },

  // within base directory check
  {
    id: 'SAN-PATH-050',
    name: 'isWithinBase',
    aliases: ['isInsideDirectory', 'isSubPath', 'isInside'],
    protects: ['file-read', 'file-write'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Check if path is within allowed base directory',
    enabled: true,
    tags: ['path', 'base', 'check'],
  },

  // realpath
  {
    id: 'SAN-PATH-060',
    name: 'realpath',
    aliases: ['realpathSync'],
    package: 'fs',
    protects: ['file-read', 'file-write'],
    completeness: 'partial',
    returnsClean: true,
    description: 'fs.realpath - resolves symlinks',
    caveats: 'Resolves symlinks but should be combined with base check',
    enabled: true,
    tags: ['path', 'realpath', 'symlink'],
  },

  // path-is-inside package
  {
    id: 'SAN-PATH-070',
    name: 'pathIsInside',
    package: 'path-is-inside',
    protects: ['file-read', 'file-write'],
    completeness: 'complete',
    returnsClean: true,
    description: 'path-is-inside package',
    enabled: true,
    tags: ['path', 'inside', 'check'],
  },

  // sanitize-filename package
  {
    id: 'SAN-PATH-080',
    name: 'sanitize',
    aliases: ['sanitizeFilename'],
    package: 'sanitize-filename',
    protects: ['file-read', 'file-write'],
    completeness: 'complete',
    returnsClean: true,
    description: 'sanitize-filename - removes dangerous characters',
    enabled: true,
    tags: ['path', 'filename', 'sanitize'],
  },

  // filenamify package
  {
    id: 'SAN-PATH-090',
    name: 'filenamify',
    package: 'filenamify',
    protects: ['file-read', 'file-write'],
    completeness: 'complete',
    returnsClean: true,
    description: 'filenamify - converts string to safe filename',
    enabled: true,
    tags: ['path', 'filename', 'sanitize'],
  },

  // Extension validation
  {
    id: 'SAN-PATH-100',
    name: 'validateExtension',
    aliases: ['checkExtension', 'allowedExtensions'],
    protects: ['file-read', 'file-write'],
    completeness: 'partial',
    returnsClean: true,
    description: 'File extension whitelist validation',
    caveats: 'Only validates extension, not path traversal',
    enabled: true,
    tags: ['path', 'extension', 'validate'],
  },

  // Zip Slip protection
  {
    id: 'SAN-PATH-110',
    name: 'checkZipSlip',
    aliases: ['validateZipEntry', 'preventZipSlip'],
    protects: ['file-write'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Zip Slip vulnerability protection',
    enabled: true,
    tags: ['path', 'zip', 'slip'],
  },
] as const;
