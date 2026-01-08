/**
 * @fileoverview Input validation sanitizer definitions
 * @module @nahisaho/musubix-security/analysis/sanitizers/validation-sanitizers
 * @trace REQ-SEC-001
 */

import type { SanitizerDefinition } from './types.js';

/**
 * Input validation sanitizers
 * @trace REQ-SEC-001
 */
export const VALIDATION_SANITIZERS: readonly SanitizerDefinition[] = [
  // validator.js - escape
  {
    id: 'SAN-VAL-001',
    name: 'escape',
    package: 'validator',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'validator.escape - escapes HTML entities',
    enabled: true,
    tags: ['validator', 'escape', 'html-output'],
  },

  // validator.js - isEmail
  {
    id: 'SAN-VAL-010',
    name: 'isEmail',
    package: 'validator',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: false,
    description: 'validator.isEmail - validates email format',
    enabled: true,
    tags: ['validator', 'email', 'format'],
  },

  // validator.js - isURL
  {
    id: 'SAN-VAL-020',
    name: 'isURL',
    package: 'validator',
    protects: ['http-request', 'redirect'],
    completeness: 'partial',
    returnsClean: false,
    description: 'validator.isURL - validates URL format',
    caveats: 'Does not prevent SSRF to internal hosts',
    enabled: true,
    tags: ['validator', 'url', 'format'],
  },

  // validator.js - isInt/isNumeric
  {
    id: 'SAN-VAL-030',
    name: 'isInt',
    aliases: ['isNumeric', 'isFloat', 'isDecimal'],
    package: 'validator',
    protects: ['sql-query', 'command-exec'],
    completeness: 'complete',
    returnsClean: false,
    description: 'validator numeric validation',
    enabled: true,
    tags: ['validator', 'numeric', 'format'],
  },

  // validator.js - isUUID
  {
    id: 'SAN-VAL-040',
    name: 'isUUID',
    package: 'validator',
    protects: ['sql-query', 'command-exec'],
    completeness: 'complete',
    returnsClean: false,
    description: 'validator.isUUID - validates UUID format',
    enabled: true,
    tags: ['validator', 'uuid', 'format'],
  },

  // validator.js - isAlphanumeric
  {
    id: 'SAN-VAL-050',
    name: 'isAlphanumeric',
    aliases: ['isAlpha', 'isAscii'],
    package: 'validator',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: false,
    description: 'validator alphanumeric validation',
    enabled: true,
    tags: ['validator', 'alphanumeric', 'format'],
  },

  // validator.js - whitelist
  {
    id: 'SAN-VAL-060',
    name: 'whitelist',
    package: 'validator',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'validator.whitelist - removes non-whitelisted chars',
    enabled: true,
    tags: ['validator', 'whitelist', 'filter'],
  },

  // validator.js - blacklist
  {
    id: 'SAN-VAL-070',
    name: 'blacklist',
    package: 'validator',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'partial',
    returnsClean: true,
    description: 'validator.blacklist - removes blacklisted chars',
    caveats: 'Blacklist approach may miss new attack vectors',
    enabled: true,
    tags: ['validator', 'blacklist', 'filter'],
  },

  // validator.js - trim/stripLow
  {
    id: 'SAN-VAL-080',
    name: 'trim',
    aliases: ['ltrim', 'rtrim', 'stripLow'],
    package: 'validator',
    protects: ['sql-query', 'command-exec'],
    completeness: 'partial',
    returnsClean: true,
    description: 'validator trim functions',
    caveats: 'Only removes whitespace/control chars',
    enabled: true,
    tags: ['validator', 'trim', 'filter'],
  },

  // Zod schema validation
  {
    id: 'SAN-VAL-090',
    name: 'parse',
    aliases: ['safeParse', 'parseAsync', 'safeParseAsync'],
    package: 'zod',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Zod schema validation',
    enabled: true,
    tags: ['zod', 'schema', 'validate'],
  },

  // Yup schema validation
  {
    id: 'SAN-VAL-100',
    name: 'validate',
    aliases: ['validateSync', 'isValid', 'isValidSync'],
    package: 'yup',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Yup schema validation',
    enabled: true,
    tags: ['yup', 'schema', 'validate'],
  },

  // Joi schema validation
  {
    id: 'SAN-VAL-110',
    name: 'validate',
    aliases: ['validateAsync', 'attempt'],
    package: 'joi',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Joi schema validation',
    enabled: true,
    tags: ['joi', 'schema', 'validate'],
  },

  // io-ts codec validation
  {
    id: 'SAN-VAL-120',
    name: 'decode',
    aliases: ['is'],
    package: 'io-ts',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'io-ts codec validation',
    enabled: true,
    tags: ['io-ts', 'codec', 'validate'],
  },

  // superstruct validation
  {
    id: 'SAN-VAL-130',
    name: 'create',
    aliases: ['validate', 'assert', 'is'],
    package: 'superstruct',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'superstruct validation',
    enabled: true,
    tags: ['superstruct', 'schema', 'validate'],
  },

  // class-validator
  {
    id: 'SAN-VAL-140',
    name: 'validate',
    aliases: ['validateSync', 'validateOrReject'],
    package: 'class-validator',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'class-validator validation',
    enabled: true,
    tags: ['class-validator', 'decorator', 'validate'],
  },

  // parseInt/parseFloat
  {
    id: 'SAN-VAL-150',
    name: 'parseInt',
    aliases: ['parseFloat', 'Number'],
    protects: ['sql-query', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'JavaScript numeric parsing',
    caveats: 'Check for NaN after parsing',
    enabled: true,
    tags: ['javascript', 'parse', 'number'],
  },

  // JSON.parse (structural validation)
  {
    id: 'SAN-VAL-160',
    name: 'parse',
    package: 'JSON',
    protects: ['sql-query', 'command-exec'],
    completeness: 'partial',
    returnsClean: false,
    description: 'JSON.parse structural validation',
    caveats: 'Only validates JSON structure, not content',
    enabled: true,
    tags: ['json', 'parse', 'validate'],
  },

  // UUID generation (safe replacement)
  {
    id: 'SAN-VAL-170',
    name: 'v4',
    aliases: ['v1', 'v5', 'randomUUID'],
    package: 'uuid',
    protects: ['sql-query', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'UUID generation as safe ID replacement',
    enabled: true,
    tags: ['uuid', 'generate', 'safe'],
  },

  // Regex test with safe pattern
  {
    id: 'SAN-VAL-180',
    name: 'test',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'conditional',
    returnsClean: false,
    description: 'RegExp.test for input validation',
    caveats: 'Depends on regex pattern quality',
    enabled: true,
    tags: ['regex', 'test', 'validate'],
  },

  // ajv JSON Schema validation
  {
    id: 'SAN-VAL-190',
    name: 'validate',
    aliases: ['compile'],
    package: 'ajv',
    protects: ['sql-query', 'html-output', 'command-exec'],
    completeness: 'complete',
    returnsClean: true,
    description: 'AJV JSON Schema validation',
    enabled: true,
    tags: ['ajv', 'jsonschema', 'validate'],
  },
] as const;
