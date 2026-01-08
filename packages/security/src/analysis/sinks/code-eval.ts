/**
 * @fileoverview Code evaluation sink definitions
 * @module @nahisaho/musubix-security/analysis/sinks/code-eval
 * @trace REQ-SEC-001
 */

import type { SinkDefinition } from './types.js';

/**
 * Code evaluation sinks (RCE vulnerabilities)
 * @trace REQ-SEC-001
 */
export const CODE_EVAL_SINKS: readonly SinkDefinition[] = [
  // JavaScript eval
  {
    id: 'SNK-EVAL-001',
    name: 'JavaScript eval',
    category: 'eval',
    severity: 'critical',
    patterns: [
      { method: 'eval', vulnerableArg: 0 },
    ],
    expectedSanitizers: [],
    description: 'JavaScript eval() - direct code execution',
    enabled: true,
    tags: ['eval', 'rce', 'code-injection'],
    relatedCWE: ['CWE-94', 'CWE-95'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Function constructor
  {
    id: 'SNK-EVAL-010',
    name: 'Function Constructor',
    category: 'eval',
    severity: 'critical',
    patterns: [
      { method: 'Function', vulnerableArg: 0 },
      { receiver: 'Function', method: 'constructor', vulnerableArg: 0 },
    ],
    expectedSanitizers: [],
    description: 'Function constructor - dynamic code creation',
    enabled: true,
    tags: ['eval', 'rce', 'code-injection'],
    relatedCWE: ['CWE-94'],
    owaspCategory: 'A03:2021-Injection',
  },

  // setTimeout/setInterval with string
  {
    id: 'SNK-EVAL-020',
    name: 'Timer String Evaluation',
    category: 'eval',
    severity: 'high',
    framework: 'browser',
    patterns: [
      { method: 'setTimeout', vulnerableArg: 0 },
      { method: 'setInterval', vulnerableArg: 0 },
      { receiver: 'window', method: 'setTimeout', vulnerableArg: 0 },
      { receiver: 'window', method: 'setInterval', vulnerableArg: 0 },
    ],
    expectedSanitizers: [],
    description: 'Timer functions with string argument - code execution',
    enabled: true,
    tags: ['eval', 'timer', 'code-injection'],
    relatedCWE: ['CWE-94'],
    owaspCategory: 'A03:2021-Injection',
  },

  // vm.runInContext (Node.js)
  {
    id: 'SNK-EVAL-030',
    name: 'Node.js VM Execution',
    category: 'eval',
    severity: 'critical',
    framework: 'node',
    patterns: [
      { receiver: 'vm', method: 'runInContext', vulnerableArg: 0 },
      { receiver: 'vm', method: 'runInNewContext', vulnerableArg: 0 },
      { receiver: 'vm', method: 'runInThisContext', vulnerableArg: 0 },
      { receiver: 'vm', method: 'compileFunction', vulnerableArg: 0 },
      { method: 'Script', vulnerableArg: 0 },
    ],
    expectedSanitizers: [],
    description: 'Node.js vm module - sandbox escape possible',
    enabled: true,
    tags: ['eval', 'vm', 'node', 'sandbox'],
    relatedCWE: ['CWE-94'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Deserialization
  {
    id: 'SNK-EVAL-040',
    name: 'Unsafe Deserialization',
    category: 'deserialization',
    severity: 'critical',
    patterns: [
      { method: 'deserialize', vulnerableArg: 0 },
      { method: 'unserialize', vulnerableArg: 0 },
      { receiver: 'serialize', method: 'unserialize', vulnerableArg: 0 },
      { receiver: 'node-serialize', method: 'unserialize', vulnerableArg: 0 },
    ],
    expectedSanitizers: [],
    description: 'Unsafe deserialization - RCE via prototype pollution',
    enabled: true,
    tags: ['deserialization', 'rce', 'prototype-pollution'],
    relatedCWE: ['CWE-502'],
    owaspCategory: 'A08:2021-Software and Data Integrity Failures',
  },

  // YAML parsing (unsafe)
  {
    id: 'SNK-EVAL-050',
    name: 'Unsafe YAML Parsing',
    category: 'deserialization',
    severity: 'critical',
    framework: 'js-yaml',
    patterns: [
      { receiver: 'yaml', method: 'load', vulnerableArg: 0 },
      { receiver: 'YAML', method: 'parse', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['safeLoad', 'JSON_SCHEMA'],
    description: 'Unsafe YAML parsing - code execution via custom tags',
    enabled: true,
    tags: ['yaml', 'deserialization', 'rce'],
    relatedCWE: ['CWE-502'],
    owaspCategory: 'A08:2021-Software and Data Integrity Failures',
  },

  // Regular expression DoS (ReDoS)
  {
    id: 'SNK-EVAL-060',
    name: 'Dynamic Regular Expression',
    category: 'eval',
    severity: 'medium',
    patterns: [
      { method: 'RegExp', vulnerableArg: 0 },
      { receiver: 'RegExp', method: 'constructor', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeRegExp', 'validateRegex'],
    description: 'Dynamic RegExp construction - ReDoS vulnerability',
    enabled: true,
    tags: ['regex', 'redos', 'dos'],
    relatedCWE: ['CWE-1333', 'CWE-400'],
    owaspCategory: 'A03:2021-Injection',
  },

  // LDAP injection
  {
    id: 'SNK-EVAL-070',
    name: 'LDAP Query',
    category: 'ldap-query',
    severity: 'high',
    patterns: [
      { method: 'search', vulnerableArg: 0 },
      { receiver: 'ldap', method: 'search', vulnerableArg: 0 },
      { receiver: 'client', method: 'search', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeLDAP', 'sanitize'],
    description: 'LDAP query with user input - LDAP injection',
    enabled: true,
    tags: ['ldap', 'injection'],
    relatedCWE: ['CWE-90'],
    owaspCategory: 'A03:2021-Injection',
  },

  // XPath injection
  {
    id: 'SNK-EVAL-080',
    name: 'XPath Query',
    category: 'xpath-query',
    severity: 'high',
    patterns: [
      { method: 'select', vulnerableArg: 0 },
      { method: 'evaluate', vulnerableArg: 0 },
      { receiver: 'xpath', method: 'select', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeXPath', 'parameterize'],
    description: 'XPath query with user input - XPath injection',
    enabled: true,
    tags: ['xpath', 'injection', 'xml'],
    relatedCWE: ['CWE-643'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Server-Side Request Forgery (SSRF)
  {
    id: 'SNK-EVAL-090',
    name: 'SSRF via HTTP Request',
    category: 'http-request',
    severity: 'high',
    patterns: [
      { method: 'fetch', vulnerableArg: 0 },
      { receiver: 'axios', method: 'get', vulnerableArg: 0 },
      { receiver: 'axios', method: 'post', vulnerableArg: 0 },
      { receiver: 'http', method: 'get', vulnerableArg: 0 },
      { receiver: 'https', method: 'get', vulnerableArg: 0 },
      { receiver: 'got', method: 'get', vulnerableArg: 0 },
      { receiver: 'request', method: 'get', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validateUrl', 'isAllowedDomain', 'whitelist'],
    description: 'HTTP request with user-controlled URL - SSRF',
    enabled: true,
    tags: ['ssrf', 'http', 'network'],
    relatedCWE: ['CWE-918'],
    owaspCategory: 'A10:2021-Server-Side Request Forgery',
  },

  // Object property access (prototype pollution)
  {
    id: 'SNK-EVAL-100',
    name: 'Dynamic Property Access',
    category: 'eval',
    severity: 'medium',
    patterns: [
      { method: 'assign', vulnerableArg: 1 },
      { receiver: 'Object', method: 'assign', vulnerableArg: 1 },
    ],
    expectedSanitizers: ['sanitizeKeys', 'Object.freeze'],
    description: 'Dynamic property assignment - prototype pollution',
    enabled: true,
    tags: ['prototype-pollution', 'object'],
    relatedCWE: ['CWE-1321'],
    owaspCategory: 'A03:2021-Injection',
  },

  // crypto weak random
  {
    id: 'SNK-EVAL-110',
    name: 'Weak Random Number',
    category: 'eval',
    severity: 'medium',
    patterns: [
      { receiver: 'Math', method: 'random', vulnerableArg: -1 },
    ],
    expectedSanitizers: ['crypto.randomBytes', 'crypto.randomUUID'],
    description: 'Math.random() used for security - weak randomness',
    enabled: true,
    tags: ['crypto', 'random', 'weak'],
    relatedCWE: ['CWE-330', 'CWE-338'],
    owaspCategory: 'A02:2021-Cryptographic Failures',
  },
] as const;
