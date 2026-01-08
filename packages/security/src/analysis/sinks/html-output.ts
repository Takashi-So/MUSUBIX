/**
 * @fileoverview HTML output sink definitions (XSS vulnerabilities)
 * @module @nahisaho/musubix-security/analysis/sinks/html-output
 * @trace REQ-SEC-001
 */

import type { SinkDefinition } from './types.js';

/**
 * HTML output sinks (XSS vulnerabilities)
 * @trace REQ-SEC-001
 */
export const HTML_OUTPUT_SINKS: readonly SinkDefinition[] = [
  // Express response
  {
    id: 'SNK-XSS-001',
    name: 'Express Response Send',
    category: 'html-output',
    severity: 'high',
    framework: 'express',
    patterns: [
      { receiver: 'res', method: 'send', vulnerableArg: 0 },
      { receiver: 'res', method: 'write', vulnerableArg: 0 },
      { receiver: 'response', method: 'send', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeHtml', 'encode', 'sanitizeHtml', 'DOMPurify'],
    description: 'Express response with user data - XSS risk',
    enabled: true,
    tags: ['xss', 'express', 'html'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Template rendering
  {
    id: 'SNK-XSS-010',
    name: 'Template Render',
    category: 'html-output',
    severity: 'high',
    framework: 'express',
    patterns: [
      { receiver: 'res', method: 'render', vulnerableArg: 1 },
      { receiver: 'response', method: 'render', vulnerableArg: 1 },
    ],
    expectedSanitizers: ['escapeHtml', 'template auto-escape'],
    description: 'Template rendering with user data',
    enabled: true,
    tags: ['xss', 'template', 'html'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // innerHTML (DOM XSS)
  {
    id: 'SNK-XSS-020',
    name: 'DOM innerHTML',
    category: 'html-output',
    severity: 'high',
    framework: 'browser',
    patterns: [
      { property: 'innerHTML', vulnerableArg: 0 },
      { property: 'outerHTML', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeHtml', 'DOMPurify', 'sanitizeHtml', 'textContent'],
    description: 'DOM innerHTML assignment - DOM XSS vulnerability',
    enabled: true,
    tags: ['xss', 'dom', 'innerHTML'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // document.write
  {
    id: 'SNK-XSS-030',
    name: 'Document Write',
    category: 'html-output',
    severity: 'high',
    framework: 'browser',
    patterns: [
      { receiver: 'document', method: 'write', vulnerableArg: 0 },
      { receiver: 'document', method: 'writeln', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeHtml', 'DOMPurify'],
    description: 'document.write with user data - XSS vulnerability',
    enabled: true,
    tags: ['xss', 'dom', 'document.write'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // insertAdjacentHTML
  {
    id: 'SNK-XSS-040',
    name: 'Insert Adjacent HTML',
    category: 'html-output',
    severity: 'high',
    framework: 'browser',
    patterns: [
      { method: 'insertAdjacentHTML', vulnerableArg: 1 },
    ],
    expectedSanitizers: ['escapeHtml', 'DOMPurify'],
    description: 'insertAdjacentHTML with user data',
    enabled: true,
    tags: ['xss', 'dom', 'insertAdjacentHTML'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // jQuery html()
  {
    id: 'SNK-XSS-050',
    name: 'jQuery HTML',
    category: 'html-output',
    severity: 'high',
    framework: 'jquery',
    patterns: [
      { receiver: '$', method: 'html', vulnerableArg: 0 },
      { receiver: 'jQuery', method: 'html', vulnerableArg: 0 },
      { method: 'html', vulnerableArg: 0 },
      { receiver: '$', method: 'append', vulnerableArg: 0 },
      { receiver: '$', method: 'prepend', vulnerableArg: 0 },
      { receiver: '$', method: 'after', vulnerableArg: 0 },
      { receiver: '$', method: 'before', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escapeHtml', 'DOMPurify', 'text()'],
    description: 'jQuery HTML manipulation with user data',
    enabled: true,
    tags: ['xss', 'jquery', 'html'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // React dangerouslySetInnerHTML
  {
    id: 'SNK-XSS-060',
    name: 'React DangerouslySetInnerHTML',
    category: 'html-output',
    severity: 'high',
    framework: 'react',
    patterns: [
      { property: 'dangerouslySetInnerHTML', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['DOMPurify', 'sanitizeHtml', 'isomorphic-dompurify'],
    description: 'React dangerouslySetInnerHTML with user data',
    enabled: true,
    tags: ['xss', 'react', 'dangerouslySetInnerHTML'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Vue v-html
  {
    id: 'SNK-XSS-070',
    name: 'Vue v-html Directive',
    category: 'html-output',
    severity: 'high',
    framework: 'vue',
    patterns: [
      { property: 'v-html', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['DOMPurify', 'sanitizeHtml', 'vue-sanitize'],
    description: 'Vue v-html directive with user data',
    enabled: true,
    tags: ['xss', 'vue', 'v-html'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Angular bypassSecurityTrust
  {
    id: 'SNK-XSS-080',
    name: 'Angular Bypass Security',
    category: 'html-output',
    severity: 'high',
    framework: 'angular',
    patterns: [
      { method: 'bypassSecurityTrustHtml', vulnerableArg: 0 },
      { method: 'bypassSecurityTrustScript', vulnerableArg: 0 },
      { method: 'bypassSecurityTrustStyle', vulnerableArg: 0 },
      { method: 'bypassSecurityTrustUrl', vulnerableArg: 0 },
      { method: 'bypassSecurityTrustResourceUrl', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['DOMPurify', 'sanitizeHtml'],
    description: 'Angular security bypass with user data',
    enabled: true,
    tags: ['xss', 'angular', 'bypass-security'],
    relatedCWE: ['CWE-79'],
    owaspCategory: 'A03:2021-Injection',
  },

  // URL redirect (Open Redirect)
  {
    id: 'SNK-XSS-090',
    name: 'URL Redirect',
    category: 'redirect',
    severity: 'medium',
    framework: 'express',
    patterns: [
      { receiver: 'res', method: 'redirect', vulnerableArg: 0 },
      { receiver: 'response', method: 'redirect', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validateUrl', 'isAllowedDomain', 'whitelist'],
    description: 'URL redirect with user-controlled destination',
    enabled: true,
    tags: ['redirect', 'open-redirect'],
    relatedCWE: ['CWE-601'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // Browser location
  {
    id: 'SNK-XSS-100',
    name: 'Browser Location',
    category: 'redirect',
    severity: 'medium',
    framework: 'browser',
    patterns: [
      { receiver: 'location', property: 'href', vulnerableArg: 0 },
      { receiver: 'window', property: ['location', 'href'], vulnerableArg: 0 },
      { receiver: 'location', method: 'assign', vulnerableArg: 0 },
      { receiver: 'location', method: 'replace', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['validateUrl', 'isAllowedDomain'],
    description: 'Browser location assignment with user data',
    enabled: true,
    tags: ['redirect', 'open-redirect', 'dom'],
    relatedCWE: ['CWE-601'],
    owaspCategory: 'A01:2021-Broken Access Control',
  },

  // HTTP Header Injection
  {
    id: 'SNK-XSS-110',
    name: 'HTTP Header',
    category: 'html-output',
    severity: 'medium',
    framework: 'express',
    patterns: [
      { receiver: 'res', method: 'setHeader', vulnerableArg: 1 },
      { receiver: 'res', method: 'set', vulnerableArg: 1 },
      { receiver: 'response', method: 'header', vulnerableArg: 1 },
    ],
    expectedSanitizers: ['sanitizeHeader', 'removeNewlines'],
    description: 'HTTP header injection - CRLF/header splitting',
    enabled: true,
    tags: ['header-injection', 'crlf'],
    relatedCWE: ['CWE-113'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Log injection
  {
    id: 'SNK-XSS-120',
    name: 'Log Output',
    category: 'html-output',
    severity: 'low',
    patterns: [
      { receiver: 'console', method: 'log', vulnerableArg: 0 },
      { receiver: 'logger', method: 'info', vulnerableArg: 0 },
      { receiver: 'logger', method: 'warn', vulnerableArg: 0 },
      { receiver: 'logger', method: 'error', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['sanitizeForLog', 'removeNewlines'],
    description: 'Log output with user data - log injection/forging',
    enabled: true,
    tags: ['log-injection', 'log-forging'],
    relatedCWE: ['CWE-117'],
    owaspCategory: 'A09:2021-Security Logging and Monitoring Failures',
  },
] as const;
