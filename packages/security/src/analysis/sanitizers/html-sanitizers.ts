/**
 * @fileoverview HTML/XSS sanitizer definitions
 * @module @nahisaho/musubix-security/analysis/sanitizers/html-sanitizers
 * @trace REQ-SEC-001
 */

import type { SanitizerDefinition } from './types.js';

/**
 * HTML/XSS sanitizers
 * @trace REQ-SEC-001
 */
export const HTML_SANITIZERS: readonly SanitizerDefinition[] = [
  // Generic HTML escape
  {
    id: 'SAN-HTML-001',
    name: 'escapeHtml',
    aliases: ['escapeHTML', 'htmlEscape', 'escape'],
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Generic HTML escape function',
    enabled: true,
    tags: ['html-output', 'html', 'escape'],
  },
  {
    id: 'SAN-HTML-002',
    name: 'encode',
    aliases: ['htmlEncode', 'encodeHTML'],
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'HTML entity encoding',
    enabled: true,
    tags: ['html-output', 'html', 'encode'],
  },

  // html-entities package
  {
    id: 'SAN-HTML-010',
    name: 'encode',
    package: 'html-entities',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'html-entities encode function',
    enabled: true,
    tags: ['html-output', 'html-entities', 'encode'],
  },
  {
    id: 'SAN-HTML-011',
    name: 'encodeHTML',
    package: 'html-entities',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'html-entities encodeHTML function',
    enabled: true,
    tags: ['html-output', 'html-entities', 'encode'],
  },

  // sanitize-html package
  {
    id: 'SAN-HTML-020',
    name: 'sanitizeHtml',
    aliases: ['sanitize'],
    package: 'sanitize-html',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'sanitize-html - removes dangerous HTML',
    enabled: true,
    tags: ['html-output', 'sanitize-html', 'sanitize'],
  },

  // DOMPurify
  {
    id: 'SAN-HTML-030',
    name: 'sanitize',
    package: 'dompurify',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'DOMPurify.sanitize - DOM-based sanitization',
    enabled: true,
    tags: ['html-output', 'dompurify', 'sanitize'],
  },
  {
    id: 'SAN-HTML-031',
    name: 'sanitize',
    package: 'isomorphic-dompurify',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'isomorphic-dompurify - works on server and client',
    enabled: true,
    tags: ['html-output', 'dompurify', 'isomorphic'],
  },

  // xss package
  {
    id: 'SAN-HTML-040',
    name: 'filterXSS',
    aliases: ['html-output'],
    package: 'html-output',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'xss package - filters XSS attacks',
    enabled: true,
    tags: ['html-output', 'filter', 'xss-package'],
  },

  // he package
  {
    id: 'SAN-HTML-050',
    name: 'encode',
    package: 'he',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'he.encode - HTML entity encoder',
    enabled: true,
    tags: ['html-output', 'he', 'encode'],
  },
  {
    id: 'SAN-HTML-051',
    name: 'escape',
    package: 'he',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'he.escape - HTML escape',
    enabled: true,
    tags: ['html-output', 'he', 'escape'],
  },

  // lodash escape
  {
    id: 'SAN-HTML-060',
    name: 'escape',
    aliases: ['_.escape'],
    package: 'lodash',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Lodash escape function',
    enabled: true,
    tags: ['html-output', 'lodash', 'escape'],
  },

  // validator.js
  {
    id: 'SAN-HTML-070',
    name: 'escape',
    package: 'validator',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'validator.js escape function',
    enabled: true,
    tags: ['html-output', 'validator', 'escape'],
  },

  // Text content (DOM safe alternative)
  {
    id: 'SAN-HTML-080',
    name: 'textContent',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Using textContent instead of innerHTML',
    enabled: true,
    tags: ['html-output', 'dom', 'textContent'],
  },
  {
    id: 'SAN-HTML-081',
    name: 'innerText',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Using innerText instead of innerHTML',
    enabled: true,
    tags: ['html-output', 'dom', 'innerText'],
  },

  // jQuery text()
  {
    id: 'SAN-HTML-090',
    name: 'text',
    package: 'jquery',
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'jQuery text() instead of html()',
    enabled: true,
    tags: ['html-output', 'jquery', 'text'],
  },

  // Template engine auto-escape
  {
    id: 'SAN-HTML-100',
    name: 'autoEscape',
    namePattern: 'autoEscape|auto_escape',
    protects: ['html-output'],
    completeness: 'conditional',
    returnsClean: true,
    description: 'Template engine auto-escape feature',
    caveats: 'Depends on template engine configuration',
    enabled: true,
    tags: ['html-output', 'template', 'auto-escape'],
  },

  // HTTP Header sanitization
  {
    id: 'SAN-HTML-110',
    name: 'sanitizeHeader',
    aliases: ['removeNewlines', 'stripNewlines'],
    protects: ['html-output'],
    completeness: 'complete',
    returnsClean: true,
    description: 'HTTP header sanitization - removes CRLF',
    enabled: true,
    tags: ['header', 'crlf', 'sanitize'],
  },
] as const;
