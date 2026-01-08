/**
 * @fileoverview User input source definitions
 * @module @nahisaho/musubix-security/analysis/sources/user-input
 * @trace REQ-SEC-001
 */

import type { SourceDefinition } from './types.js';

/**
 * User input sources - form data, query params, request body
 * @trace REQ-SEC-001
 */
export const USER_INPUT_SOURCES: readonly SourceDefinition[] = [
  // Express.js sources
  {
    id: 'SRC-UI-001',
    name: 'Express Request Body',
    category: 'user-input',
    framework: 'express',
    patterns: [
      { receiver: 'req', property: 'body', taintedReturn: true },
      { receiver: 'request', property: 'body', taintedReturn: true },
    ],
    description: 'HTTP request body (POST/PUT data)',
    confidence: 0.95,
    enabled: true,
    tags: ['express', 'http', 'body'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },
  {
    id: 'SRC-UI-002',
    name: 'Express Query Parameters',
    category: 'user-input',
    framework: 'express',
    patterns: [
      { receiver: 'req', property: 'query', taintedReturn: true },
      { receiver: 'request', property: 'query', taintedReturn: true },
    ],
    description: 'URL query parameters',
    confidence: 0.95,
    enabled: true,
    tags: ['express', 'http', 'query'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },
  {
    id: 'SRC-UI-003',
    name: 'Express URL Parameters',
    category: 'user-input',
    framework: 'express',
    patterns: [
      { receiver: 'req', property: 'params', taintedReturn: true },
      { receiver: 'request', property: 'params', taintedReturn: true },
    ],
    description: 'URL path parameters (e.g., /users/:id)',
    confidence: 0.95,
    enabled: true,
    tags: ['express', 'http', 'params'],
    relatedCWE: ['CWE-20', 'CWE-89', 'CWE-22'],
  },
  {
    id: 'SRC-UI-004',
    name: 'Express Headers',
    category: 'user-input',
    framework: 'express',
    patterns: [
      { receiver: 'req', property: 'headers', taintedReturn: true },
      { receiver: 'req', method: 'get', taintedReturn: true },
      { receiver: 'req', method: 'header', taintedReturn: true },
    ],
    description: 'HTTP request headers',
    confidence: 0.9,
    enabled: true,
    tags: ['express', 'http', 'headers'],
    relatedCWE: ['CWE-20', 'CWE-113'],
  },
  {
    id: 'SRC-UI-005',
    name: 'Express Cookies',
    category: 'user-input',
    framework: 'express',
    patterns: [
      { receiver: 'req', property: 'cookies', taintedReturn: true },
      { receiver: 'req', property: 'signedCookies', taintedReturn: true },
    ],
    description: 'HTTP cookies',
    confidence: 0.9,
    enabled: true,
    tags: ['express', 'http', 'cookies'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },

  // Koa.js sources
  {
    id: 'SRC-UI-010',
    name: 'Koa Request Body',
    category: 'user-input',
    framework: 'koa',
    patterns: [
      { receiver: 'ctx', property: ['request', 'body'], taintedReturn: true },
      { receiver: 'ctx', property: 'body', taintedReturn: true },
    ],
    description: 'Koa request body',
    confidence: 0.95,
    enabled: true,
    tags: ['koa', 'http', 'body'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },
  {
    id: 'SRC-UI-011',
    name: 'Koa Query Parameters',
    category: 'user-input',
    framework: 'koa',
    patterns: [
      { receiver: 'ctx', property: 'query', taintedReturn: true },
      { receiver: 'ctx', property: ['request', 'query'], taintedReturn: true },
    ],
    description: 'Koa query parameters',
    confidence: 0.95,
    enabled: true,
    tags: ['koa', 'http', 'query'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },
  {
    id: 'SRC-UI-012',
    name: 'Koa URL Parameters',
    category: 'user-input',
    framework: 'koa',
    patterns: [
      { receiver: 'ctx', property: 'params', taintedReturn: true },
    ],
    description: 'Koa URL path parameters',
    confidence: 0.95,
    enabled: true,
    tags: ['koa', 'http', 'params'],
    relatedCWE: ['CWE-20', 'CWE-89', 'CWE-22'],
  },

  // Fastify sources
  {
    id: 'SRC-UI-020',
    name: 'Fastify Request Body',
    category: 'user-input',
    framework: 'fastify',
    patterns: [
      { receiver: 'request', property: 'body', taintedReturn: true },
      { receiver: 'req', property: 'body', taintedReturn: true },
    ],
    description: 'Fastify request body',
    confidence: 0.95,
    enabled: true,
    tags: ['fastify', 'http', 'body'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },
  {
    id: 'SRC-UI-021',
    name: 'Fastify Query Parameters',
    category: 'user-input',
    framework: 'fastify',
    patterns: [
      { receiver: 'request', property: 'query', taintedReturn: true },
    ],
    description: 'Fastify query parameters',
    confidence: 0.95,
    enabled: true,
    tags: ['fastify', 'http', 'query'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },

  // Next.js sources
  {
    id: 'SRC-UI-030',
    name: 'Next.js API Request Body',
    category: 'user-input',
    framework: 'next',
    patterns: [
      { receiver: 'req', property: 'body', taintedReturn: true },
    ],
    description: 'Next.js API route request body',
    confidence: 0.95,
    enabled: true,
    tags: ['next', 'http', 'body'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },
  {
    id: 'SRC-UI-031',
    name: 'Next.js Query Parameters',
    category: 'user-input',
    framework: 'next',
    patterns: [
      { receiver: 'req', property: 'query', taintedReturn: true },
    ],
    description: 'Next.js API route query parameters',
    confidence: 0.95,
    enabled: true,
    tags: ['next', 'http', 'query'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },

  // Browser sources
  {
    id: 'SRC-UI-040',
    name: 'DOM Input Value',
    category: 'user-input',
    framework: 'browser',
    patterns: [
      { method: 'getElementById', taintedReturn: true },
      { method: 'querySelector', taintedReturn: true },
      { method: 'querySelectorAll', taintedReturn: true },
      { method: 'getElementsByName', taintedReturn: true },
      { method: 'getElementsByClassName', taintedReturn: true },
    ],
    description: 'DOM element values (potentially user-controlled)',
    confidence: 0.85,
    enabled: true,
    tags: ['browser', 'dom', 'input'],
    relatedCWE: ['CWE-79', 'CWE-20'],
  },
  {
    id: 'SRC-UI-041',
    name: 'URL Location',
    category: 'user-input',
    framework: 'browser',
    patterns: [
      { receiver: 'location', property: 'search', taintedReturn: true },
      { receiver: 'location', property: 'hash', taintedReturn: true },
      { receiver: 'location', property: 'href', taintedReturn: true },
      { receiver: 'window', property: ['location', 'search'], taintedReturn: true },
    ],
    description: 'Browser URL parameters',
    confidence: 0.9,
    enabled: true,
    tags: ['browser', 'url'],
    relatedCWE: ['CWE-79', 'CWE-601'],
  },
  {
    id: 'SRC-UI-042',
    name: 'User Prompt',
    category: 'user-input',
    framework: 'browser',
    patterns: [
      { method: 'prompt', taintedReturn: true },
    ],
    description: 'User input from prompt dialog',
    confidence: 0.95,
    enabled: true,
    tags: ['browser', 'prompt'],
    relatedCWE: ['CWE-79', 'CWE-20'],
  },

  // FormData
  {
    id: 'SRC-UI-050',
    name: 'FormData',
    category: 'user-input',
    framework: 'browser',
    patterns: [
      { receiver: 'FormData', method: 'get', taintedReturn: true },
      { receiver: 'FormData', method: 'getAll', taintedReturn: true },
      { receiver: 'formData', method: 'get', taintedReturn: true },
      { receiver: 'formData', method: 'getAll', taintedReturn: true },
    ],
    description: 'Form data values',
    confidence: 0.95,
    enabled: true,
    tags: ['browser', 'form'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },
] as const;
