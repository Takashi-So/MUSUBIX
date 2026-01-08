/**
 * @fileoverview HTTP request source definitions
 * @module @nahisaho/musubix-security/analysis/sources/http-request
 * @trace REQ-SEC-001
 */

import type { SourceDefinition } from './types.js';

/**
 * HTTP request sources - external API responses, network data
 * @trace REQ-SEC-001
 */
export const HTTP_REQUEST_SOURCES: readonly SourceDefinition[] = [
  // Fetch API
  {
    id: 'SRC-HTTP-001',
    name: 'Fetch Response',
    category: 'network',
    framework: 'browser',
    patterns: [
      { method: 'fetch', taintedReturn: true },
      { receiver: ['Response'], method: 'json', taintedReturn: true },
      { receiver: ['Response'], method: 'text', taintedReturn: true },
      { receiver: ['response'], method: 'json', taintedReturn: true },
      { receiver: ['response'], method: 'text', taintedReturn: true },
    ],
    description: 'HTTP fetch API response data',
    confidence: 0.85,
    enabled: true,
    tags: ['http', 'fetch', 'external'],
    relatedCWE: ['CWE-20', 'CWE-918'],
  },

  // Axios
  {
    id: 'SRC-HTTP-010',
    name: 'Axios Response',
    category: 'network',
    framework: 'axios',
    patterns: [
      { receiver: 'axios', method: 'get', taintedReturn: true },
      { receiver: 'axios', method: 'post', taintedReturn: true },
      { receiver: 'axios', method: 'put', taintedReturn: true },
      { receiver: 'axios', method: 'delete', taintedReturn: true },
      { receiver: 'axios', method: 'patch', taintedReturn: true },
      { receiver: 'axios', method: 'request', taintedReturn: true },
      { property: 'data', taintedReturn: true },
    ],
    description: 'Axios HTTP client response data',
    confidence: 0.85,
    enabled: true,
    tags: ['http', 'axios', 'external'],
    relatedCWE: ['CWE-20', 'CWE-918'],
  },

  // Node.js HTTP
  {
    id: 'SRC-HTTP-020',
    name: 'Node HTTP Response',
    category: 'network',
    framework: 'node',
    patterns: [
      { receiver: 'http', method: 'get', taintedReturn: true },
      { receiver: 'http', method: 'request', taintedReturn: true },
      { receiver: 'https', method: 'get', taintedReturn: true },
      { receiver: 'https', method: 'request', taintedReturn: true },
      {
        importPattern: { module: 'http', named: ['get', 'request'] },
        method: ['get', 'request'],
        taintedReturn: true,
      },
    ],
    description: 'Node.js http/https module response',
    confidence: 0.85,
    enabled: true,
    tags: ['http', 'node', 'external'],
    relatedCWE: ['CWE-20', 'CWE-918'],
  },

  // Got
  {
    id: 'SRC-HTTP-030',
    name: 'Got Response',
    category: 'network',
    framework: 'got',
    patterns: [
      { method: 'got', taintedReturn: true },
      { receiver: 'got', method: 'get', taintedReturn: true },
      { receiver: 'got', method: 'post', taintedReturn: true },
    ],
    description: 'Got HTTP client response data',
    confidence: 0.85,
    enabled: true,
    tags: ['http', 'got', 'external'],
    relatedCWE: ['CWE-20', 'CWE-918'],
  },

  // Superagent
  {
    id: 'SRC-HTTP-040',
    name: 'Superagent Response',
    category: 'network',
    framework: 'superagent',
    patterns: [
      { receiver: 'superagent', method: 'get', taintedReturn: true },
      { receiver: 'superagent', method: 'post', taintedReturn: true },
      { receiver: 'request', method: 'get', taintedReturn: true },
      { receiver: 'request', method: 'post', taintedReturn: true },
    ],
    description: 'Superagent HTTP client response data',
    confidence: 0.85,
    enabled: true,
    tags: ['http', 'superagent', 'external'],
    relatedCWE: ['CWE-20', 'CWE-918'],
  },

  // XMLHttpRequest (legacy)
  {
    id: 'SRC-HTTP-050',
    name: 'XMLHttpRequest Response',
    category: 'network',
    framework: 'browser',
    patterns: [
      { receiver: 'XMLHttpRequest', property: 'response', taintedReturn: true },
      { receiver: 'XMLHttpRequest', property: 'responseText', taintedReturn: true },
      { receiver: 'xhr', property: 'response', taintedReturn: true },
      { receiver: 'xhr', property: 'responseText', taintedReturn: true },
    ],
    description: 'XMLHttpRequest response data',
    confidence: 0.85,
    enabled: true,
    tags: ['http', 'xhr', 'external', 'legacy'],
    relatedCWE: ['CWE-20', 'CWE-918'],
  },

  // WebSocket
  {
    id: 'SRC-HTTP-060',
    name: 'WebSocket Message',
    category: 'network',
    framework: 'browser',
    patterns: [
      { receiver: 'WebSocket', method: 'onmessage', taintedArg: 0 },
      { receiver: 'ws', method: 'on', taintedArg: 1 },
      { receiver: 'socket', method: 'on', taintedArg: 1 },
    ],
    description: 'WebSocket message data',
    confidence: 0.9,
    enabled: true,
    tags: ['websocket', 'external'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },

  // GraphQL
  {
    id: 'SRC-HTTP-070',
    name: 'GraphQL Response',
    category: 'network',
    framework: 'graphql',
    patterns: [
      { property: 'data', taintedReturn: true },
      { method: 'query', taintedReturn: true },
      { method: 'mutate', taintedReturn: true },
    ],
    description: 'GraphQL query/mutation response',
    confidence: 0.8,
    enabled: true,
    tags: ['graphql', 'external'],
    relatedCWE: ['CWE-20'],
  },

  // tRPC
  {
    id: 'SRC-HTTP-080',
    name: 'tRPC Response',
    category: 'network',
    framework: 'trpc',
    patterns: [
      { receiver: 'trpc', method: 'query', taintedReturn: true },
      { receiver: 'trpc', method: 'mutation', taintedReturn: true },
      { receiver: 'api', method: 'query', taintedReturn: true },
    ],
    description: 'tRPC procedure response',
    confidence: 0.8,
    enabled: true,
    tags: ['trpc', 'external'],
    relatedCWE: ['CWE-20'],
  },
] as const;
