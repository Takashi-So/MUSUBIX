#!/usr/bin/env node
/**
 * YATA UI CLI
 *
 * Start the YATA Knowledge Graph Web UI server.
 *
 * @see REQ-YI-WEB-001
 */

import { createYataUIServer } from '../dist/index.js';

const args = process.argv.slice(2);
const portArg = args.find(a => a.startsWith('--port='));
const port = portArg ? parseInt(portArg.split('=')[1], 10) : 3000;

const server = createYataUIServer({ port });

// Demo data provider
server.setDataProvider(async () => ({
  nodes: [
    { id: '1', label: 'UserService', type: 'class', namespace: 'app.services' },
    { id: '2', label: 'UserRepository', type: 'interface', namespace: 'app.repositories' },
    { id: '3', label: 'User', type: 'entity', namespace: 'app.domain' },
    { id: '4', label: 'createUser', type: 'function', namespace: 'app.services' },
  ],
  edges: [
    { id: 'e1', source: '1', target: '2', type: 'uses', label: 'uses' },
    { id: 'e2', source: '1', target: '3', type: 'returns', label: 'returns' },
    { id: 'e3', source: '4', target: '3', type: 'creates', label: 'creates' },
  ],
}));

server.start().then(() => {
  console.log(`🌐 YATA UI running at ${server.getUrl()}`);
  console.log('Press Ctrl+C to stop');
});

process.on('SIGINT', async () => {
  console.log('\nShutting down...');
  await server.stop();
  process.exit(0);
});
