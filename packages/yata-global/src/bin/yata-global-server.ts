#!/usr/bin/env node
/**
 * YATA Global Server CLI
 */

import { startServer } from '../server.js';

const port = parseInt(process.env.PORT || '3000', 10);
const host = process.env.HOST || '0.0.0.0';

console.log('🚀 Starting YATA Global Server...');

startServer({ port, host }).catch((err: Error) => {
  console.error('❌ Failed to start server:', err);
  process.exit(1);
});
