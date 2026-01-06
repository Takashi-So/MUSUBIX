#!/usr/bin/env node
/**
 * @fileoverview MUSUBIX Security MCP Server entry point
 * @module @nahisaho/musubix-security/bin/mcp
 */

import { runMCPServer } from '../dist/mcp/index.js';

runMCPServer().catch((error) => {
  console.error('Fatal error:', error.message);
  process.exit(1);
});
