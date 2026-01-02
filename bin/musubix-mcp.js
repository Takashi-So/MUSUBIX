#!/usr/bin/env node
/**
 * MUSUBIX MCP Server Entry Point (Root Package)
 * 
 * This file delegates to the @nahisaho/musubix-mcp-server package.
 * 
 * @see REQ-ARC-003 - MCP Server
 * 
 * Usage:
 *   npx musubix-mcp
 *   musubix-mcp --transport stdio
 */

import { main } from '@nahisaho/musubix-mcp-server';

main().catch((error) => {
  console.error('MUSUBIX MCP Server error:', error);
  process.exit(1);
});
