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

// Forward to the mcp-server package's CLI
import '@nahisaho/musubix-mcp-server/bin/musubix-mcp.js';
