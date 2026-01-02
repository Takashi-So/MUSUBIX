#!/usr/bin/env node
/**
 * MUSUBIX MCP Server Entry Point
 * 
 * Starts the MCP server for AI platform integration.
 * 
 * @see REQ-INT-102 - MCP Server
 * 
 * Usage:
 *   npx @musubix/mcp-server
 *   musubix-mcp --transport stdio
 *   musubix-mcp --transport sse --port 8080
 */

import { startServer, VERSION } from '../dist/index.js';
import { parseArgs } from 'node:util';

const options = {
  transport: {
    type: 'string',
    short: 't',
    default: 'stdio'
  },
  port: {
    type: 'string',
    short: 'p',
    default: '3000'
  },
  help: {
    type: 'boolean',
    short: 'h',
    default: false
  },
  version: {
    type: 'boolean',
    short: 'v',
    default: false
  }
};

const { values } = parseArgs({ options, allowPositionals: true });

if (values.help) {
  console.log(`
MUSUBIX MCP Server - Model Context Protocol Server for AI Platforms

Usage:
  musubix-mcp [options]

Options:
  -t, --transport <type>  Transport type: stdio | sse (default: stdio)
  -p, --port <port>       Port for SSE transport (default: 3000)
  -h, --help              Show this help message
  -v, --version           Show version

Examples:
  musubix-mcp                          # Start with stdio transport
  musubix-mcp -t sse -p 8080           # Start SSE server on port 8080
  npx @musubix/mcp-server              # Run via npx
`);
  process.exit(0);
}

if (values.version) {
  console.log(`@musubix/mcp-server v${VERSION}`);
  process.exit(0);
}

// Start the MCP server
startServer({
  transport: values.transport,
  port: parseInt(values.port, 10)
});
