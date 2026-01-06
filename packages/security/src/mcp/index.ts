/**
 * @fileoverview MCP module entry point
 * @module @nahisaho/musubix-security/mcp
 */

export {
  getToolSchemas,
  createToolHandler,
  SecurityToolHandler,
  SECURITY_TOOLS,
  type ToolSchema,
  type ToolResult,
} from './tools.js';

export {
  SecurityMCPServer,
  startMCPServer,
  runMCPServer,
} from './server.js';
