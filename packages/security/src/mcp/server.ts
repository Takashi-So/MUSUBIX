/**
 * @fileoverview MCP Server for security scanning
 * @module @nahisaho/musubix-security/mcp/server
 * @trace REQ-SEC-MCP-002
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';

import {
  getToolSchemas,
  createToolHandler,
  type SecurityToolHandler,
} from './tools.js';

/**
 * MCP Security Server
 */
export class SecurityMCPServer {
  private server: Server;
  private toolHandler: SecurityToolHandler;

  constructor() {
    this.server = new Server(
      {
        name: 'musubix-security',
        version: '1.8.0',
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );

    this.toolHandler = createToolHandler();
    this.setupHandlers();
  }

  /**
   * Setup request handlers
   */
  private setupHandlers(): void {
    // List tools handler
    this.server.setRequestHandler(ListToolsRequestSchema, async () => {
      const tools = getToolSchemas();
      return {
        tools: tools.map((t) => ({
          name: t.name,
          description: t.description,
          inputSchema: t.inputSchema,
        })),
      };
    });

    // Call tool handler
    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;
      const result = await this.toolHandler.handleTool(name, args ?? {});
      return {
        content: result.content,
        isError: result.isError,
      };
    });
  }

  /**
   * Start the server with stdio transport
   */
  async start(): Promise<void> {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    console.error('MUSUBIX Security MCP Server started');
  }

  /**
   * Stop the server
   */
  async stop(): Promise<void> {
    await this.server.close();
  }
}

/**
 * Create and start MCP server
 */
export async function startMCPServer(): Promise<SecurityMCPServer> {
  const server = new SecurityMCPServer();
  await server.start();
  return server;
}

/**
 * Run MCP server from CLI
 */
export async function runMCPServer(): Promise<void> {
  try {
    await startMCPServer();
  } catch (error: any) {
    console.error(`Failed to start MCP server: ${error.message}`);
    process.exit(1);
  }
}
