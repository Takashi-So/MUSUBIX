/**
 * MUSUBIX MCP Server
 * 
 * Model Context Protocol server for MUSUBIX
 * 
 * @packageDocumentation
 * @module server
 * 
 * @see REQ-INT-102 - MCP Server
 * @see DES-MUSUBIX-001 Section 2.2 - Container Diagram
 */

import { EventEmitter } from 'events';
import type {
  MCPServerConfig,
  ToolDefinition,
  PromptDefinition,
  ResourceDefinition,
  ResourceTemplateDefinition,
  ServerCapabilities,
  ToolResult,
  PromptResult,
  ResourceResult,
  NotificationHandler,
} from './types.js';
import { DEFAULT_SERVER_CONFIG } from './types.js';

/**
 * JSON-RPC Request
 */
interface JsonRpcRequest {
  jsonrpc: '2.0';
  id?: number | string;
  method: string;
  params?: Record<string, unknown>;
}

/**
 * JSON-RPC Response
 */
interface JsonRpcResponse {
  jsonrpc: '2.0';
  id: number | string;
  result?: unknown;
  error?: {
    code: number;
    message: string;
    data?: unknown;
  };
}

/**
 * Server state
 */
type ServerState = 'stopped' | 'starting' | 'running' | 'stopping';

/**
 * MCP Server Events
 */
export interface MCPServerEvents {
  started: [];
  stopped: [];
  error: [Error];
  request: [JsonRpcRequest];
  response: [JsonRpcResponse];
}

/**
 * MUSUBIX MCP Server
 * 
 * Implements Model Context Protocol server
 */
export class MCPServer extends EventEmitter {
  private config: MCPServerConfig;
  private state: ServerState = 'stopped';
  private tools = new Map<string, ToolDefinition>();
  private prompts = new Map<string, PromptDefinition>();
  private resources = new Map<string, ResourceDefinition>();
  private resourceTemplates = new Map<string, ResourceTemplateDefinition>();
  private notificationHandlers = new Map<string, NotificationHandler>();
  private buffer = '';
  private _initialized = false;
  private _clientCapabilities: Record<string, unknown> = {};

  constructor(config?: Partial<MCPServerConfig>) {
    super();
    this.config = { ...DEFAULT_SERVER_CONFIG, ...config };
  }

  /**
   * Get server state
   */
  getState(): ServerState {
    return this.state;
  }

  /**
   * Check if server is running
   */
  isRunning(): boolean {
    return this.state === 'running';
  }

  /**
   * Check if server is initialized
   */
  isInitialized(): boolean {
    return this._initialized;
  }

  /**
   * Get client capabilities
   */
  getClientCapabilities(): Record<string, unknown> {
    return this._clientCapabilities;
  }

  /**
   * Get server capabilities
   */
  getCapabilities(): ServerCapabilities {
    const capabilities: ServerCapabilities = {};

    if (this.tools.size > 0) {
      capabilities.tools = { listChanged: true };
    }

    if (this.prompts.size > 0) {
      capabilities.prompts = { listChanged: true };
    }

    if (this.resources.size > 0 || this.resourceTemplates.size > 0) {
      capabilities.resources = { subscribe: false, listChanged: true };
    }

    capabilities.logging = {};

    return capabilities;
  }

  /**
   * Register a tool
   */
  registerTool(tool: ToolDefinition): void {
    this.tools.set(tool.name, tool);
    this.debug(`Registered tool: ${tool.name}`);
  }

  /**
   * Register multiple tools
   */
  registerTools(tools: ToolDefinition[]): void {
    for (const tool of tools) {
      this.registerTool(tool);
    }
  }

  /**
   * Register a prompt
   */
  registerPrompt(prompt: PromptDefinition): void {
    this.prompts.set(prompt.name, prompt);
    this.debug(`Registered prompt: ${prompt.name}`);
  }

  /**
   * Register multiple prompts
   */
  registerPrompts(prompts: PromptDefinition[]): void {
    for (const prompt of prompts) {
      this.registerPrompt(prompt);
    }
  }

  /**
   * Register a resource
   */
  registerResource(resource: ResourceDefinition): void {
    this.resources.set(resource.uri, resource);
    this.debug(`Registered resource: ${resource.uri}`);
  }

  /**
   * Register a resource template
   */
  registerResourceTemplate(template: ResourceTemplateDefinition): void {
    this.resourceTemplates.set(template.uriTemplate, template);
    this.debug(`Registered resource template: ${template.uriTemplate}`);
  }

  /**
   * Register notification handler
   */
  onNotification(method: string, handler: NotificationHandler): void {
    this.notificationHandlers.set(method, handler);
  }

  /**
   * Start the server
   */
  async start(): Promise<void> {
    if (this.state !== 'stopped') {
      throw new Error('Server is already running or starting');
    }

    this.state = 'starting';
    this.debug('Starting MCP server...');

    try {
      if (this.config.transport === 'stdio') {
        await this.startStdio();
      } else {
        await this.startSSE();
      }

      this.state = 'running';
      this.emit('started');
      this.debug('MCP server started');
    } catch (error) {
      this.state = 'stopped';
      throw error;
    }
  }

  /**
   * Stop the server
   */
  async stop(): Promise<void> {
    if (this.state !== 'running') {
      return;
    }

    this.state = 'stopping';
    this.debug('Stopping MCP server...');

    // Cleanup
    this._initialized = false;

    this.state = 'stopped';
    this.emit('stopped');
    this.debug('MCP server stopped');
  }

  /**
   * Start stdio transport
   */
  private async startStdio(): Promise<void> {
    process.stdin.setEncoding('utf8');
    process.stdin.on('data', (data: string) => {
      this.handleInput(data);
    });

    process.stdin.on('end', () => {
      this.stop();
    });
  }

  /**
   * Start SSE transport
   */
  private async startSSE(): Promise<void> {
    throw new Error('SSE transport not yet implemented');
  }

  /**
   * Handle input data
   */
  private handleInput(data: string): void {
    this.buffer += data;

    // Process complete lines
    const lines = this.buffer.split('\n');
    this.buffer = lines.pop() ?? '';

    for (const line of lines) {
      if (line.trim()) {
        this.processMessage(line);
      }
    }
  }

  /**
   * Process JSON-RPC message
   */
  private processMessage(message: string): void {
    try {
      const request = JSON.parse(message) as JsonRpcRequest;
      this.emit('request', request);
      this.handleRequest(request);
    } catch (error) {
      this.sendError(null, -32700, 'Parse error');
    }
  }

  /**
   * Handle JSON-RPC request
   */
  private async handleRequest(request: JsonRpcRequest): Promise<void> {
    const { id, method, params } = request;

    // Handle notification (no id)
    if (id === undefined) {
      const handler = this.notificationHandlers.get(method);
      if (handler) {
        handler(method, params ?? {});
      }
      return;
    }

    try {
      let result: unknown;

      switch (method) {
        case 'initialize':
          result = await this.handleInitialize(params ?? {});
          break;

        case 'tools/list':
          result = this.handleToolsList();
          break;

        case 'tools/call':
          result = await this.handleToolsCall(params ?? {});
          break;

        case 'prompts/list':
          result = this.handlePromptsList();
          break;

        case 'prompts/get':
          result = await this.handlePromptsGet(params ?? {});
          break;

        case 'resources/list':
          result = this.handleResourcesList();
          break;

        case 'resources/read':
          result = await this.handleResourcesRead(params ?? {});
          break;

        case 'resources/templates/list':
          result = this.handleResourceTemplatesList();
          break;

        case 'ping':
          result = {};
          break;

        default:
          this.sendError(id, -32601, `Method not found: ${method}`);
          return;
      }

      this.sendResult(id, result);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      this.sendError(id, -32603, message);
    }
  }

  /**
   * Handle initialize request
   */
  private async handleInitialize(
    params: Record<string, unknown>
  ): Promise<unknown> {
    this._clientCapabilities = (params.capabilities as Record<string, unknown>) ?? {};
    this._initialized = true;

    return {
      protocolVersion: '2024-11-05',
      capabilities: this.getCapabilities(),
      serverInfo: {
        name: this.config.name,
        version: this.config.version,
      },
    };
  }

  /**
   * Handle tools/list request
   */
  private handleToolsList(): unknown {
    const tools = Array.from(this.tools.values()).map((tool) => ({
      name: tool.name,
      description: tool.description,
      inputSchema: tool.inputSchema,
    }));

    return { tools };
  }

  /**
   * Handle tools/call request
   */
  private async handleToolsCall(
    params: Record<string, unknown>
  ): Promise<ToolResult> {
    const { name, arguments: args } = params as {
      name: string;
      arguments: Record<string, unknown>;
    };

    const tool = this.tools.get(name);
    if (!tool) {
      throw new Error(`Unknown tool: ${name}`);
    }

    return tool.handler(args ?? {});
  }

  /**
   * Handle prompts/list request
   */
  private handlePromptsList(): unknown {
    const prompts = Array.from(this.prompts.values()).map((prompt) => ({
      name: prompt.name,
      description: prompt.description,
      arguments: prompt.arguments,
    }));

    return { prompts };
  }

  /**
   * Handle prompts/get request
   */
  private async handlePromptsGet(
    params: Record<string, unknown>
  ): Promise<PromptResult> {
    const { name, arguments: args } = params as {
      name: string;
      arguments: Record<string, string>;
    };

    const prompt = this.prompts.get(name);
    if (!prompt) {
      throw new Error(`Unknown prompt: ${name}`);
    }

    return prompt.handler(args ?? {});
  }

  /**
   * Handle resources/list request
   */
  private handleResourcesList(): unknown {
    const resources = Array.from(this.resources.values()).map((resource) => ({
      uri: resource.uri,
      name: resource.name,
      description: resource.description,
      mimeType: resource.mimeType,
    }));

    return { resources };
  }

  /**
   * Handle resources/read request
   */
  private async handleResourcesRead(
    params: Record<string, unknown>
  ): Promise<ResourceResult> {
    const { uri } = params as { uri: string };

    // Check direct resources first
    const resource = this.resources.get(uri);
    if (resource) {
      return resource.handler();
    }

    // Check templates
    for (const [template, def] of this.resourceTemplates) {
      const match = this.matchTemplate(template, uri);
      if (match) {
        return def.handler(uri, match);
      }
    }

    throw new Error(`Unknown resource: ${uri}`);
  }

  /**
   * Handle resources/templates/list request
   */
  private handleResourceTemplatesList(): unknown {
    const resourceTemplates = Array.from(this.resourceTemplates.values()).map(
      (template) => ({
        uriTemplate: template.uriTemplate,
        name: template.name,
        description: template.description,
        mimeType: template.mimeType,
      })
    );

    return { resourceTemplates };
  }

  /**
   * Match URI against template
   */
  private matchTemplate(
    template: string,
    uri: string
  ): Record<string, string> | null {
    // Simple template matching for {param} patterns
    const templateParts = template.split('/');
    const uriParts = uri.split('/');

    if (templateParts.length !== uriParts.length) {
      return null;
    }

    const params: Record<string, string> = {};

    for (let i = 0; i < templateParts.length; i++) {
      const tPart = templateParts[i];
      const uPart = uriParts[i];

      if (tPart.startsWith('{') && tPart.endsWith('}')) {
        const paramName = tPart.slice(1, -1);
        params[paramName] = uPart;
      } else if (tPart !== uPart) {
        return null;
      }
    }

    return params;
  }

  /**
   * Send result response
   */
  private sendResult(id: number | string, result: unknown): void {
    const response: JsonRpcResponse = {
      jsonrpc: '2.0',
      id,
      result,
    };
    this.send(response);
  }

  /**
   * Send error response
   */
  private sendError(
    id: number | string | null,
    code: number,
    message: string,
    data?: unknown
  ): void {
    const response: JsonRpcResponse = {
      jsonrpc: '2.0',
      id: id ?? 0,
      error: { code, message, data },
    };
    this.send(response);
  }

  /**
   * Send JSON-RPC response
   */
  private send(response: JsonRpcResponse): void {
    this.emit('response', response);
    const json = JSON.stringify(response);
    process.stdout.write(json + '\n');
  }

  /**
   * Debug log
   */
  private debug(message: string): void {
    if (this.config.debug) {
      console.error(`[MCP Server] ${message}`);
    }
  }
}

/**
 * Create MCP server instance
 */
export function createMCPServer(config?: Partial<MCPServerConfig>): MCPServer {
  return new MCPServer(config);
}
