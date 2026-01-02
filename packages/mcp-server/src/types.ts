/**
 * MCP Server Types
 * 
 * Type definitions for MUSUBIX MCP Server
 * 
 * @packageDocumentation
 * @module types
 * 
 * @see REQ-INT-102 - MCP Server
 */

/**
 * MCP Server transport type
 */
export type ServerTransport = 'stdio' | 'sse';

/**
 * MCP Server configuration
 */
export interface MCPServerConfig {
  /** Server name */
  name: string;
  /** Server version */
  version: string;
  /** Transport type */
  transport: ServerTransport;
  /** Port for SSE transport */
  port?: number;
  /** Enable debug logging */
  debug?: boolean;
}

/**
 * Default server configuration
 */
export const DEFAULT_SERVER_CONFIG: MCPServerConfig = {
  name: 'musubix-mcp-server',
  version: '0.1.0',
  transport: 'stdio',
  debug: false,
};

/**
 * Tool definition
 */
export interface ToolDefinition {
  /** Tool name */
  name: string;
  /** Tool description */
  description: string;
  /** Input schema (JSON Schema) */
  inputSchema: Record<string, unknown>;
  /** Handler function */
  handler: ToolHandler;
}

/**
 * Tool handler function type
 */
export type ToolHandler = (
  args: Record<string, unknown>
) => Promise<ToolResult>;

/**
 * Tool execution result
 */
export interface ToolResult {
  /** Result content */
  content: ToolContent[];
  /** Is error result */
  isError?: boolean;
}

/**
 * Tool content types
 */
export type ToolContent =
  | TextContent
  | ImageContent
  | ResourceContent;

/**
 * Text content
 */
export interface TextContent {
  type: 'text';
  text: string;
}

/**
 * Image content
 */
export interface ImageContent {
  type: 'image';
  data: string;
  mimeType: string;
}

/**
 * Resource content
 */
export interface ResourceContent {
  type: 'resource';
  resource: {
    uri: string;
    mimeType: string;
    text?: string;
    blob?: string;
  };
}

/**
 * Prompt definition
 */
export interface PromptDefinition {
  /** Prompt name */
  name: string;
  /** Prompt description */
  description: string;
  /** Arguments */
  arguments?: PromptArgument[];
  /** Handler function */
  handler: PromptHandler;
}

/**
 * Prompt argument
 */
export interface PromptArgument {
  /** Argument name */
  name: string;
  /** Argument description */
  description: string;
  /** Is required */
  required: boolean;
}

/**
 * Prompt handler function type
 */
export type PromptHandler = (
  args: Record<string, string>
) => Promise<PromptResult>;

/**
 * Prompt result
 */
export interface PromptResult {
  /** Prompt description */
  description?: string;
  /** Messages */
  messages: PromptMessage[];
}

/**
 * Prompt message
 */
export interface PromptMessage {
  /** Role */
  role: 'user' | 'assistant';
  /** Content */
  content: TextContent | ImageContent;
}

/**
 * Resource definition
 */
export interface ResourceDefinition {
  /** Resource URI */
  uri: string;
  /** Resource name */
  name: string;
  /** Resource description */
  description?: string;
  /** MIME type */
  mimeType?: string;
  /** Handler function */
  handler: ResourceHandler;
}

/**
 * Resource handler function type
 */
export type ResourceHandler = () => Promise<ResourceResult>;

/**
 * Resource result
 */
export interface ResourceResult {
  /** Resource contents */
  contents: Array<{
    uri: string;
    mimeType: string;
    text?: string;
    blob?: string;
  }>;
}

/**
 * Resource template definition
 */
export interface ResourceTemplateDefinition {
  /** URI template */
  uriTemplate: string;
  /** Template name */
  name: string;
  /** Template description */
  description?: string;
  /** MIME type */
  mimeType?: string;
  /** Handler function */
  handler: ResourceTemplateHandler;
}

/**
 * Resource template handler function type
 */
export type ResourceTemplateHandler = (
  uri: string,
  params: Record<string, string>
) => Promise<ResourceResult>;

/**
 * JSON-RPC notification handler
 */
export type NotificationHandler = (
  method: string,
  params: Record<string, unknown>
) => void;

/**
 * Server capabilities
 */
export interface ServerCapabilities {
  tools?: {
    listChanged?: boolean;
  };
  prompts?: {
    listChanged?: boolean;
  };
  resources?: {
    subscribe?: boolean;
    listChanged?: boolean;
  };
  logging?: Record<string, never>;
}
