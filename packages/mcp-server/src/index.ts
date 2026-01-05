/**
 * @musubix/mcp-server - MUSUBIX MCP Server
 * 
 * Model Context Protocol Server for AI Coding Platforms
 * 
 * Supported platforms:
 * - Claude Code
 * - GitHub Copilot
 * - Cursor
 * - Gemini CLI
 * - Codex CLI
 * - Qwen Code
 * - Windsurf
 * 
 * @packageDocumentation
 * @module @musubix/mcp-server
 * 
 * @see REQ-INT-102 - MCP Server
 * @see DES-MUSUBIX-001 Section 11 - MCP Server Design
 */

// Version
export const VERSION = '1.0.0';

// Types
export type {
  ServerTransport,
  MCPServerConfig,
  ToolDefinition,
  ToolHandler,
  ToolResult,
  ToolContent,
  TextContent,
  ImageContent,
  ResourceContent,
  PromptDefinition,
  PromptArgument,
  PromptHandler,
  PromptResult,
  PromptMessage,
  ResourceDefinition,
  ResourceHandler,
  ResourceResult,
  ResourceTemplateDefinition,
  ResourceTemplateHandler,
  NotificationHandler,
  ServerCapabilities,
} from './types.js';

export { DEFAULT_SERVER_CONFIG } from './types.js';

// Server
export { MCPServer, createMCPServer, type MCPServerEvents } from './server.js';

// SDD Tools
export {
  sddTools,
  getSddTools,
  createRequirementsTool,
  validateRequirementsTool,
  createDesignTool,
  validateDesignTool,
  createTasksTool,
  queryKnowledgeTool,
  updateKnowledgeTool,
  validateConstitutionTool,
  validateTraceabilityTool,
} from './tools/index.js';

// Symbolic Tools
export {
  symbolicTools,
  getSymbolicTools,
  filterCodeTool,
  detectHallucinationsTool,
  checkConstitutionTool,
  estimateConfidenceTool,
  getPipelineInfoTool,
} from './tools/index.js';

// Ontology Tools
export {
  ontologyTools,
  getOntologyTools,
  consistencyValidateTool,
  validateTripleTool,
  checkCircularTool,
} from './tools/index.js';

// SDD Prompts
export {
  sddPrompts,
  getSddPrompts,
  requirementsAnalysisPrompt,
  requirementsReviewPrompt,
  designGenerationPrompt,
  designReviewPrompt,
  taskDecompositionPrompt,
  projectSteeringPrompt,
} from './prompts/index.js';

// SDD Resources
export {
  sddResources,
  sddResourceTemplates,
  getSddResources,
  getSddResourceTemplates,
  constitutionResource,
  earsPatternsResource,
  c4PatternsResource,
  adrTemplateResource,
  requirementDocTemplate,
  designDocTemplate,
  taskDocTemplate,
} from './resources/index.js';

// Platform Adapter
export {
  PlatformAdapter,
  createPlatformAdapter,
  getSupportedPlatforms,
  getPlatformConfig,
  type PlatformType,
  type PlatformCapabilities,
  type PlatformConfig,
  type PlatformDetectionResult,
  PLATFORM_CONFIGS,
} from './platform/index.js';

/**
 * MCP Server Entry Point
 * 
 * This module provides MCP tools, prompts, and resources for AI platforms.
 * 
 * @example
 * ```typescript
 * import { createMCPServer, VERSION, registerSDDTools, registerSDDPrompts, registerSDDResources } from '@musubix/mcp-server';
 * 
 * const server = createMCPServer({
 *   name: 'my-musubix-server',
 *   version: VERSION,
 *   transport: 'stdio',
 * });
 * 
 * // Register all SDD capabilities
 * registerSDDTools(server);
 * registerSDDPrompts(server);
 * registerSDDResources(server);
 * 
 * await server.start();
 * ```
 */

/**
 * Start Server Options
 */
export interface StartServerOptions {
  /** Transport type: 'stdio' or 'sse' */
  transport?: string;
  /** Port for SSE transport */
  port?: number;
}

/**
 * Start the MUSUBIX MCP Server
 * 
 * @param options - Server options
 */
export async function startServer(options: StartServerOptions = {}): Promise<void> {
  const transport = (options.transport || 'stdio') as 'stdio' | 'sse';
  const port = options.port || 3000;
  
  console.log(`Starting MUSUBIX MCP Server v${VERSION}...`);
  console.log(`Transport: ${transport}${transport === 'sse' ? ` (port: ${port})` : ''}`);
  
  // Import server and registries
  const { createMCPServer } = await import('./server.js');
  const { sddTools } = await import('./tools/index.js');
  const { sddPrompts } = await import('./prompts/index.js');
  const { sddResources, sddResourceTemplates } = await import('./resources/index.js');
  
  const server = createMCPServer({
    name: 'musubix-mcp-server',
    version: VERSION,
    transport,
    port,
  });

  // Import symbolic tools
  const { symbolicTools } = await import('./tools/index.js');

  // Import ontology tools
  const { ontologyTools } = await import('./tools/index.js');

  // Register all SDD tools, prompts, and resources
  for (const tool of sddTools) {
    server.registerTool(tool);
  }

  // Register symbolic tools
  for (const tool of symbolicTools) {
    server.registerTool(tool);
  }

  // Register ontology tools
  for (const tool of ontologyTools) {
    server.registerTool(tool);
  }
  
  for (const prompt of sddPrompts) {
    server.registerPrompt(prompt);
  }
  
  for (const resource of sddResources) {
    server.registerResource(resource);
  }
  
  for (const template of sddResourceTemplates) {
    server.registerResourceTemplate(template);
  }
  
  // Start the server
  await server.start();
  console.log('MUSUBIX MCP Server started successfully.');
}
