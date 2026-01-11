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
export const VERSION = '2.4.1';

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

// v2.4.0 NEW - Agent Orchestration Tools
export {
  agentTools,
  agentDispatchTool,
  agentStatusTool,
  agentCancelTool,
  agentAnalyzeTool,
  handleAgentDispatch,
  handleAgentStatus,
  handleAgentCancel,
  handleAgentAnalyze,
  type AgentDispatchInput,
  type AgentStatusInput,
  type AgentCancelInput,
  type AgentAnalyzeInput,
} from './tools/index.js';

// v2.4.0 NEW - Workflow Engine Tools
export {
  workflowTools,
  workflowCreateTool,
  workflowTransitionTool,
  workflowStatusTool,
  workflowReviewTool,
  workflowGateTool,
  handleWorkflowCreate,
  handleWorkflowTransition,
  handleWorkflowStatus,
  handleWorkflowReview,
  handleWorkflowGate,
  type WorkflowCreateInput,
  type WorkflowTransitionInput,
  type WorkflowStatusInput,
  type WorkflowReviewInput,
  type WorkflowGateInput,
} from './tools/index.js';

// v2.4.0 NEW - Skill Manager Tools
export {
  skillTools,
  skillListTool,
  skillExecuteTool,
  skillValidateTool,
  skillInfoTool,
  skillRegisterTool,
  handleSkillList,
  handleSkillExecute,
  handleSkillValidate,
  handleSkillInfo,
  handleSkillRegister,
  type SkillListInput,
  type SkillExecuteInput,
  type SkillValidateInput,
  type SkillInfoInput,
  type SkillRegisterInput,
} from './tools/index.js';

// v2.4.0 NEW - Tool Categories
export { toolCategories } from './tools/index.js';

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
  
  // v2.4.0 NEW: Import and register agent, workflow, and skill tools
  const { agentTools, workflowTools, skillTools } = await import('./tools/index.js');
  
  // Register agent tools
  for (const tool of agentTools) {
    server.registerTool(tool);
  }
  
  // Register workflow tools
  for (const tool of workflowTools) {
    server.registerTool(tool);
  }
  
  // Register skill tools
  for (const tool of skillTools) {
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
