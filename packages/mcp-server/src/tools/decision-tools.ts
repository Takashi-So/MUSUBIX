/**
 * Decision Tools - MCP tools for ADR (Architecture Decision Records) management
 * 
 * @packageDocumentation
 * @module tools/decision-tools
 */

import { Tool } from '@modelcontextprotocol/sdk/types.js';
import {
  createDecisionManager,
  DecisionManager,
  ADR,
  ADRDraft,
  ADRFilter,
  ADR_TEMPLATE,
} from '@musubix/decisions';

// Singleton manager instance
let decisionManager: DecisionManager | null = null;

/**
 * Get or create decision manager
 */
export function getDecisionManager(projectPath?: string): DecisionManager {
  if (!decisionManager) {
    const path = projectPath || process.cwd();
    decisionManager = createDecisionManager(`${path}/docs/decisions`) as DecisionManager;
  }
  return decisionManager;
}

/**
 * Reset decision manager (for testing)
 */
export function resetDecisionManager(): void {
  decisionManager = null;
}

// Tool definitions
export const decisionCreateTool: Tool = {
  name: 'decision_create',
  description: 'Create a new Architecture Decision Record (ADR)',
  inputSchema: {
    type: 'object',
    properties: {
      title: { type: 'string', description: 'Decision title' },
      context: { type: 'string', description: 'Background context for the decision' },
      decision: { type: 'string', description: 'The decision made' },
      rationale: { type: 'string', description: 'Reasons for the decision' },
      alternatives: { 
        type: 'array', 
        items: { type: 'string' },
        description: 'Alternative options considered' 
      },
      consequences: { 
        type: 'array', 
        items: { type: 'string' },
        description: 'Expected consequences' 
      },
      relatedRequirements: { 
        type: 'array', 
        items: { type: 'string' },
        description: 'Related requirement IDs (e.g., REQ-001)' 
      },
      decider: { type: 'string', description: 'Who made the decision' },
    },
    required: ['title', 'context', 'decision'],
  },
};

export const decisionListTool: Tool = {
  name: 'decision_list',
  description: 'List all ADRs with optional filters',
  inputSchema: {
    type: 'object',
    properties: {
      status: { 
        type: 'string', 
        enum: ['proposed', 'accepted', 'deprecated', 'superseded'],
        description: 'Filter by status' 
      },
      keyword: { type: 'string', description: 'Search keyword' },
    },
    required: [],
  },
};

export const decisionGetTool: Tool = {
  name: 'decision_get',
  description: 'Get a specific ADR by ID',
  inputSchema: {
    type: 'object',
    properties: {
      id: { type: 'string', description: 'ADR ID (e.g., 0001)' },
    },
    required: ['id'],
  },
};

export const decisionAcceptTool: Tool = {
  name: 'decision_accept',
  description: 'Accept a proposed ADR',
  inputSchema: {
    type: 'object',
    properties: {
      id: { type: 'string', description: 'ADR ID to accept' },
    },
    required: ['id'],
  },
};

export const decisionDeprecateTool: Tool = {
  name: 'decision_deprecate',
  description: 'Deprecate an ADR, optionally marking it as superseded',
  inputSchema: {
    type: 'object',
    properties: {
      id: { type: 'string', description: 'ADR ID to deprecate' },
      supersededBy: { type: 'string', description: 'ID of the superseding ADR (optional)' },
    },
    required: ['id'],
  },
};

export const decisionSearchTool: Tool = {
  name: 'decision_search',
  description: 'Search ADRs by keyword',
  inputSchema: {
    type: 'object',
    properties: {
      query: { type: 'string', description: 'Search query' },
    },
    required: ['query'],
  },
};

export const decisionFindByRequirementTool: Tool = {
  name: 'decision_find_by_requirement',
  description: 'Find ADRs related to a requirement',
  inputSchema: {
    type: 'object',
    properties: {
      requirementId: { type: 'string', description: 'Requirement ID (e.g., REQ-001)' },
    },
    required: ['requirementId'],
  },
};

export const decisionGenerateIndexTool: Tool = {
  name: 'decision_generate_index',
  description: 'Generate or update the ADR index file',
  inputSchema: {
    type: 'object',
    properties: {},
    required: [],
  },
};

// Tool handlers
export async function handleDecisionCreate(
  input: ADRDraft
): Promise<{ success: boolean; adr: ADR }> {
  const manager = getDecisionManager();
  const draft: ADRDraft = {
    title: input.title,
    context: input.context,
    decision: input.decision,
    rationale: input.rationale,
    alternatives: input.alternatives,
    consequences: input.consequences,
    relatedRequirements: input.relatedRequirements,
    decider: input.decider,
  };
  const adr = await manager.create(draft);
  return { success: true, adr };
}

export async function handleDecisionList(
  input: ADRFilter
): Promise<{ adrs: ADR[]; count: number }> {
  const manager = getDecisionManager();
  const adrs = await manager.list(input);
  return { adrs, count: adrs.length };
}

export async function handleDecisionGet(
  input: { id: string }
): Promise<{ adr: ADR | null }> {
  const manager = getDecisionManager();
  const adr = await manager.get(input.id);
  return { adr: adr || null };
}

export async function handleDecisionAccept(
  input: { id: string }
): Promise<{ success: boolean; adr: ADR }> {
  const manager = getDecisionManager();
  const adr = await manager.accept(input.id);
  return { success: true, adr };
}

export async function handleDecisionDeprecate(
  input: { id: string; supersededBy?: string }
): Promise<{ success: boolean; adr: ADR }> {
  const manager = getDecisionManager();
  const adr = await manager.deprecate(input.id, input.supersededBy);
  return { success: true, adr };
}

export async function handleDecisionSearch(
  input: { query: string }
): Promise<{ adrs: ADR[]; count: number }> {
  const manager = getDecisionManager();
  const adrs = await manager.search(input.query);
  return { adrs, count: adrs.length };
}

export async function handleDecisionFindByRequirement(
  input: { requirementId: string }
): Promise<{ adrs: ADR[]; count: number }> {
  const manager = getDecisionManager();
  const adrs = await manager.findByRequirement(input.requirementId);
  return { adrs, count: adrs.length };
}

export async function handleDecisionGenerateIndex(): Promise<{ success: boolean; path: string }> {
  const manager = getDecisionManager();
  await manager.generateIndex();
  const path = `${process.cwd()}/docs/decisions/index.md`;
  return { success: true, path };
}

// Tool collection
export const decisionTools: Tool[] = [
  decisionCreateTool,
  decisionListTool,
  decisionGetTool,
  decisionAcceptTool,
  decisionDeprecateTool,
  decisionSearchTool,
  decisionFindByRequirementTool,
  decisionGenerateIndexTool,
];

export function getDecisionTools(): Tool[] {
  return decisionTools;
}

export async function handleDecisionTool(
  name: string,
  args: Record<string, unknown>
): Promise<unknown> {
  switch (name) {
    case 'decision_create':
      return handleDecisionCreate(args as unknown as ADRDraft);
    case 'decision_list':
      return handleDecisionList(args as Parameters<typeof handleDecisionList>[0]);
    case 'decision_get':
      return handleDecisionGet(args as Parameters<typeof handleDecisionGet>[0]);
    case 'decision_accept':
      return handleDecisionAccept(args as Parameters<typeof handleDecisionAccept>[0]);
    case 'decision_deprecate':
      return handleDecisionDeprecate(args as Parameters<typeof handleDecisionDeprecate>[0]);
    case 'decision_search':
      return handleDecisionSearch(args as Parameters<typeof handleDecisionSearch>[0]);
    case 'decision_find_by_requirement':
      return handleDecisionFindByRequirement(args as Parameters<typeof handleDecisionFindByRequirement>[0]);
    case 'decision_generate_index':
      return handleDecisionGenerateIndex();
    default:
      throw new Error(`Unknown decision tool: ${name}`);
  }
}

// Re-export template
export { ADR_TEMPLATE };
