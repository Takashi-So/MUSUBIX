/**
 * MCP Tools for CodeGraph
 *
 * Tool definitions for code graph analysis via MCP
 *
 * @packageDocumentation
 * @module tools/codegraph
 *
 * @see REQ-CG-MCP-001 - MCP Integration
 * @see DES-CG-007
 */

import type { ToolDefinition, ToolResult, TextContent } from '../types.js';

/**
 * Create text content helper
 */
function text(content: string): TextContent {
  return { type: 'text', text: content };
}

/**
 * Success result helper
 */
function success(content: string | object): ToolResult {
  const textContent =
    typeof content === 'string' ? content : JSON.stringify(content, null, 2);
  return {
    content: [text(textContent)],
  };
}

/**
 * Error result helper
 */
function error(message: string): ToolResult {
  return {
    content: [text(`Error: ${message}`)],
    isError: true,
  };
}

// Lazy-loaded CodeGraph instance
let codeGraphInstance: unknown = null;

/**
 * Get or create CodeGraph instance
 */
async function getCodeGraph() {
  if (!codeGraphInstance) {
    const { createCodeGraph } = await import('@nahisaho/musubix-codegraph');
    codeGraphInstance = createCodeGraph({ storage: 'memory' });
  }
  return codeGraphInstance as {
    index: (path: string) => Promise<unknown>;
    query: (query: string | object) => Promise<unknown>;
    findDependencies: (name: string, options?: unknown) => Promise<unknown>;
    findCallers: (name: string) => Promise<unknown>;
    findCallees: (name: string) => Promise<unknown>;
    globalSearch: (query: string, options?: unknown) => Promise<unknown>;
    localSearch: (entityId: string, options?: unknown) => Promise<unknown>;
    getStats: () => Promise<unknown>;
    close: () => Promise<void>;
  };
}

// ============================================================
// Indexing Tools
// ============================================================

/**
 * Index a code repository
 */
export const codegraphIndexTool: ToolDefinition = {
  name: 'codegraph_index',
  description:
    'Index a code repository or directory to build a code graph. This extracts entities (classes, functions, etc.) and their relationships.',
  inputSchema: {
    type: 'object',
    properties: {
      path: {
        type: 'string',
        description: 'Path to the repository or directory to index',
      },
    },
    required: ['path'],
  },
  handler: async (args) => {
    try {
      const { path } = args as { path: string };
      const cg = await getCodeGraph();
      const result = await cg.index(path);

      return success({
        action: 'index',
        path,
        result,
        message: `Successfully indexed ${path}`,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Query Tools
// ============================================================

/**
 * Query the code graph
 */
export const codegraphQueryTool: ToolDefinition = {
  name: 'codegraph_query',
  description:
    'Query the code graph for entities matching specific criteria (type, name pattern, file path, etc.)',
  inputSchema: {
    type: 'object',
    properties: {
      entityTypes: {
        type: 'array',
        items: { type: 'string' },
        description:
          'Filter by entity types (class, function, interface, etc.)',
      },
      namePattern: {
        type: 'string',
        description: 'Glob pattern to match entity names',
      },
      filePath: {
        type: 'string',
        description: 'Filter by file path',
      },
      textSearch: {
        type: 'string',
        description: 'Full-text search query',
      },
      limit: {
        type: 'number',
        description: 'Maximum number of results',
      },
    },
    required: [],
  },
  handler: async (args) => {
    try {
      const query = args as {
        entityTypes?: string[];
        namePattern?: string;
        filePath?: string;
        textSearch?: string;
        limit?: number;
      };
      const cg = await getCodeGraph();
      const result = await cg.query(query);

      return success({
        action: 'query',
        query,
        result,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Dependency Analysis Tools
// ============================================================

/**
 * Find dependencies of an entity
 */
export const codegraphFindDependenciesTool: ToolDefinition = {
  name: 'codegraph_find_dependencies',
  description:
    'Find all dependencies (imports, extends, implements, calls) of a code entity',
  inputSchema: {
    type: 'object',
    properties: {
      name: {
        type: 'string',
        description: 'Name of the entity to find dependencies for',
      },
      depth: {
        type: 'number',
        description: 'Maximum depth to traverse (default: 5)',
      },
      relationTypes: {
        type: 'array',
        items: { type: 'string' },
        description: 'Types of relations to follow (calls, imports, extends, etc.)',
      },
    },
    required: ['name'],
  },
  handler: async (args) => {
    try {
      const { name, depth, relationTypes } = args as {
        name: string;
        depth?: number;
        relationTypes?: string[];
      };
      const cg = await getCodeGraph();
      const result = await cg.findDependencies(name, { depth, relationTypes });

      return success({
        action: 'find_dependencies',
        name,
        options: { depth, relationTypes },
        result,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Find callers of a function/method
 */
export const codegraphFindCallersTool: ToolDefinition = {
  name: 'codegraph_find_callers',
  description: 'Find all entities that call a specific function or method',
  inputSchema: {
    type: 'object',
    properties: {
      name: {
        type: 'string',
        description: 'Name of the function/method to find callers for',
      },
    },
    required: ['name'],
  },
  handler: async (args) => {
    try {
      const { name } = args as { name: string };
      const cg = await getCodeGraph();
      const result = await cg.findCallers(name);

      return success({
        action: 'find_callers',
        name,
        result,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Find callees of a function/method
 */
export const codegraphFindCalleesTool: ToolDefinition = {
  name: 'codegraph_find_callees',
  description: 'Find all functions/methods called by a specific entity',
  inputSchema: {
    type: 'object',
    properties: {
      name: {
        type: 'string',
        description: 'Name of the entity to find callees for',
      },
    },
    required: ['name'],
  },
  handler: async (args) => {
    try {
      const { name } = args as { name: string };
      const cg = await getCodeGraph();
      const result = await cg.findCallees(name);

      return success({
        action: 'find_callees',
        name,
        result,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// GraphRAG Search Tools
// ============================================================

/**
 * Global semantic search across the codebase
 */
export const codegraphGlobalSearchTool: ToolDefinition = {
  name: 'codegraph_global_search',
  description:
    'Perform a semantic search across the entire codebase using GraphRAG. Best for high-level questions about architecture and code organization.',
  inputSchema: {
    type: 'object',
    properties: {
      query: {
        type: 'string',
        description: 'Natural language query about the codebase',
      },
      limit: {
        type: 'number',
        description: 'Maximum number of results (default: 10)',
      },
      includeSummaries: {
        type: 'boolean',
        description: 'Include community summaries in results',
      },
    },
    required: ['query'],
  },
  handler: async (args) => {
    try {
      const { query, limit, includeSummaries } = args as {
        query: string;
        limit?: number;
        includeSummaries?: boolean;
      };
      const cg = await getCodeGraph();
      const result = await cg.globalSearch(query, { limit, includeSummaries });

      return success({
        action: 'global_search',
        query,
        options: { limit, includeSummaries },
        result,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Local context search around a specific entity
 */
export const codegraphLocalSearchTool: ToolDefinition = {
  name: 'codegraph_local_search',
  description:
    'Search for related code around a specific entity. Best for understanding how a particular piece of code fits into its context.',
  inputSchema: {
    type: 'object',
    properties: {
      entityId: {
        type: 'string',
        description: 'ID or name of the entity to search around',
      },
      radius: {
        type: 'number',
        description: 'Number of hops to traverse (default: 2)',
      },
      limit: {
        type: 'number',
        description: 'Maximum number of results',
      },
    },
    required: ['entityId'],
  },
  handler: async (args) => {
    try {
      const { entityId, radius, limit } = args as {
        entityId: string;
        radius?: number;
        limit?: number;
      };
      const cg = await getCodeGraph();
      const result = await cg.localSearch(entityId, { radius, limit });

      return success({
        action: 'local_search',
        entityId,
        options: { radius, limit },
        result,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Statistics Tools
// ============================================================

/**
 * Get code graph statistics
 */
export const codegraphStatsTool: ToolDefinition = {
  name: 'codegraph_stats',
  description:
    'Get statistics about the indexed code graph (entity counts, relation counts, etc.)',
  inputSchema: {
    type: 'object',
    properties: {},
    required: [],
  },
  handler: async () => {
    try {
      const cg = await getCodeGraph();
      const result = await cg.getStats();

      return success({
        action: 'stats',
        result,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Exports
// ============================================================

/**
 * All CodeGraph tools
 */
export const codegraphTools: ToolDefinition[] = [
  codegraphIndexTool,
  codegraphQueryTool,
  codegraphFindDependenciesTool,
  codegraphFindCallersTool,
  codegraphFindCalleesTool,
  codegraphGlobalSearchTool,
  codegraphLocalSearchTool,
  codegraphStatsTool,
];

/**
 * Get all CodeGraph tools
 */
export function getCodeGraphTools(): ToolDefinition[] {
  return codegraphTools;
}

/**
 * Handle CodeGraph tool call
 */
export async function handleCodeGraphTool(
  name: string,
  args: Record<string, unknown>
): Promise<ToolResult> {
  const tool = codegraphTools.find((t) => t.name === name);
  if (!tool) {
    return error(`Unknown CodeGraph tool: ${name}`);
  }
  return tool.handler(args);
}

/**
 * Reset CodeGraph instance (for testing)
 */
export async function resetCodeGraph(): Promise<void> {
  if (codeGraphInstance) {
    const cg = codeGraphInstance as { close: () => Promise<void> };
    await cg.close();
    codeGraphInstance = null;
  }
}
