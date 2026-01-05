/**
 * YATA Integration Tools for MCP Server
 *
 * Provides automatic knowledge graph updates through MCP.
 *
 * @packageDocumentation
 * @module tools
 * @see REQ-YATA-AUTO-003
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

/**
 * Analyze code and extract entities for knowledge graph
 */
export const analyzeCodeTool: ToolDefinition = {
  name: 'yata_analyze_code',
  description: `Analyze code to extract entities (classes, functions, interfaces) 
and relationships (extends, implements, imports) for knowledge graph.

Use this tool when:
- Analyzing new or modified code files
- Building project knowledge graph
- Understanding code structure and dependencies

Returns extracted entities and relationships without persisting.`,
  inputSchema: {
    type: 'object',
    properties: {
      content: {
        type: 'string',
        description: 'The code content to analyze',
      },
      filePath: {
        type: 'string',
        description: 'File path for namespace extraction',
      },
      language: {
        type: 'string',
        description: 'Programming language (typescript, javascript)',
        default: 'typescript',
      },
    },
    required: ['content', 'filePath'],
  },
  handler: async (args) => {
    try {
      const { content, filePath } = args as {
        content: string;
        filePath: string;
        language?: string;
      };

      // Try to use full KnowledgeGraphUpdater if available
      let KnowledgeGraphUpdater: (new () => { analyzeCode: (content: string, filePath: string) => { entities: unknown[]; relationships: unknown[]; errors: string[] } }) | null = null;
      try {
        const mod = await import('@nahisaho/yata-local');
        KnowledgeGraphUpdater = mod.KnowledgeGraphUpdater;
      } catch {
        // Module not installed, will use fallback
      }

      if (!KnowledgeGraphUpdater) {
        // Fallback: simple analysis
        const entities = extractEntitiesSimple(content, filePath);
        return success({
          action: 'analyze_code',
          filePath,
          preview: true,
          entities: entities,
          relationships: [],
          summary: {
            entityCount: entities.length,
            relationshipCount: 0,
          },
        });
      }

      const updater = new KnowledgeGraphUpdater();
      const result = updater.analyzeCode(content, filePath);

      return success({
        action: 'analyze_code',
        filePath,
        preview: true,
        entities: result.entities,
        relationships: result.relationships,
        errors: result.errors,
        summary: {
          entityCount: result.entities.length,
          relationshipCount: result.relationships.length,
        },
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Update knowledge graph from code
 */
export const updateKnowledgeFromCodeTool: ToolDefinition = {
  name: 'yata_update_from_code',
  description: `Analyze code and update the YATA Local knowledge graph.

Use this tool when:
- Code has been generated or modified
- Building initial project knowledge graph
- Keeping knowledge graph in sync with codebase

Automatically:
- Extracts entities (classes, functions, interfaces, etc.)
- Detects relationships (extends, implements, imports)
- Updates YATA Local database
- Runs validation if configured`,
  inputSchema: {
    type: 'object',
    properties: {
      content: {
        type: 'string',
        description: 'The code content to analyze and persist',
      },
      filePath: {
        type: 'string',
        description: 'File path for namespace extraction',
      },
      databasePath: {
        type: 'string',
        description: 'YATA Local database path (default: ./yata-local.db)',
        default: './yata-local.db',
      },
      autoInfer: {
        type: 'boolean',
        description: 'Run inference after update',
        default: false,
      },
    },
    required: ['content', 'filePath'],
  },
  handler: async (args) => {
    try {
      const { content, filePath, databasePath, autoInfer } = args as {
        content: string;
        filePath: string;
        databasePath?: string;
        autoInfer?: boolean;
      };

      // Dynamic import
      let yataLocalModule: typeof import('@nahisaho/yata-local') | null = null;
      try {
        yataLocalModule = await import('@nahisaho/yata-local');
      } catch {
        // Module not installed
      }

      if (!yataLocalModule) {
        return error(
          'YATA Local not installed. Run: npm install @nahisaho/yata-local'
        );
      }

      const { createYataLocal, createYataBridge } = yataLocalModule;

      // Initialize YATA Local
      const yata = createYataLocal({ path: databasePath ?? './yata-local.db' });
      await yata.open();

      try {
        // Create bridge and update
        const bridge = createYataBridge(yata, {
          autoInfer: autoInfer ?? false,
          autoValidate: true,
        });

        const result = await bridge.updateFromCode(content, filePath);

        return success({
          action: 'update_knowledge_from_code',
          filePath,
          databasePath: databasePath ?? './yata-local.db',
          result,
        });
      } finally {
        await yata.close();
      }
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Bulk update knowledge graph from multiple files
 */
export const bulkUpdateKnowledgeTool: ToolDefinition = {
  name: 'yata_bulk_update',
  description: `Bulk update knowledge graph from multiple code files.

Use this tool when:
- Initializing knowledge graph for entire project
- Syncing large codebase changes
- Rebuilding knowledge graph`,
  inputSchema: {
    type: 'object',
    properties: {
      files: {
        type: 'array',
        description: 'Array of files to process',
        items: {
          type: 'object',
          properties: {
            content: { type: 'string' },
            filePath: { type: 'string' },
          },
          required: ['content', 'filePath'],
        },
      },
      databasePath: {
        type: 'string',
        description: 'YATA Local database path',
        default: './yata-local.db',
      },
    },
    required: ['files'],
  },
  handler: async (args) => {
    try {
      const { files, databasePath } = args as {
        files: Array<{ content: string; filePath: string }>;
        databasePath?: string;
      };

      let yataLocalModule: typeof import('@nahisaho/yata-local') | null = null;
      try {
        yataLocalModule = await import('@nahisaho/yata-local');
      } catch {
        // Module not installed
      }

      if (!yataLocalModule) {
        return error(
          'YATA Local not installed. Run: npm install @nahisaho/yata-local'
        );
      }

      const { createYataLocal, createYataBridge } = yataLocalModule;

      const yata = createYataLocal({ path: databasePath ?? './yata-local.db' });
      await yata.open();

      try {
        const bridge = createYataBridge(yata);
        const result = await bridge.updateFromFiles(files);

        return success({
          action: 'bulk_update_knowledge',
          fileCount: files.length,
          databasePath: databasePath ?? './yata-local.db',
          result,
        });
      } finally {
        await yata.close();
      }
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Query knowledge graph
 */
export const queryKnowledgeGraphTool: ToolDefinition = {
  name: 'yata_query',
  description: `Query the YATA Local knowledge graph.

Use this tool when:
- Finding entities by name or type
- Exploring relationships
- Understanding code dependencies`,
  inputSchema: {
    type: 'object',
    properties: {
      searchText: {
        type: 'string',
        description: 'Full-text search query',
      },
      entityTypes: {
        type: 'array',
        description: 'Filter by entity types',
        items: { type: 'string' },
      },
      namespace: {
        type: 'string',
        description: 'Filter by namespace',
      },
      databasePath: {
        type: 'string',
        description: 'YATA Local database path',
        default: './yata-local.db',
      },
      limit: {
        type: 'number',
        description: 'Maximum results',
        default: 50,
      },
    },
    required: [],
  },
  handler: async (args) => {
    try {
      const { searchText, entityTypes, namespace, databasePath, limit } =
        args as {
          searchText?: string;
          entityTypes?: string[];
          namespace?: string;
          databasePath?: string;
          limit?: number;
        };

      const yataLocalModule = await import('@nahisaho/yata-local').catch(
        () => null
      );

      if (!yataLocalModule) {
        return error(
          'YATA Local not installed. Run: npm install @nahisaho/yata-local'
        );
      }

      const { createYataLocal } = yataLocalModule;
      const yata = createYataLocal({ path: databasePath ?? './yata-local.db' });
      await yata.open();

      try {
        let entities;

        if (searchText) {
          entities = await yata.search(searchText, limit ?? 50);
        } else {
          const result = await yata.query({
            entityFilters: {
              types: entityTypes as never[],
              namespace: namespace,
            },
          });
          entities = result.entities.slice(0, limit ?? 50);
        }

        return success({
          action: 'query_knowledge',
          query: { searchText, entityTypes, namespace },
          resultCount: entities.length,
          entities,
        });
      } finally {
        await yata.close();
      }
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Simple entity extraction (fallback when full module not available)
 */
function extractEntitiesSimple(
  content: string,
  _filePath: string
): Array<{ type: string; name: string; line: number }> {
  const entities: Array<{ type: string; name: string; line: number }> = [];
  const lines = content.split('\n');

  const patterns = [
    { regex: /^(?:export\s+)?(?:abstract\s+)?class\s+(\w+)/, type: 'class' },
    { regex: /^(?:export\s+)?interface\s+(\w+)/, type: 'interface' },
    { regex: /^(?:export\s+)?(?:async\s+)?function\s+(\w+)/, type: 'function' },
    { regex: /^(?:export\s+)?type\s+(\w+)\s*=/, type: 'type' },
    { regex: /^(?:export\s+)?enum\s+(\w+)/, type: 'enum' },
  ];

  for (let i = 0; i < lines.length; i++) {
    const trimmed = lines[i].trim();
    for (const { regex, type } of patterns) {
      const match = trimmed.match(regex);
      if (match) {
        entities.push({ type, name: match[1], line: i + 1 });
        break;
      }
    }
  }

  return entities;
}

/**
 * All YATA integration tools
 */
export const yataTools: ToolDefinition[] = [
  analyzeCodeTool,
  updateKnowledgeFromCodeTool,
  bulkUpdateKnowledgeTool,
  queryKnowledgeGraphTool,
];

/**
 * Get all YATA tool definitions
 */
export function getYataTools(): ToolDefinition[] {
  return yataTools;
}
