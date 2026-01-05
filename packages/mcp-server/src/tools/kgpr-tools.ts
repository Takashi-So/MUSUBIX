/**
 * KGPR MCP Tools
 *
 * Knowledge Graph Pull Request tools for MCP Server
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-mcp-server/tools
 */

import type { ToolDefinition } from '../types.js';

const success = (data: unknown) => ({
  content: [{ type: 'text' as const, text: JSON.stringify(data, null, 2) }],
});

const error = (message: string) => ({
  content: [{ type: 'text' as const, text: `Error: ${message}` }],
  isError: true,
});

/**
 * KGPR Create Tool - Create a new Knowledge Graph PR
 */
export const kgprCreateTool: ToolDefinition = {
  name: 'kgpr_create',
  description: `Create a new Knowledge Graph Pull Request (KGPR) from your local knowledge graph.
This is similar to creating a GitHub PR - it packages your local knowledge (entities, relationships)
for review and potential merge into the global knowledge graph.

Use this when you want to share patterns, code structures, or domain knowledge with the community.

The tool will:
1. Extract entities/relationships from your local YATA database
2. Apply privacy filters (remove sensitive info)
3. Create a draft KGPR ready for submission

Example use cases:
- Sharing React component patterns
- Contributing TypeScript design patterns
- Documenting API integration patterns`,
  inputSchema: {
    type: 'object',
    properties: {
      title: {
        type: 'string',
        description: 'KGPR title (like a PR title)',
      },
      description: {
        type: 'string',
        description: 'Description of what knowledge is being shared',
      },
      sourceNamespace: {
        type: 'string',
        description: 'Namespace to include (default: all)',
      },
      labels: {
        type: 'array',
        description: 'Labels/tags for categorization',
        items: { type: 'string' },
      },
      entityTypes: {
        type: 'array',
        description: 'Filter to specific entity types (class, function, interface, etc.)',
        items: { type: 'string' },
      },
      privacyLevel: {
        type: 'string',
        description: 'Privacy filter level',
        enum: ['strict', 'moderate', 'none'],
        default: 'moderate',
      },
      localDatabasePath: {
        type: 'string',
        description: 'YATA Local database path',
        default: './yata-local.db',
      },
    },
    required: ['title'],
  },
  handler: async (args) => {
    try {
      const {
        title,
        description,
        sourceNamespace,
        labels,
        entityTypes,
        privacyLevel,
        localDatabasePath,
      } = args as {
        title: string;
        description?: string;
        sourceNamespace?: string;
        labels?: string[];
        entityTypes?: string[];
        privacyLevel?: 'strict' | 'moderate' | 'none';
        localDatabasePath?: string;
      };

      // Dynamic import for optional dependencies
      let yataLocalModule: typeof import('@nahisaho/yata-local') | null = null;
      let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

      try {
        yataLocalModule = await import('@nahisaho/yata-local');
      } catch {
        // Not installed
      }

      try {
        yataGlobalModule = await import('@nahisaho/yata-global');
      } catch {
        // Not installed
      }

      if (!yataLocalModule) {
        return error('YATA Local not installed. Run: npm install @nahisaho/yata-local');
      }

      if (!yataGlobalModule) {
        return error('YATA Global not installed. Run: npm install @nahisaho/yata-global');
      }

      const { createYataLocal } = yataLocalModule;
      const { createKGPRManager } = yataGlobalModule;

      // Connect to local KG
      const yataLocal = createYataLocal({ path: localDatabasePath ?? './yata-local.db' });
      await yataLocal.open();

      try {
        // Create KGPR manager
        const kgprManager = createKGPRManager();

        // Build entity map for relationship lookup
        const buildEntityMap = async () => {
          const result = await yataLocal.query({});
          const map = new Map<string, { name: string; namespace: string }>();
          for (const e of result.entities) {
            map.set(e.id, { name: e.name, namespace: e.namespace ?? 'default' });
          }
          return map;
        };

        // Adapter to connect YATA Local to KGPR Manager
        kgprManager.connectLocalKG({
          queryEntities: async (ns?: string) => {
            const result = await yataLocal.query({
              entityFilters: ns ? { namespace: ns } : undefined,
            });
            return result.entities.map((e) => ({
              id: e.id,
              name: e.name,
              type: e.type,
              namespace: e.namespace ?? 'default',
              filePath: e.metadata?.filePath as string | undefined,
              line: e.metadata?.line as number | undefined,
              metadata: e.metadata,
            }));
          },
          queryRelationships: async (ns?: string) => {
            const result = await yataLocal.query({
              entityFilters: ns ? { namespace: ns } : undefined,
            });
            const entityMap = await buildEntityMap();
            return result.relationships.map((r) => {
              const source = entityMap.get(r.sourceId) ?? { name: r.sourceId, namespace: 'unknown' };
              const target = entityMap.get(r.targetId) ?? { name: r.targetId, namespace: 'unknown' };
              return {
                id: r.id,
                sourceName: source.name,
                sourceNamespace: source.namespace,
                targetName: target.name,
                targetNamespace: target.namespace,
                type: r.type,
                metadata: r.metadata,
              };
            });
          },
        });

        // Create KGPR
        const kgpr = await kgprManager.create({
          title,
          description,
          sourceNamespace,
          labels,
          entityTypes,
          privacyLevel: privacyLevel ?? 'moderate',
        });

        return success({
          action: 'kgpr_created',
          kgprId: kgpr.id,
          title: kgpr.title,
          status: kgpr.status,
          stats: kgpr.diff.stats,
          message: `KGPR "${kgpr.title}" created as draft. Use kgpr_submit to submit for review.`,
        });
      } finally {
        await yataLocal.close();
      }
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * KGPR Diff Tool - Preview changes before creating KGPR
 */
export const kgprDiffTool: ToolDefinition = {
  name: 'kgpr_diff',
  description: `Preview the knowledge graph diff before creating a KGPR.
Shows what entities and relationships would be included in the KGPR,
after applying privacy filters.

Use this to:
- Review what will be shared
- Verify sensitive data is filtered out
- Check the scope of changes`,
  inputSchema: {
    type: 'object',
    properties: {
      sourceNamespace: {
        type: 'string',
        description: 'Namespace to include (default: all)',
      },
      entityTypes: {
        type: 'array',
        description: 'Filter to specific entity types',
        items: { type: 'string' },
      },
      privacyLevel: {
        type: 'string',
        description: 'Privacy filter level',
        enum: ['strict', 'moderate', 'none'],
        default: 'moderate',
      },
      localDatabasePath: {
        type: 'string',
        description: 'YATA Local database path',
        default: './yata-local.db',
      },
    },
    required: [],
  },
  handler: async (args) => {
    try {
      const { sourceNamespace, entityTypes, privacyLevel, localDatabasePath } = args as {
        sourceNamespace?: string;
        entityTypes?: string[];
        privacyLevel?: 'strict' | 'moderate' | 'none';
        localDatabasePath?: string;
      };

      let yataLocalModule: typeof import('@nahisaho/yata-local') | null = null;
      let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

      try {
        yataLocalModule = await import('@nahisaho/yata-local');
      } catch {
        // Not installed
      }

      try {
        yataGlobalModule = await import('@nahisaho/yata-global');
      } catch {
        // Not installed
      }

      if (!yataLocalModule) {
        return error('YATA Local not installed');
      }

      if (!yataGlobalModule) {
        return error('YATA Global not installed');
      }

      const { createYataLocal } = yataLocalModule;
      const { createKGPRManager } = yataGlobalModule;

      const yataLocal = createYataLocal({ path: localDatabasePath ?? './yata-local.db' });
      await yataLocal.open();

      try {
        const kgprManager = createKGPRManager();

        // Build entity map for relationship lookup
        const buildEntityMap = async () => {
          const result = await yataLocal.query({});
          const map = new Map<string, { name: string; namespace: string }>();
          for (const e of result.entities) {
            map.set(e.id, { name: e.name, namespace: e.namespace ?? 'default' });
          }
          return map;
        };

        kgprManager.connectLocalKG({
          queryEntities: async (ns?: string) => {
            const result = await yataLocal.query({
              entityFilters: ns ? { namespace: ns } : undefined,
            });
            return result.entities.map((e) => ({
              id: e.id,
              name: e.name,
              type: e.type,
              namespace: e.namespace ?? 'default',
              filePath: e.metadata?.filePath as string | undefined,
              line: e.metadata?.line as number | undefined,
              metadata: e.metadata,
            }));
          },
          queryRelationships: async (ns?: string) => {
            const result = await yataLocal.query({
              entityFilters: ns ? { namespace: ns } : undefined,
            });
            const entityMap = await buildEntityMap();
            return result.relationships.map((r) => {
              const source = entityMap.get(r.sourceId) ?? { name: r.sourceId, namespace: 'unknown' };
              const target = entityMap.get(r.targetId) ?? { name: r.targetId, namespace: 'unknown' };
              return {
                id: r.id,
                sourceName: source.name,
                sourceNamespace: source.namespace,
                targetName: target.name,
                targetNamespace: target.namespace,
                type: r.type,
                metadata: r.metadata,
              };
            });
          },
        });

        const diff = await kgprManager.previewDiff({
          sourceNamespace,
          entityTypes,
          privacyLevel: privacyLevel ?? 'moderate',
        });

        return success({
          action: 'kgpr_diff_preview',
          stats: diff.stats,
          entities: {
            added: diff.entities.added.slice(0, 20), // Limit for display
            totalAdded: diff.entities.added.length,
          },
          relationships: {
            added: diff.relationships.added.slice(0, 20),
            totalAdded: diff.relationships.added.length,
          },
          privacyLevel: privacyLevel ?? 'moderate',
        });
      } finally {
        await yataLocal.close();
      }
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * KGPR List Tool - List KGPRs
 */
export const kgprListTool: ToolDefinition = {
  name: 'kgpr_list',
  description: `List Knowledge Graph Pull Requests.
Shows both local drafts and (when connected) remote KGPRs from YATA Global.

Use this to:
- View your draft KGPRs
- Browse open KGPRs from the community
- Track the status of submitted KGPRs`,
  inputSchema: {
    type: 'object',
    properties: {
      status: {
        type: 'string',
        description: 'Filter by status',
        enum: ['draft', 'open', 'reviewing', 'approved', 'changes_requested', 'merged', 'closed'],
      },
      search: {
        type: 'string',
        description: 'Search query',
      },
      labels: {
        type: 'array',
        description: 'Filter by labels',
        items: { type: 'string' },
      },
      limit: {
        type: 'number',
        description: 'Maximum results',
        default: 20,
      },
    },
    required: [],
  },
  handler: async (args) => {
    try {
      const { status, search, labels, limit } = args as {
        status?: string;
        search?: string;
        labels?: string[];
        limit?: number;
      };

      let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

      try {
        yataGlobalModule = await import('@nahisaho/yata-global');
      } catch {
        // Not installed
      }

      if (!yataGlobalModule) {
        return error('YATA Global not installed');
      }

      const { createKGPRManager } = yataGlobalModule;
      const kgprManager = createKGPRManager();

      const result = await kgprManager.list({
        status: status as import('@nahisaho/yata-global').KGPRStatus | undefined,
        search,
        labels,
        limit: limit ?? 20,
      });

      return success({
        action: 'kgpr_list',
        total: result.total,
        kgprs: result.kgprs.map((kgpr) => ({
          id: kgpr.id,
          title: kgpr.title,
          status: kgpr.status,
          authorName: kgpr.authorName,
          labels: kgpr.labels,
          stats: kgpr.diff.stats,
          createdAt: kgpr.createdAt,
        })),
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * KGPR Submit Tool - Submit a draft KGPR
 */
export const kgprSubmitTool: ToolDefinition = {
  name: 'kgpr_submit',
  description: `Submit a draft KGPR for review.
This will send your KGPR to YATA Global where the community can review it.

After submission:
- Community members can comment and review
- AI quality checks are performed
- Duplicate detection runs automatically
- Once approved, it can be merged into the global knowledge graph`,
  inputSchema: {
    type: 'object',
    properties: {
      kgprId: {
        type: 'string',
        description: 'KGPR ID to submit',
      },
    },
    required: ['kgprId'],
  },
  handler: async (args) => {
    try {
      const { kgprId } = args as { kgprId: string };

      let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

      try {
        yataGlobalModule = await import('@nahisaho/yata-global');
      } catch {
        // Not installed
      }

      if (!yataGlobalModule) {
        return error('YATA Global not installed');
      }

      const { createKGPRManager } = yataGlobalModule;
      const kgprManager = createKGPRManager();

      const result = await kgprManager.submit(kgprId);

      if (!result.success) {
        return error(result.error ?? 'Failed to submit KGPR');
      }

      return success({
        action: 'kgpr_submitted',
        kgprId: result.kgprId,
        kgprUrl: result.kgprUrl,
        qualityScore: result.qualityScore,
        duplicateWarnings: result.duplicateWarnings,
        message: 'KGPR submitted for review.',
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * KGPR Review Tool - Review a KGPR
 */
export const kgprReviewTool: ToolDefinition = {
  name: 'kgpr_review',
  description: `Submit a review for a Knowledge Graph PR.
Similar to GitHub PR reviews, you can:
- Approve: The knowledge is accurate and valuable
- Request Changes: Suggest improvements
- Comment: Add feedback without approval/rejection`,
  inputSchema: {
    type: 'object',
    properties: {
      kgprId: {
        type: 'string',
        description: 'KGPR ID to review',
      },
      status: {
        type: 'string',
        description: 'Review status',
        enum: ['approved', 'changes_requested', 'commented'],
      },
      body: {
        type: 'string',
        description: 'Review comment',
      },
    },
    required: ['kgprId', 'status'],
  },
  handler: async (args) => {
    try {
      const { kgprId, status, body } = args as {
        kgprId: string;
        status: 'approved' | 'changes_requested' | 'commented';
        body?: string;
      };

      let yataGlobalModule: typeof import('@nahisaho/yata-global') | null = null;

      try {
        yataGlobalModule = await import('@nahisaho/yata-global');
      } catch {
        // Not installed
      }

      if (!yataGlobalModule) {
        return error('YATA Global not installed');
      }

      const { createKGPRManager } = yataGlobalModule;
      const kgprManager = createKGPRManager();

      const review = await kgprManager.submitReview(kgprId, status, body);

      if (!review) {
        return error('Failed to submit review');
      }

      return success({
        action: 'kgpr_reviewed',
        kgprId,
        reviewId: review.id,
        status: review.status,
        message: `Review submitted: ${status}`,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * All KGPR tools
 */
export const kgprTools: ToolDefinition[] = [
  kgprCreateTool,
  kgprDiffTool,
  kgprListTool,
  kgprSubmitTool,
  kgprReviewTool,
];
