/**
 * Knowledge Tools - MCP tools for Knowledge Graph management
 * 
 * @packageDocumentation
 * @module tools/knowledge-tools
 */

import { Tool } from '@modelcontextprotocol/sdk/types.js';
import {
  createKnowledgeStore,
  KnowledgeStore,
  Entity,
  Relation,
  EntityType,
  QueryFilter,
  TraverseOptions,
} from '@musubix/knowledge';

// Singleton store instance
let knowledgeStore: KnowledgeStore | null = null;

/**
 * Get or create knowledge store
 */
export function getKnowledgeStore(projectPath?: string): KnowledgeStore {
  if (!knowledgeStore) {
    const path = projectPath || process.cwd();
    knowledgeStore = createKnowledgeStore(`${path}/.knowledge`);
  }
  return knowledgeStore;
}

/**
 * Reset knowledge store (for testing)
 */
export function resetKnowledgeStore(): void {
  knowledgeStore = null;
}

// Tool definitions
export const knowledgePutEntityTool: Tool = {
  name: 'knowledge_put_entity',
  description: 'Add or update an entity in the knowledge graph',
  inputSchema: {
    type: 'object',
    properties: {
      id: { type: 'string', description: 'Entity ID (e.g., REQ-001, DES-001)' },
      type: { 
        type: 'string', 
        enum: ['requirement', 'design', 'task', 'code', 'test', 'pattern', 'custom'],
        description: 'Entity type' 
      },
      name: { type: 'string', description: 'Entity name' },
      description: { type: 'string', description: 'Entity description' },
      properties: { type: 'object', description: 'Additional properties' },
      tags: { type: 'array', items: { type: 'string' }, description: 'Tags' },
    },
    required: ['id', 'type', 'name'],
  },
};

export const knowledgeGetEntityTool: Tool = {
  name: 'knowledge_get_entity',
  description: 'Get an entity from the knowledge graph by ID',
  inputSchema: {
    type: 'object',
    properties: {
      id: { type: 'string', description: 'Entity ID' },
    },
    required: ['id'],
  },
};

export const knowledgeDeleteEntityTool: Tool = {
  name: 'knowledge_delete_entity',
  description: 'Delete an entity from the knowledge graph',
  inputSchema: {
    type: 'object',
    properties: {
      id: { type: 'string', description: 'Entity ID to delete' },
    },
    required: ['id'],
  },
};

export const knowledgeAddRelationTool: Tool = {
  name: 'knowledge_add_relation',
  description: 'Add a relation between two entities',
  inputSchema: {
    type: 'object',
    properties: {
      source: { type: 'string', description: 'Source entity ID' },
      target: { type: 'string', description: 'Target entity ID' },
      type: { 
        type: 'string', 
        enum: ['implements', 'depends_on', 'tests', 'traces_to', 'contains', 'supersedes'],
        description: 'Relation type' 
      },
      properties: { type: 'object', description: 'Additional relation properties' },
    },
    required: ['source', 'target', 'type'],
  },
};

export const knowledgeQueryTool: Tool = {
  name: 'knowledge_query',
  description: 'Query entities from the knowledge graph with filters',
  inputSchema: {
    type: 'object',
    properties: {
      type: { 
        oneOf: [
          { type: 'string' },
          { type: 'array', items: { type: 'string' } }
        ],
        description: 'Filter by entity type(s)' 
      },
      tags: { type: 'array', items: { type: 'string' }, description: 'Filter by tags (AND)' },
      text: { type: 'string', description: 'Full-text search' },
      limit: { type: 'number', description: 'Maximum results' },
      offset: { type: 'number', description: 'Skip first N results' },
    },
    required: [],
  },
};

export const knowledgeTraverseTool: Tool = {
  name: 'knowledge_traverse',
  description: 'Traverse the knowledge graph from a starting entity',
  inputSchema: {
    type: 'object',
    properties: {
      startId: { type: 'string', description: 'Starting entity ID' },
      depth: { type: 'number', description: 'Maximum traversal depth', default: 3 },
      direction: { 
        type: 'string', 
        enum: ['in', 'out', 'both'],
        description: 'Traversal direction',
        default: 'both'
      },
      relationTypes: { 
        type: 'array', 
        items: { type: 'string' },
        description: 'Filter by relation types' 
      },
    },
    required: ['startId'],
  },
};

// Tool handlers
export async function handleKnowledgePutEntity(
  input: { id: string; type: EntityType; name: string; description?: string; properties?: Record<string, unknown>; tags?: string[] }
): Promise<{ success: boolean; entity: Entity }> {
  const store = getKnowledgeStore();
  const now = new Date().toISOString();
  
  const entity: Entity = {
    id: input.id,
    type: input.type,
    name: input.name,
    description: input.description,
    properties: input.properties || {},
    tags: input.tags || [],
    createdAt: now,
    updatedAt: now,
  };
  
  await store.putEntity(entity);
  await store.save();
  
  return { success: true, entity };
}

export async function handleKnowledgeGetEntity(
  input: { id: string }
): Promise<{ entity: Entity | null }> {
  const store = getKnowledgeStore();
  await store.load();
  const entity = await store.getEntity(input.id);
  return { entity: entity || null };
}

export async function handleKnowledgeDeleteEntity(
  input: { id: string }
): Promise<{ success: boolean }> {
  const store = getKnowledgeStore();
  const success = await store.deleteEntity(input.id);
  if (success) {
    await store.save();
  }
  return { success };
}

export async function handleKnowledgeAddRelation(
  input: { source: string; target: string; type: Relation['type']; properties?: Record<string, unknown> }
): Promise<{ success: boolean; relation: Relation }> {
  const store = getKnowledgeStore();
  
  const relation: Relation = {
    id: `${input.source}-${input.type}-${input.target}`,
    source: input.source,
    target: input.target,
    type: input.type,
    properties: input.properties,
  };
  
  await store.addRelation(relation);
  await store.save();
  
  return { success: true, relation };
}

export async function handleKnowledgeQuery(
  input: QueryFilter
): Promise<{ entities: Entity[]; count: number }> {
  const store = getKnowledgeStore();
  await store.load();
  const entities = await store.query(input);
  return { entities, count: entities.length };
}

export async function handleKnowledgeTraverse(
  input: { startId: string; depth?: number; direction?: 'in' | 'out' | 'both'; relationTypes?: string[] }
): Promise<{ entities: Entity[]; count: number }> {
  const store = getKnowledgeStore();
  await store.load();
  
  const options: TraverseOptions = {
    depth: input.depth ?? 3,
    direction: input.direction ?? 'both',
    relationTypes: input.relationTypes as Relation['type'][],
  };
  
  const entities = await store.traverse(input.startId, options);
  return { entities, count: entities.length };
}

// Tool collection
export const knowledgeTools: Tool[] = [
  knowledgePutEntityTool,
  knowledgeGetEntityTool,
  knowledgeDeleteEntityTool,
  knowledgeAddRelationTool,
  knowledgeQueryTool,
  knowledgeTraverseTool,
];

export function getKnowledgeTools(): Tool[] {
  return knowledgeTools;
}

export async function handleKnowledgeTool(
  name: string,
  args: Record<string, unknown>
): Promise<unknown> {
  switch (name) {
    case 'knowledge_put_entity':
      return handleKnowledgePutEntity(args as Parameters<typeof handleKnowledgePutEntity>[0]);
    case 'knowledge_get_entity':
      return handleKnowledgeGetEntity(args as Parameters<typeof handleKnowledgeGetEntity>[0]);
    case 'knowledge_delete_entity':
      return handleKnowledgeDeleteEntity(args as Parameters<typeof handleKnowledgeDeleteEntity>[0]);
    case 'knowledge_add_relation':
      return handleKnowledgeAddRelation(args as Parameters<typeof handleKnowledgeAddRelation>[0]);
    case 'knowledge_query':
      return handleKnowledgeQuery(args as Parameters<typeof handleKnowledgeQuery>[0]);
    case 'knowledge_traverse':
      return handleKnowledgeTraverse(args as Parameters<typeof handleKnowledgeTraverse>[0]);
    default:
      throw new Error(`Unknown knowledge tool: ${name}`);
  }
}
