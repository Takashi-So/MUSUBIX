/**
 * KnowledgeContextStore Infrastructure
 * 
 * Persists execution contexts to @musubix/knowledge store
 * 
 * @see REQ-SDD-003 - Context Sharing
 */

import type { ExecutionContext } from '../domain/entities/ExecutionContext.js';
import { createExecutionContext } from '../domain/entities/ExecutionContext.js';
import type { ContextSnapshot } from '../application/ContextManager.js';
import { createContextSnapshot } from '../application/ContextManager.js';

/**
 * Context store interface
 */
export interface IContextStore {
  /**
   * Save context
   * @param context - Context to save
   * @returns Context ID
   */
  save(context: ExecutionContext): Promise<string>;

  /**
   * Load context by task ID
   * @param taskId - Task ID
   * @returns Context or null
   */
  load(taskId: string): Promise<ExecutionContext | null>;

  /**
   * Delete context
   * @param taskId - Task ID
   * @returns true if deleted
   */
  delete(taskId: string): Promise<boolean>;

  /**
   * List all context IDs
   * @returns Context task IDs
   */
  list(): Promise<string[]>;
}

/**
 * Knowledge store adapter interface
 * Compatible with @musubix/knowledge KnowledgeStore
 */
export interface IKnowledgeStoreAdapter {
  putEntity(entity: {
    id: string;
    type: string;
    name: string;
    properties: Record<string, unknown>;
    tags: string[];
  }): Promise<void>;

  getEntity(id: string): Promise<{
    id: string;
    type: string;
    name: string;
    properties: Record<string, unknown>;
    tags: string[];
  } | null>;

  deleteEntity(id: string): Promise<boolean>;

  query(filter: { type?: string; tags?: string[] }): Promise<Array<{
    id: string;
    type: string;
    name: string;
    properties: Record<string, unknown>;
    tags: string[];
  }>>;
}

/**
 * In-memory context store (for testing)
 */
export function createInMemoryContextStore(): IContextStore {
  const store = new Map<string, ContextSnapshot>();

  return {
    async save(context: ExecutionContext): Promise<string> {
      const snapshot = createContextSnapshot(context);
      store.set(context.taskId, snapshot);
      return context.taskId;
    },

    async load(taskId: string): Promise<ExecutionContext | null> {
      const snapshot = store.get(taskId);
      if (!snapshot) return null;

      return createExecutionContext({
        taskId: snapshot.taskId,
        sharedKnowledge: new Map(Object.entries(snapshot.knowledge)),
        metadata: snapshot.metadata,
      });
    },

    async delete(taskId: string): Promise<boolean> {
      return store.delete(taskId);
    },

    async list(): Promise<string[]> {
      return Array.from(store.keys());
    },
  };
}

/**
 * Knowledge Store-based context store (v3.0.0)
 * 
 * Uses @musubix/knowledge for context persistence
 */
export function createKnowledgeContextStore(knowledgeStore: IKnowledgeStoreAdapter): IContextStore {
  const ENTITY_TYPE = 'code';
  const CONTEXT_TAG = 'execution-context';

  return {
    async save(context: ExecutionContext): Promise<string> {
      const snapshot = createContextSnapshot(context);
      const entityId = `context:${context.taskId}`;

      await knowledgeStore.putEntity({
        id: entityId,
        type: ENTITY_TYPE,
        name: `ExecutionContext-${context.taskId}`,
        properties: snapshot as unknown as Record<string, unknown>,
        tags: [CONTEXT_TAG],
      });

      return context.taskId;
    },

    async load(taskId: string): Promise<ExecutionContext | null> {
      const entityId = `context:${taskId}`;
      const entity = await knowledgeStore.getEntity(entityId);

      if (!entity) return null;

      const snapshot = entity.properties as unknown as ContextSnapshot;

      return createExecutionContext({
        taskId: snapshot.taskId,
        sharedKnowledge: new Map(Object.entries(snapshot.knowledge)),
        metadata: snapshot.metadata,
      });
    },

    async delete(taskId: string): Promise<boolean> {
      const entityId = `context:${taskId}`;
      return knowledgeStore.deleteEntity(entityId);
    },

    async list(): Promise<string[]> {
      const entities = await knowledgeStore.query({
        type: ENTITY_TYPE,
        tags: [CONTEXT_TAG],
      });

      return entities.map(e => e.id.replace('context:', ''));
    },
  };
}

/**
 * Store factory
 * 
 * @param knowledgeStore - Optional knowledge store adapter. If provided, uses persistent storage.
 * @returns Context store instance
 */
export function createContextStoreFactory(
  knowledgeStore?: IKnowledgeStoreAdapter
): IContextStore {
  if (knowledgeStore) {
    return createKnowledgeContextStore(knowledgeStore);
  }
  return createInMemoryContextStore();
}
