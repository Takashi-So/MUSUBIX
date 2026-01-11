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
 * Knowledge Store-based context store
 * 
 * Note: This is a placeholder. In production, this would integrate
 * with the @musubix/knowledge store.
 * 
 * @deprecated Use createKnowledgeContextStore instead
 */
export function createYATAContextStore(_knowledgeStore?: unknown): IContextStore {
  // Fallback to in-memory store until @musubix/knowledge integration is complete
  const inMemoryStore = createInMemoryContextStore();

  return {
    async save(context: ExecutionContext): Promise<string> {
      // In production, this would persist to @musubix/knowledge:
      // await knowledgeStore.putEntity({
      //   id: `context:${context.taskId}`,
      //   type: 'code',
      //   name: `ExecutionContext-${context.taskId}`,
      //   properties: createContextSnapshot(context),
      //   tags: ['execution-context'],
      // });

      return inMemoryStore.save(context);
    },

    async load(taskId: string): Promise<ExecutionContext | null> {
      // In production, this would load from @musubix/knowledge:
      // const entity = await knowledgeStore.getEntity(`context:${taskId}`);
      // if (!entity) return null;
      // return restoreContextFromSnapshot(entity.properties);

      return inMemoryStore.load(taskId);
    },

    async delete(taskId: string): Promise<boolean> {
      // In production:
      // await knowledgeStore.deleteEntity(`context:${taskId}`);

      return inMemoryStore.delete(taskId);
    },

    async list(): Promise<string[]> {
      // In production:
      // const entities = await knowledgeStore.query({ type: 'code', tags: ['execution-context'] });
      // return entities.map(e => e.id.replace('context:', ''));

      return inMemoryStore.list();
    },
  };
}

/**
 * Knowledge Store-based context store (v3.0.0)
 * 
 * Uses @musubix/knowledge for context persistence
 */
export function createKnowledgeContextStore(_knowledgeStore?: unknown): IContextStore {
  return createYATAContextStore(_knowledgeStore);
}

/**
 * Store factory
 */
export function createContextStoreFactory(
  useKnowledgeStore: boolean = false,
  knowledgeStore?: unknown
): IContextStore {
  if (useKnowledgeStore && knowledgeStore) {
    return createKnowledgeContextStore(knowledgeStore);
  }
  return createInMemoryContextStore();
}
