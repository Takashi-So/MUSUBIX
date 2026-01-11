/**
 * YATAContextStore Infrastructure
 * 
 * Persists execution contexts to YATA knowledge graph
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
 * YATA-based context store
 * 
 * Note: This is a placeholder. In production, this would integrate
 * with the YATA knowledge graph.
 */
export function createYATAContextStore(_yataClient?: unknown): IContextStore {
  // Fallback to in-memory store until YATA integration is complete
  const inMemoryStore = createInMemoryContextStore();

  return {
    async save(context: ExecutionContext): Promise<string> {
      // In production, this would persist to YATA:
      // await yataClient.createEntity({
      //   type: 'ExecutionContext',
      //   id: context.taskId,
      //   properties: createContextSnapshot(context),
      // });

      return inMemoryStore.save(context);
    },

    async load(taskId: string): Promise<ExecutionContext | null> {
      // In production, this would load from YATA:
      // const entity = await yataClient.getEntity('ExecutionContext', taskId);
      // if (!entity) return null;
      // return restoreContextFromSnapshot(entity.properties);

      return inMemoryStore.load(taskId);
    },

    async delete(taskId: string): Promise<boolean> {
      // In production:
      // await yataClient.deleteEntity('ExecutionContext', taskId);

      return inMemoryStore.delete(taskId);
    },

    async list(): Promise<string[]> {
      // In production:
      // const entities = await yataClient.listEntities('ExecutionContext');
      // return entities.map(e => e.id);

      return inMemoryStore.list();
    },
  };
}

/**
 * Store factory
 */
export function createContextStoreFactory(
  useYATA: boolean = false,
  yataClient?: unknown
): IContextStore {
  if (useYATA && yataClient) {
    return createYATAContextStore(yataClient);
  }
  return createInMemoryContextStore();
}
