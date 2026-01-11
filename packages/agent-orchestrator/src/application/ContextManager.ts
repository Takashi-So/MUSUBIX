/**
 * ContextManager Application Service
 * 
 * Manages execution contexts for task sharing
 * 
 * @see REQ-SDD-003 - Context Sharing
 * @see DES-SDD-003 - ContextManager
 */

import {
  type ExecutionContext,
  type CreateExecutionContextInput,
  createExecutionContext,
  getFromContext,
  getAllArtifacts,
} from '../domain/entities/ExecutionContext.js';
import type { Artifact } from '../domain/entities/Artifact.js';

/**
 * Context manager interface
 */
export interface IContextManager {
  /**
   * Create a new execution context
   * @param taskId - Task ID
   * @param parent - Optional parent context
   * @returns New execution context
   */
  create(taskId: string, parent?: ExecutionContext): ExecutionContext;

  /**
   * Share knowledge in context
   * @param context - Context to update
   * @param key - Knowledge key
   * @param value - Knowledge value
   * @returns Updated context (immutable)
   */
  share(context: ExecutionContext, key: string, value: unknown): ExecutionContext;

  /**
   * Add artifact to context
   * @param context - Context to update
   * @param artifact - Artifact to add
   * @returns Updated context (immutable)
   */
  addArtifact(context: ExecutionContext, artifact: Artifact): ExecutionContext;

  /**
   * Merge multiple contexts
   * @param contexts - Contexts to merge
   * @returns Merged context
   */
  merge(contexts: ExecutionContext[]): ExecutionContext;

  /**
   * Get value from context (including parents)
   * @param context - Context to search
   * @param key - Knowledge key
   * @returns Value or undefined
   */
  get<T>(context: ExecutionContext, key: string): T | undefined;

  /**
   * Get all artifacts from context (including parents)
   * @param context - Context to search
   * @returns All artifacts
   */
  getArtifacts(context: ExecutionContext): Artifact[];
}

/**
 * Context manager configuration
 */
export interface ContextManagerConfig {
  /** Default project path */
  defaultProjectPath?: string;
  /** Default source */
  defaultSource?: 'user' | 'agent' | 'system';
}

/**
 * Create a context manager
 * 
 * @param config - Optional configuration
 * @returns IContextManager implementation
 */
export function createContextManager(
  config: ContextManagerConfig = {}
): IContextManager {
  const defaultSource = config.defaultSource ?? 'system';

  return {
    create(taskId: string, parent?: ExecutionContext): ExecutionContext {
      const input: CreateExecutionContextInput = {
        taskId,
        parentContext: parent,
        metadata: {
          source: defaultSource,
          projectPath: config.defaultProjectPath,
          relatedFiles: [],
          tags: [],
        },
      };

      return createExecutionContext(input);
    },

    share(context: ExecutionContext, key: string, value: unknown): ExecutionContext {
      // Create new Map with existing knowledge plus new entry
      const newKnowledge = new Map(context.sharedKnowledge);
      newKnowledge.set(key, value);

      return createExecutionContext({
        taskId: context.taskId,
        parentContext: context.parentContext,
        sharedKnowledge: newKnowledge,
        artifacts: [...context.artifacts],
        metadata: context.metadata,
      });
    },

    addArtifact(context: ExecutionContext, artifact: Artifact): ExecutionContext {
      return createExecutionContext({
        taskId: context.taskId,
        parentContext: context.parentContext,
        sharedKnowledge: new Map(context.sharedKnowledge),
        artifacts: [...context.artifacts, artifact],
        metadata: context.metadata,
      });
    },

    merge(contexts: ExecutionContext[]): ExecutionContext {
      if (contexts.length === 0) {
        throw new Error('Cannot merge empty context array');
      }

      if (contexts.length === 1) {
        return contexts[0];
      }

      // Merge all knowledge
      const mergedKnowledge = new Map<string, unknown>();
      for (const ctx of contexts) {
        for (const [key, value] of ctx.sharedKnowledge) {
          // Later contexts override earlier ones
          mergedKnowledge.set(key, value);
        }
      }

      // Merge all artifacts (deduplicate by ID)
      const artifactMap = new Map<string, Artifact>();
      for (const ctx of contexts) {
        for (const artifact of getAllArtifacts(ctx)) {
          artifactMap.set(artifact.id, artifact);
        }
      }

      // Merge related files
      const relatedFilesSet = new Set<string>();
      for (const ctx of contexts) {
        for (const file of ctx.metadata.relatedFiles) {
          relatedFilesSet.add(file);
        }
      }

      // Merge tags
      const tagsSet = new Set<string>();
      for (const ctx of contexts) {
        for (const tag of ctx.metadata.tags) {
          tagsSet.add(tag);
        }
      }

      // Use first context's taskId as merged ID
      const mergedTaskId = `merged-${contexts.map((c) => c.taskId).join('-')}`;

      return createExecutionContext({
        taskId: mergedTaskId,
        sharedKnowledge: mergedKnowledge,
        artifacts: Array.from(artifactMap.values()),
        metadata: {
          source: 'system',
          projectPath: contexts[0].metadata.projectPath,
          relatedFiles: Array.from(relatedFilesSet),
          tags: Array.from(tagsSet),
        },
      });
    },

    get<T>(context: ExecutionContext, key: string): T | undefined {
      return getFromContext<T>(context, key);
    },

    getArtifacts(context: ExecutionContext): Artifact[] {
      return getAllArtifacts(context);
    },
  };
}

/**
 * Context snapshot for serialization
 */
export interface ContextSnapshot {
  taskId: string;
  knowledge: Record<string, unknown>;
  artifactIds: string[];
  metadata: ExecutionContext['metadata'];
  timestamp: string;
}

/**
 * Create a snapshot of context for persistence
 * 
 * @param context - Context to snapshot
 * @returns Serializable snapshot
 */
export function createContextSnapshot(context: ExecutionContext): ContextSnapshot {
  const knowledge: Record<string, unknown> = {};
  for (const [key, value] of context.sharedKnowledge) {
    knowledge[key] = value;
  }

  return {
    taskId: context.taskId,
    knowledge,
    artifactIds: context.artifacts.map((a) => a.id),
    metadata: context.metadata,
    timestamp: context.timestamp.toISOString(),
  };
}
