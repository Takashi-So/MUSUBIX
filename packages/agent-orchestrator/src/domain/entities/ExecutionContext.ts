/**
 * ExecutionContext Entity
 * 
 * Context shared between parent task and subagents
 * 
 * @see REQ-SDD-003 - Context Sharing
 * @see DES-SDD-003 - ContextManager
 */

import type { Artifact } from './Artifact.js';

/**
 * Execution context entity
 */
export interface ExecutionContext {
  /** Task ID this context belongs to */
  readonly taskId: string;
  /** Parent context (for hierarchical sharing) */
  readonly parentContext?: ExecutionContext;
  /** Shared knowledge map */
  readonly sharedKnowledge: ReadonlyMap<string, unknown>;
  /** Produced artifacts */
  readonly artifacts: readonly Artifact[];
  /** Context creation timestamp */
  readonly timestamp: Date;
  /** Context metadata */
  readonly metadata: ContextMetadata;
}

/**
 * Context metadata
 */
export interface ContextMetadata {
  /** Source of this context */
  readonly source: 'user' | 'agent' | 'system';
  /** Project path */
  readonly projectPath?: string;
  /** Related file paths */
  readonly relatedFiles: readonly string[];
  /** Tags for categorization */
  readonly tags: readonly string[];
}

/**
 * Context creation input
 */
export interface CreateExecutionContextInput {
  taskId: string;
  parentContext?: ExecutionContext;
  sharedKnowledge?: Map<string, unknown>;
  artifacts?: Artifact[];
  metadata?: Partial<ContextMetadata>;
}

/**
 * Create an ExecutionContext entity
 * 
 * @param input - Creation input
 * @returns ExecutionContext entity
 */
export function createExecutionContext(input: CreateExecutionContextInput): ExecutionContext {
  const defaultMetadata: ContextMetadata = {
    source: 'system',
    relatedFiles: [],
    tags: [],
  };

  return Object.freeze({
    taskId: input.taskId,
    parentContext: input.parentContext,
    sharedKnowledge: new Map(input.sharedKnowledge ?? []),
    artifacts: Object.freeze([...(input.artifacts ?? [])]),
    timestamp: new Date(),
    metadata: Object.freeze({
      ...defaultMetadata,
      ...input.metadata,
      relatedFiles: Object.freeze([...(input.metadata?.relatedFiles ?? [])]),
      tags: Object.freeze([...(input.metadata?.tags ?? [])]),
    }),
  });
}

/**
 * Get value from context (including parent contexts)
 * 
 * @param context - Execution context
 * @param key - Knowledge key
 * @returns Value or undefined
 */
export function getFromContext<T>(context: ExecutionContext, key: string): T | undefined {
  // Check current context
  if (context.sharedKnowledge.has(key)) {
    return context.sharedKnowledge.get(key) as T;
  }
  
  // Check parent context recursively
  if (context.parentContext) {
    return getFromContext<T>(context.parentContext, key);
  }
  
  return undefined;
}

/**
 * Get all artifacts from context (including parent contexts)
 * 
 * @param context - Execution context
 * @returns All artifacts
 */
export function getAllArtifacts(context: ExecutionContext): Artifact[] {
  const artifacts = [...context.artifacts];
  
  if (context.parentContext) {
    artifacts.push(...getAllArtifacts(context.parentContext));
  }
  
  return artifacts;
}

/**
 * Check if context has parent
 * 
 * @param context - Execution context
 * @returns true if has parent
 */
export function hasParentContext(context: ExecutionContext): boolean {
  return context.parentContext !== undefined;
}
