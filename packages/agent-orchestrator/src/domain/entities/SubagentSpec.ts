/**
 * SubagentSpec Entity
 * 
 * Specification for a subagent to execute a decomposed task
 * 
 * @see REQ-SDD-002 - Subagent Decomposition
 * @see DES-SDD-002 - SubagentDispatcher
 */

import type { AgentRole } from '../value-objects/AgentRole.js';
import type { ExecutionContext } from './ExecutionContext.js';

/**
 * Subagent specification entity
 */
export interface SubagentSpec {
  /** Unique specification identifier */
  readonly id: string;
  /** Agent role */
  readonly role: AgentRole;
  /** Prompt to send to subagent */
  readonly prompt: string;
  /** Input context */
  readonly inputContext: ExecutionContext;
  /** Expected output description */
  readonly outputExpectation: string;
  /** Timeout in milliseconds */
  readonly timeoutMs: number;
  /** Dependencies on other subagent specs */
  readonly dependencies: readonly string[];
  /** Created timestamp */
  readonly createdAt: Date;
}

/**
 * Subagent execution result
 */
export interface SubagentResult {
  /** Specification ID */
  readonly specId: string;
  /** Success status */
  readonly success: boolean;
  /** Result content */
  readonly content: string;
  /** Artifacts produced */
  readonly artifacts: readonly SubagentArtifact[];
  /** Execution duration in ms */
  readonly durationMs: number;
  /** Error message if failed */
  readonly error?: string;
  /** Completed timestamp */
  readonly completedAt: Date;
}

/**
 * Artifact produced by subagent
 */
export interface SubagentArtifact {
  /** Artifact type */
  readonly type: 'code' | 'document' | 'test' | 'config';
  /** File path */
  readonly path: string;
  /** Content */
  readonly content: string;
}

/**
 * Subagent spec creation input
 */
export interface CreateSubagentSpecInput {
  id: string;
  role: AgentRole;
  prompt: string;
  inputContext: ExecutionContext;
  outputExpectation: string;
  timeoutMs?: number;
  dependencies?: string[];
}

/**
 * Create a SubagentSpec entity
 * 
 * @param input - Creation input
 * @returns SubagentSpec entity
 */
export function createSubagentSpec(input: CreateSubagentSpecInput): SubagentSpec {
  return Object.freeze({
    id: input.id,
    role: input.role,
    prompt: input.prompt,
    inputContext: input.inputContext,
    outputExpectation: input.outputExpectation,
    timeoutMs: input.timeoutMs ?? 300000, // Default 5 minutes
    dependencies: Object.freeze([...(input.dependencies ?? [])]),
    createdAt: new Date(),
  });
}

/**
 * Create a SubagentResult
 * 
 * @param specId - Specification ID
 * @param success - Success status
 * @param content - Result content
 * @param durationMs - Duration in ms
 * @param artifacts - Produced artifacts
 * @param error - Error message if failed
 * @returns SubagentResult
 */
export function createSubagentResult(
  specId: string,
  success: boolean,
  content: string,
  durationMs: number,
  artifacts: SubagentArtifact[] = [],
  error?: string
): SubagentResult {
  return Object.freeze({
    specId,
    success,
    content,
    artifacts: Object.freeze([...artifacts]),
    durationMs,
    error,
    completedAt: new Date(),
  });
}

/**
 * Check if spec has dependencies
 * 
 * @param spec - Subagent spec
 * @returns true if has dependencies
 */
export function hasDependencies(spec: SubagentSpec): boolean {
  return spec.dependencies.length > 0;
}
