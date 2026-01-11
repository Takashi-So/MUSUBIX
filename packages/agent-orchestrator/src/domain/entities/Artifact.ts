/**
 * Artifact Entity
 * 
 * Represents an artifact produced during task execution
 * 
 * @see REQ-SDD-003 - Context Sharing
 */

/**
 * Artifact type
 */
export type ArtifactType = 
  | 'requirement'
  | 'design'
  | 'code'
  | 'test'
  | 'document'
  | 'config';

/**
 * Artifact entity
 */
export interface Artifact {
  /** Unique artifact identifier */
  readonly id: string;
  /** Artifact type */
  readonly type: ArtifactType;
  /** File path (relative to project root) */
  readonly path: string;
  /** Artifact content */
  readonly content: string;
  /** Content hash for change detection */
  readonly contentHash: string;
  /** Producer (task or agent ID) */
  readonly producerId: string;
  /** Created timestamp */
  readonly createdAt: Date;
  /** Traceability IDs */
  readonly traceabilityIds: readonly string[];
}

/**
 * Artifact creation input
 */
export interface CreateArtifactInput {
  id: string;
  type: ArtifactType;
  path: string;
  content: string;
  producerId: string;
  traceabilityIds?: string[];
}

/**
 * Simple hash function for content
 */
function simpleHash(content: string): string {
  let hash = 0;
  for (let i = 0; i < content.length; i++) {
    const char = content.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash; // Convert to 32bit integer
  }
  return Math.abs(hash).toString(16).padStart(8, '0');
}

/**
 * Create an Artifact entity
 * 
 * @param input - Creation input
 * @returns Artifact entity
 */
export function createArtifact(input: CreateArtifactInput): Artifact {
  return Object.freeze({
    id: input.id,
    type: input.type,
    path: input.path,
    content: input.content,
    contentHash: simpleHash(input.content),
    producerId: input.producerId,
    createdAt: new Date(),
    traceabilityIds: Object.freeze([...(input.traceabilityIds ?? [])]),
  });
}

/**
 * Check if artifact has changed
 * 
 * @param artifact - Artifact to check
 * @param newContent - New content to compare
 * @returns true if content has changed
 */
export function hasArtifactChanged(artifact: Artifact, newContent: string): boolean {
  return artifact.contentHash !== simpleHash(newContent);
}

/**
 * Get artifact extension
 * 
 * @param artifact - Artifact
 * @returns File extension
 */
export function getArtifactExtension(artifact: Artifact): string {
  const parts = artifact.path.split('.');
  return parts.length > 1 ? parts[parts.length - 1] : '';
}
