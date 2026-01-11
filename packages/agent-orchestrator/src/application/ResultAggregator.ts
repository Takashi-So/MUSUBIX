/**
 * ResultAggregator Application Service
 * 
 * Aggregates results from multiple subagents
 * 
 * @see REQ-PAD-003 - Result Aggregation
 * @see DES-PAD-003 - ResultAggregator
 */

import type { SubagentResult, SubagentArtifact } from '../domain/entities/SubagentSpec.js';

/**
 * Conflict detection result
 */
export interface ConflictInfo {
  /** Conflicting spec IDs */
  readonly specIds: readonly string[];
  /** Conflicting file path */
  readonly filePath: string;
  /** Conflict type */
  readonly type: 'file' | 'content' | 'semantic';
  /** Description */
  readonly description: string;
  /** Can be auto-resolved */
  readonly autoResolvable: boolean;
}

/**
 * Aggregated output
 */
export interface AggregatedOutput {
  /** All results */
  readonly results: readonly SubagentResult[];
  /** Overall success */
  readonly success: boolean;
  /** Combined content */
  readonly combinedContent: string;
  /** All artifacts (deduplicated) */
  readonly artifacts: readonly SubagentArtifact[];
  /** Detected conflicts */
  readonly conflicts: readonly ConflictInfo[];
  /** Failed results */
  readonly failures: readonly SubagentResult[];
  /** Statistics */
  readonly stats: AggregationStats;
}

/**
 * Aggregation statistics
 */
export interface AggregationStats {
  readonly totalSpecs: number;
  readonly succeeded: number;
  readonly failed: number;
  readonly totalDurationMs: number;
  readonly averageDurationMs: number;
  readonly artifactCount: number;
  readonly conflictCount: number;
}

/**
 * Result aggregator interface
 */
export interface IResultAggregator {
  /**
   * Aggregate results from multiple subagents
   * @param results - Subagent results
   * @returns Aggregated output
   */
  aggregate(results: SubagentResult[]): AggregatedOutput;

  /**
   * Detect conflicts between results
   * @param results - Subagent results
   * @returns Detected conflicts
   */
  detectConflicts(results: SubagentResult[]): ConflictInfo[];

  /**
   * Merge artifacts from results
   * @param results - Subagent results
   * @returns Merged artifacts
   */
  mergeArtifacts(results: SubagentResult[]): SubagentArtifact[];
}

/**
 * Aggregator configuration
 */
export interface ResultAggregatorConfig {
  /** Enable conflict detection (default: true) */
  detectConflicts?: boolean;
  /** Content separator for combining */
  contentSeparator?: string;
}

/**
 * Create a result aggregator
 * 
 * @param config - Optional configuration
 * @returns IResultAggregator implementation
 */
export function createResultAggregator(
  config: ResultAggregatorConfig = {}
): IResultAggregator {
  const enableConflictDetection = config.detectConflicts ?? true;
  const contentSeparator = config.contentSeparator ?? '\n\n---\n\n';

  /**
   * Detect file conflicts
   */
  function detectFileConflicts(results: SubagentResult[]): ConflictInfo[] {
    const conflicts: ConflictInfo[] = [];
    const fileMap = new Map<string, { specId: string; content: string }[]>();

    // Group artifacts by file path
    for (const result of results) {
      if (!result.success) continue;

      for (const artifact of result.artifacts) {
        const existing = fileMap.get(artifact.path) ?? [];
        existing.push({ specId: result.specId, content: artifact.content });
        fileMap.set(artifact.path, existing);
      }
    }

    // Check for conflicts
    for (const [path, entries] of fileMap) {
      if (entries.length > 1) {
        // Check if contents differ
        const contents = new Set(entries.map((e) => e.content));
        if (contents.size > 1) {
          conflicts.push({
            specIds: entries.map((e) => e.specId),
            filePath: path,
            type: 'file',
            description: `Multiple specs produced different content for ${path}`,
            autoResolvable: false,
          });
        }
      }
    }

    return conflicts;
  }

  /**
   * Combine content from results
   */
  function combineContent(results: SubagentResult[]): string {
    return results
      .filter((r) => r.success && r.content)
      .map((r) => `## ${r.specId}\n\n${r.content}`)
      .join(contentSeparator);
  }

  /**
   * Calculate statistics
   */
  function calculateStats(
    results: SubagentResult[],
    artifacts: SubagentArtifact[],
    conflicts: ConflictInfo[]
  ): AggregationStats {
    const succeeded = results.filter((r) => r.success).length;
    const failed = results.length - succeeded;
    const totalDurationMs = results.reduce((sum, r) => sum + r.durationMs, 0);
    const averageDurationMs =
      results.length > 0 ? Math.round(totalDurationMs / results.length) : 0;

    return {
      totalSpecs: results.length,
      succeeded,
      failed,
      totalDurationMs,
      averageDurationMs,
      artifactCount: artifacts.length,
      conflictCount: conflicts.length,
    };
  }

  return {
    aggregate(results: SubagentResult[]): AggregatedOutput {
      const failures = results.filter((r) => !r.success);
      const success = failures.length === 0;
      const combinedContent = combineContent(results);
      const artifacts = this.mergeArtifacts(results);
      const conflicts = enableConflictDetection
        ? this.detectConflicts(results)
        : [];
      const stats = calculateStats(results, artifacts, conflicts);

      return Object.freeze({
        results: Object.freeze([...results]),
        success: success && conflicts.length === 0,
        combinedContent,
        artifacts: Object.freeze(artifacts),
        conflicts: Object.freeze(conflicts),
        failures: Object.freeze(failures),
        stats: Object.freeze(stats),
      });
    },

    detectConflicts(results: SubagentResult[]): ConflictInfo[] {
      return detectFileConflicts(results);
    },

    mergeArtifacts(results: SubagentResult[]): SubagentArtifact[] {
      const artifactMap = new Map<string, SubagentArtifact>();

      for (const result of results) {
        if (!result.success) continue;

        for (const artifact of result.artifacts) {
          // Use path as key, later results override earlier ones
          artifactMap.set(artifact.path, artifact);
        }
      }

      return Array.from(artifactMap.values());
    },
  };
}

/**
 * Create a conflict resolution strategy
 */
export type ConflictResolver = (
  conflict: ConflictInfo,
  artifacts: SubagentArtifact[]
) => SubagentArtifact | null;

/**
 * Default conflict resolver - use latest artifact
 */
export const latestArtifactResolver: ConflictResolver = (conflict, artifacts) => {
  const conflicting = artifacts.filter((a) => a.path === conflict.filePath);
  return conflicting.length > 0 ? conflicting[conflicting.length - 1] : null;
};

/**
 * Merge resolver - attempt to merge content
 */
export const mergeResolver: ConflictResolver = (conflict, artifacts) => {
  if (conflict.type !== 'file') {
    return latestArtifactResolver(conflict, artifacts);
  }

  const conflicting = artifacts.filter((a) => a.path === conflict.filePath);
  if (conflicting.length === 0) return null;

  // Simple merge: concatenate with markers
  const mergedContent = conflicting
    .map((a) => `// === From spec ===\n${a.content}`)
    .join('\n\n');

  return {
    ...conflicting[0],
    content: mergedContent,
  };
};
