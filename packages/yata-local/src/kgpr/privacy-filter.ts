/**
 * YATA Local KGPR - Privacy Filter
 *
 * Removes sensitive information before sharing local knowledge graphs
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/kgpr
 *
 * @see REQ-YL-EXT-KGPR-002
 */

import type {
  LocalEntityChange,
  LocalRelationshipChange,
  LocalKGPRDiff,
  LocalPrivacyFilterConfig,
  LocalDiffStats,
  PrivacyLevel,
} from './types.js';
import {
  DEFAULT_LOCAL_PRIVACY_STRICT,
  DEFAULT_LOCAL_PRIVACY_MODERATE,
  DEFAULT_LOCAL_PRIVACY_NONE,
} from './types.js';

/**
 * Privacy filter for local KGPR
 *
 * @example
 * ```typescript
 * const filter = createLocalPrivacyFilter('strict');
 * const sanitizedDiff = filter.filterDiff(diff);
 * ```
 */
export class LocalPrivacyFilter {
  private config: LocalPrivacyFilterConfig;
  private excludeRegexes: RegExp[];

  constructor(config: LocalPrivacyFilterConfig) {
    this.config = config;
    this.excludeRegexes = config.excludePatterns.map(
      (pattern) => new RegExp(pattern, 'i')
    );
  }

  /**
   * Get the current configuration
   */
  getConfig(): LocalPrivacyFilterConfig {
    return { ...this.config };
  }

  /**
   * Filter a complete diff
   *
   * @param diff - The diff to filter
   * @returns Filtered diff with sensitive data removed
   */
  filterDiff(diff: LocalKGPRDiff): LocalKGPRDiff {
    const filteredEntities = {
      added: this.filterEntityChanges(diff.entities.added),
      updated: this.filterEntityChanges(diff.entities.updated),
      deleted: this.filterEntityChanges(diff.entities.deleted),
    };

    const filteredRelationships = {
      added: this.filterRelationshipChanges(diff.relationships.added),
      updated: this.filterRelationshipChanges(diff.relationships.updated),
      deleted: this.filterRelationshipChanges(diff.relationships.deleted),
    };

    return {
      entities: filteredEntities,
      relationships: filteredRelationships,
      stats: this.calculateStats(filteredEntities, filteredRelationships),
    };
  }

  /**
   * Filter entity changes
   */
  filterEntityChanges(changes: LocalEntityChange[]): LocalEntityChange[] {
    return changes
      .filter((change) => this.shouldIncludeEntity(change))
      .map((change) => this.sanitizeEntity(change));
  }

  /**
   * Filter relationship changes
   */
  filterRelationshipChanges(changes: LocalRelationshipChange[]): LocalRelationshipChange[] {
    return changes
      .filter((change) => this.shouldIncludeRelationship(change))
      .map((change) => this.sanitizeRelationship(change));
  }

  /**
   * Check if an entity should be included
   */
  shouldIncludeEntity(entity: LocalEntityChange): boolean {
    // Check namespace exclusion
    if (this.isNamespaceExcluded(entity.namespace)) {
      return false;
    }

    // Check name pattern exclusion
    if (this.isNameExcluded(entity.name)) {
      return false;
    }

    // Check file path exclusion
    if (entity.filePath && this.isPathExcluded(entity.filePath)) {
      return false;
    }

    return true;
  }

  /**
   * Check if a relationship should be included
   */
  shouldIncludeRelationship(rel: LocalRelationshipChange): boolean {
    // Exclude if either endpoint is in excluded namespace
    if (this.isNamespaceExcluded(rel.sourceNamespace) || this.isNamespaceExcluded(rel.targetNamespace)) {
      return false;
    }

    // Check name pattern exclusion for both endpoints
    if (this.isNameExcluded(rel.sourceName) || this.isNameExcluded(rel.targetName)) {
      return false;
    }

    return true;
  }

  /**
   * Sanitize an entity change
   */
  private sanitizeEntity(entity: LocalEntityChange): LocalEntityChange {
    const sanitized: LocalEntityChange = {
      changeType: entity.changeType,
      localId: entity.localId,
      name: this.applyReplacements(entity.name),
      entityType: entity.entityType,
      namespace: this.applyReplacements(entity.namespace),
    };

    // Conditionally include file path
    if (!this.config.removeFilePaths && entity.filePath) {
      sanitized.filePath = this.sanitizePath(entity.filePath);
    }

    // Conditionally include line number
    if (!this.config.removeLineNumbers && entity.line !== undefined) {
      sanitized.line = entity.line;
    }

    // Conditionally include metadata
    if (!this.config.removeMetadata && entity.metadata) {
      sanitized.metadata = this.sanitizeMetadata(entity.metadata);
    }

    return sanitized;
  }

  /**
   * Sanitize a relationship change
   */
  private sanitizeRelationship(rel: LocalRelationshipChange): LocalRelationshipChange {
    const sanitized: LocalRelationshipChange = {
      changeType: rel.changeType,
      sourceName: this.applyReplacements(rel.sourceName),
      sourceNamespace: this.applyReplacements(rel.sourceNamespace),
      targetName: this.applyReplacements(rel.targetName),
      targetNamespace: this.applyReplacements(rel.targetNamespace),
      relationshipType: rel.relationshipType,
    };

    if (rel.localId) {
      sanitized.localId = rel.localId;
    }

    // Conditionally include metadata
    if (!this.config.removeMetadata && rel.metadata) {
      sanitized.metadata = this.sanitizeMetadata(rel.metadata);
    }

    return sanitized;
  }

  /**
   * Check if a namespace should be excluded
   */
  private isNamespaceExcluded(namespace: string): boolean {
    const lowerNs = namespace.toLowerCase();
    return this.config.excludeNamespaces.some(
      (excluded) => lowerNs.includes(excluded.toLowerCase())
    );
  }

  /**
   * Check if a name should be excluded
   */
  private isNameExcluded(name: string): boolean {
    return this.excludeRegexes.some((regex) => regex.test(name));
  }

  /**
   * Check if a file path should be excluded
   */
  private isPathExcluded(filePath: string): boolean {
    const lowerPath = filePath.toLowerCase();
    return this.config.excludeNamespaces.some(
      (excluded) => lowerPath.includes(excluded.toLowerCase())
    );
  }

  /**
   * Sanitize a file path
   */
  private sanitizePath(filePath: string): string {
    // Apply replacements to path
    return this.applyReplacements(filePath);
  }

  /**
   * Sanitize metadata object
   */
  private sanitizeMetadata(metadata: Record<string, unknown>): Record<string, unknown> {
    const sanitized: Record<string, unknown> = {};

    for (const [key, value] of Object.entries(metadata)) {
      // Skip keys that match exclude patterns
      if (this.isNameExcluded(key)) {
        continue;
      }

      // Sanitize string values
      if (typeof value === 'string') {
        sanitized[key] = this.applyReplacements(value);
      } else if (typeof value === 'object' && value !== null) {
        // Recursively sanitize nested objects
        sanitized[key] = this.sanitizeMetadata(value as Record<string, unknown>);
      } else {
        sanitized[key] = value;
      }
    }

    return sanitized;
  }

  /**
   * Apply configured string replacements
   */
  private applyReplacements(str: string): string {
    let result = str;
    for (const { pattern, replacement } of this.config.replacements) {
      result = result.replace(new RegExp(pattern, 'gi'), replacement);
    }
    return result;
  }

  /**
   * Calculate stats from filtered changes
   */
  private calculateStats(
    entities: LocalKGPRDiff['entities'],
    relationships: LocalKGPRDiff['relationships']
  ): LocalDiffStats {
    const entitiesAdded = entities.added.length;
    const entitiesUpdated = entities.updated.length;
    const entitiesDeleted = entities.deleted.length;
    const relationshipsAdded = relationships.added.length;
    const relationshipsUpdated = relationships.updated.length;
    const relationshipsDeleted = relationships.deleted.length;

    return {
      entitiesAdded,
      entitiesUpdated,
      entitiesDeleted,
      relationshipsAdded,
      relationshipsUpdated,
      relationshipsDeleted,
      totalChanges:
        entitiesAdded +
        entitiesUpdated +
        entitiesDeleted +
        relationshipsAdded +
        relationshipsUpdated +
        relationshipsDeleted,
    };
  }
}

/**
 * Create a privacy filter with a preset level
 *
 * @param level - Privacy level preset
 * @param customConfig - Custom configuration to merge with preset
 * @returns Configured privacy filter
 *
 * @example
 * ```typescript
 * // Use strict preset
 * const strictFilter = createLocalPrivacyFilter('strict');
 *
 * // Use moderate with custom exclusions
 * const customFilter = createLocalPrivacyFilter('moderate', {
 *   excludePatterns: [...DEFAULT_LOCAL_PRIVACY_MODERATE.excludePatterns, 'my_secret'],
 * });
 * ```
 */
export function createLocalPrivacyFilter(
  level: PrivacyLevel,
  customConfig?: Partial<LocalPrivacyFilterConfig>
): LocalPrivacyFilter {
  let baseConfig: LocalPrivacyFilterConfig;

  switch (level) {
    case 'strict':
      baseConfig = { ...DEFAULT_LOCAL_PRIVACY_STRICT };
      break;
    case 'moderate':
      baseConfig = { ...DEFAULT_LOCAL_PRIVACY_MODERATE };
      break;
    case 'none':
      baseConfig = { ...DEFAULT_LOCAL_PRIVACY_NONE };
      break;
    default:
      baseConfig = { ...DEFAULT_LOCAL_PRIVACY_MODERATE };
  }

  // Merge custom config if provided
  if (customConfig) {
    return new LocalPrivacyFilter({
      ...baseConfig,
      ...customConfig,
      // Merge arrays instead of replacing
      excludeNamespaces: [
        ...baseConfig.excludeNamespaces,
        ...(customConfig.excludeNamespaces || []),
      ],
      excludePatterns: [
        ...baseConfig.excludePatterns,
        ...(customConfig.excludePatterns || []),
      ],
      replacements: [
        ...baseConfig.replacements,
        ...(customConfig.replacements || []),
      ],
    });
  }

  return new LocalPrivacyFilter(baseConfig);
}

// Re-export default configs
export {
  DEFAULT_LOCAL_PRIVACY_STRICT,
  DEFAULT_LOCAL_PRIVACY_MODERATE,
  DEFAULT_LOCAL_PRIVACY_NONE,
} from './types.js';
