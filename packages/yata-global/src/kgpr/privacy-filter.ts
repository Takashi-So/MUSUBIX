/**
 * Knowledge Graph Pull Request (KGPR) - Privacy Filter
 *
 * Removes sensitive information before sharing
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global/kgpr
 *
 * @see REQ-KGPR-002
 */

import type {
  EntityChange,
  RelationshipChange,
  KGPRDiff,
  PrivacyFilterConfig,
} from './types.js';
import {
  DEFAULT_PRIVACY_FILTER_STRICT,
  DEFAULT_PRIVACY_FILTER_MODERATE,
} from './types.js';

export {
  DEFAULT_PRIVACY_FILTER_STRICT,
  DEFAULT_PRIVACY_FILTER_MODERATE,
} from './types.js';

/**
 * Privacy filter for KGPR
 */
export class PrivacyFilter {
  private config: PrivacyFilterConfig;
  private excludeRegexes: RegExp[];

  constructor(config: PrivacyFilterConfig) {
    this.config = config;
    this.excludeRegexes = config.excludePatterns.map(
      (p) => new RegExp(p, 'i')
    );
  }

  /**
   * Filter a complete diff
   */
  filterDiff(diff: KGPRDiff): KGPRDiff {
    return {
      entities: {
        added: this.filterEntityChanges(diff.entities.added),
        updated: this.filterEntityChanges(diff.entities.updated),
        deleted: this.filterEntityChanges(diff.entities.deleted),
      },
      relationships: {
        added: this.filterRelationshipChanges(diff.relationships.added),
        updated: this.filterRelationshipChanges(diff.relationships.updated),
        deleted: this.filterRelationshipChanges(diff.relationships.deleted),
      },
      stats: this.recalculateStats(diff),
    };
  }

  /**
   * Filter entity changes
   */
  private filterEntityChanges(changes: EntityChange[]): EntityChange[] {
    return changes
      .filter((change) => this.shouldIncludeEntity(change))
      .map((change) => this.sanitizeEntity(change));
  }

  /**
   * Filter relationship changes
   */
  private filterRelationshipChanges(
    changes: RelationshipChange[]
  ): RelationshipChange[] {
    return changes
      .filter((change) => this.shouldIncludeRelationship(change))
      .map((change) => this.sanitizeRelationship(change));
  }

  /**
   * Check if entity should be included
   */
  private shouldIncludeEntity(entity: EntityChange): boolean {
    // Check namespace exclusion
    if (this.config.excludeNamespaces.some((ns) =>
      entity.namespace.toLowerCase().includes(ns.toLowerCase())
    )) {
      return false;
    }

    // Check name pattern exclusion
    if (this.excludeRegexes.some((regex) => regex.test(entity.name))) {
      return false;
    }

    return true;
  }

  /**
   * Check if relationship should be included
   */
  private shouldIncludeRelationship(rel: RelationshipChange): boolean {
    // Exclude if either endpoint is in excluded namespace
    const excludedNs = this.config.excludeNamespaces;
    if (
      excludedNs.some(
        (ns) =>
          rel.sourceNamespace.toLowerCase().includes(ns.toLowerCase()) ||
          rel.targetNamespace.toLowerCase().includes(ns.toLowerCase())
      )
    ) {
      return false;
    }

    // Check name pattern exclusion
    if (
      this.excludeRegexes.some(
        (regex) => regex.test(rel.sourceName) || regex.test(rel.targetName)
      )
    ) {
      return false;
    }

    return true;
  }

  /**
   * Sanitize entity data
   */
  private sanitizeEntity(entity: EntityChange): EntityChange {
    const sanitized: EntityChange = {
      ...entity,
    };

    // Remove file path if configured
    if (this.config.removeFilePaths) {
      delete sanitized.filePath;
    }

    // Remove line numbers if configured
    if (this.config.removeLineNumbers) {
      delete sanitized.line;
    }

    // Remove metadata if configured
    if (this.config.removeMetadata) {
      delete sanitized.metadata;
      delete sanitized.previousValue;
    }

    // Apply string replacements
    sanitized.name = this.applyReplacements(sanitized.name);
    sanitized.namespace = this.applyReplacements(sanitized.namespace);

    return sanitized;
  }

  /**
   * Sanitize relationship data
   */
  private sanitizeRelationship(rel: RelationshipChange): RelationshipChange {
    const sanitized: RelationshipChange = {
      ...rel,
    };

    // Remove metadata if configured
    if (this.config.removeMetadata) {
      delete sanitized.metadata;
    }

    // Apply string replacements
    sanitized.sourceName = this.applyReplacements(sanitized.sourceName);
    sanitized.sourceNamespace = this.applyReplacements(sanitized.sourceNamespace);
    sanitized.targetName = this.applyReplacements(sanitized.targetName);
    sanitized.targetNamespace = this.applyReplacements(sanitized.targetNamespace);

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
   * Recalculate stats after filtering
   */
  private recalculateStats(diff: KGPRDiff): KGPRDiff['stats'] {
    const filteredEntitiesAdded = this.filterEntityChanges(diff.entities.added).length;
    const filteredEntitiesUpdated = this.filterEntityChanges(diff.entities.updated).length;
    const filteredEntitiesDeleted = this.filterEntityChanges(diff.entities.deleted).length;
    const filteredRelsAdded = this.filterRelationshipChanges(diff.relationships.added).length;
    const filteredRelsUpdated = this.filterRelationshipChanges(diff.relationships.updated).length;
    const filteredRelsDeleted = this.filterRelationshipChanges(diff.relationships.deleted).length;

    return {
      entitiesAdded: filteredEntitiesAdded,
      entitiesUpdated: filteredEntitiesUpdated,
      entitiesDeleted: filteredEntitiesDeleted,
      relationshipsAdded: filteredRelsAdded,
      relationshipsUpdated: filteredRelsUpdated,
      relationshipsDeleted: filteredRelsDeleted,
      totalChanges:
        filteredEntitiesAdded +
        filteredEntitiesUpdated +
        filteredEntitiesDeleted +
        filteredRelsAdded +
        filteredRelsUpdated +
        filteredRelsDeleted,
    };
  }
}

/**
 * Create privacy filter with preset level
 */
export function createPrivacyFilter(
  level: 'strict' | 'moderate' | 'none',
  customConfig?: Partial<PrivacyFilterConfig>
): PrivacyFilter {
  let baseConfig: PrivacyFilterConfig;

  switch (level) {
    case 'strict':
      baseConfig = { ...DEFAULT_PRIVACY_FILTER_STRICT };
      break;
    case 'moderate':
      baseConfig = { ...DEFAULT_PRIVACY_FILTER_MODERATE };
      break;
    case 'none':
      baseConfig = {
        removeFilePaths: false,
        removeLineNumbers: false,
        removeMetadata: false,
        excludeNamespaces: [],
        excludePatterns: [],
        replacements: [],
      };
      break;
  }

  return new PrivacyFilter({ ...baseConfig, ...customConfig });
}
