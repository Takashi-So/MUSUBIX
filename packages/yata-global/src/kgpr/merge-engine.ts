/**
 * Knowledge Graph Pull Request (KGPR) - Merge Engine
 *
 * Handles conflict detection, diff application, and merge audit logging
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global/kgpr
 *
 * @see REQ-KGPR-004
 * @see TSK-KGPR-006
 */

import { EventEmitter } from 'events';
import type {
  KGPR,
  KGPRDiff,
  EntityChange,
  RelationshipChange,
} from './types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Conflict type
 */
export type ConflictType =
  | 'entity_exists'        // Entity with same name/namespace already exists
  | 'entity_modified'      // Entity was modified since KGPR creation
  | 'entity_deleted'       // Entity was deleted since KGPR creation
  | 'relationship_exists'  // Relationship already exists
  | 'relationship_broken'  // Source or target entity doesn't exist
  | 'circular_dependency'  // Would create circular dependency
  | 'schema_violation';    // Violates global KG schema

/**
 * Conflict severity
 */
export type ConflictSeverity = 'error' | 'warning' | 'info';

/**
 * Merge conflict
 */
export interface MergeConflict {
  /** Conflict ID */
  id: string;
  /** Conflict type */
  type: ConflictType;
  /** Severity */
  severity: ConflictSeverity;
  /** Human-readable message */
  message: string;
  /** Local entity/relationship ID */
  localId: string;
  /** Global entity/relationship ID (if exists) */
  globalId?: string;
  /** Entity/relationship name */
  name: string;
  /** Namespace */
  namespace: string;
  /** Whether this is an entity or relationship */
  itemType: 'entity' | 'relationship';
  /** Local value */
  localValue?: Record<string, unknown>;
  /** Global value */
  globalValue?: Record<string, unknown>;
  /** Suggested resolution */
  suggestedResolution?: ConflictResolution;
}

/**
 * Conflict resolution strategy
 */
export type ConflictResolution =
  | 'use_local'    // Use local (KGPR) value
  | 'use_global'   // Keep global value
  | 'merge'        // Merge both values
  | 'skip'         // Skip this change
  | 'rename';      // Rename to avoid conflict

/**
 * Merge options
 */
export interface MergeOptions {
  /** How to handle conflicts */
  conflictStrategy?: 'fail' | 'skip_conflicts' | 'force';
  /** Custom conflict resolutions by ID */
  resolutions?: Map<string, ConflictResolution>;
  /** Dry run (don't actually apply) */
  dryRun?: boolean;
  /** Merger user ID */
  mergerId?: string;
  /** Merger user name */
  mergerName?: string;
}

/**
 * Merge result
 */
export interface MergeResult {
  /** Whether merge was successful */
  success: boolean;
  /** KGPR ID */
  kgprId: string;
  /** Conflicts found */
  conflicts: MergeConflict[];
  /** Applied changes */
  applied: {
    entitiesAdded: number;
    entitiesUpdated: number;
    entitiesDeleted: number;
    relationshipsAdded: number;
    relationshipsUpdated: number;
    relationshipsDeleted: number;
  };
  /** Skipped changes */
  skipped: {
    entities: string[];
    relationships: string[];
  };
  /** Audit log entry */
  auditLog: MergeAuditLog;
  /** Error message (if failed) */
  error?: string;
}

/**
 * Merge audit log entry
 */
export interface MergeAuditLog {
  /** Log ID */
  id: string;
  /** KGPR ID */
  kgprId: string;
  /** KGPR title */
  kgprTitle: string;
  /** KGPR author */
  kgprAuthor: string;
  /** Merger ID */
  mergerId: string;
  /** Merger name */
  mergerName: string;
  /** Operation type */
  operation: 'merge' | 'dry_run' | 'conflict_check';
  /** Result */
  result: 'success' | 'failed' | 'partial';
  /** Timestamp */
  timestamp: Date;
  /** Changes applied */
  changes: {
    entitiesAdded: EntityChange[];
    entitiesUpdated: EntityChange[];
    entitiesDeleted: EntityChange[];
    relationshipsAdded: RelationshipChange[];
    relationshipsUpdated: RelationshipChange[];
    relationshipsDeleted: RelationshipChange[];
  };
  /** Conflicts */
  conflicts: MergeConflict[];
  /** Resolutions applied */
  resolutions: Array<{ conflictId: string; resolution: ConflictResolution }>;
  /** Duration (ms) */
  durationMs: number;
}

/**
 * Global Knowledge Graph interface (for reading/writing to global KG)
 */
export interface GlobalKnowledgeGraph {
  /** Check if entity exists */
  entityExists(name: string, namespace: string): Promise<boolean>;
  
  /** Get entity by name and namespace */
  getEntity(name: string, namespace: string): Promise<{
    id: string;
    name: string;
    type: string;
    namespace: string;
    version?: number;
    metadata?: Record<string, unknown>;
    updatedAt: Date;
  } | null>;
  
  /** Check if relationship exists */
  relationshipExists(
    sourceName: string,
    sourceNamespace: string,
    targetName: string,
    targetNamespace: string,
    type: string
  ): Promise<boolean>;
  
  /** Add entity */
  addEntity(entity: {
    name: string;
    type: string;
    namespace: string;
    metadata?: Record<string, unknown>;
  }): Promise<string>;
  
  /** Update entity */
  updateEntity(
    name: string,
    namespace: string,
    updates: Record<string, unknown>
  ): Promise<void>;
  
  /** Delete entity */
  deleteEntity(name: string, namespace: string): Promise<void>;
  
  /** Add relationship */
  addRelationship(rel: {
    sourceName: string;
    sourceNamespace: string;
    targetName: string;
    targetNamespace: string;
    type: string;
    metadata?: Record<string, unknown>;
  }): Promise<string>;
  
  /** Delete relationship */
  deleteRelationship(
    sourceName: string,
    sourceNamespace: string,
    targetName: string,
    targetNamespace: string,
    type: string
  ): Promise<void>;
  
  /** Check for circular dependencies */
  wouldCreateCycle?(
    sourceName: string,
    sourceNamespace: string,
    targetName: string,
    targetNamespace: string,
    relationshipType: string
  ): Promise<boolean>;
}

// ============================================================================
// Merge Engine
// ============================================================================

/**
 * MergeEngine events
 */
export interface MergeEngineEvents {
  'merge:started': { kgprId: string };
  'merge:conflict': { conflict: MergeConflict };
  'merge:progress': { phase: string; progress: number; total: number };
  'merge:completed': { result: MergeResult };
  'merge:failed': { kgprId: string; error: string };
  'error': Error;
}

/**
 * Merge Engine
 *
 * Handles conflict detection, diff application, and merge audit logging
 *
 * @example
 * ```typescript
 * const engine = new MergeEngine({ globalKG });
 * const conflicts = await engine.checkConflicts(kgpr.diff);
 * if (conflicts.length === 0) {
 *   const result = await engine.merge(kgpr);
 * }
 * ```
 */
export class MergeEngine extends EventEmitter {
  private globalKG: GlobalKnowledgeGraph | null = null;
  private auditLogs: MergeAuditLog[] = [];
  private conflictIdCounter = 0;

  constructor(options: {
    globalKG?: GlobalKnowledgeGraph;
  } = {}) {
    super();
    this.globalKG = options.globalKG ?? null;
  }

  /**
   * Connect to global knowledge graph
   */
  connectGlobalKG(globalKG: GlobalKnowledgeGraph): void {
    this.globalKG = globalKG;
  }

  /**
   * Generate unique conflict ID
   */
  private generateConflictId(): string {
    return `CONFLICT-${++this.conflictIdCounter}`;
  }

  /**
   * Generate unique audit log ID
   */
  private generateAuditLogId(): string {
    const timestamp = Date.now().toString(36);
    const random = Math.random().toString(36).substring(2, 6);
    return `AUDIT-${timestamp}-${random}`;
  }

  // ============================================================================
  // Conflict Detection
  // ============================================================================

  /**
   * Check for conflicts in a diff
   */
  async checkConflicts(diff: KGPRDiff): Promise<MergeConflict[]> {
    const conflicts: MergeConflict[] = [];

    if (!this.globalKG) {
      // No global KG connected, no conflicts possible
      return conflicts;
    }

    // Check entity additions
    for (const entity of diff.entities.added) {
      const existing = await this.globalKG.getEntity(entity.name, entity.namespace);
      if (existing) {
        conflicts.push({
          id: this.generateConflictId(),
          type: 'entity_exists',
          severity: 'error',
          message: `Entity '${entity.name}' already exists in namespace '${entity.namespace}'`,
          localId: entity.localId,
          globalId: existing.id,
          name: entity.name,
          namespace: entity.namespace,
          itemType: 'entity',
          localValue: entity.metadata,
          globalValue: existing.metadata,
          suggestedResolution: 'rename',
        });
      }
    }

    // Check entity updates
    for (const entity of diff.entities.updated) {
      const existing = await this.globalKG.getEntity(entity.name, entity.namespace);
      if (!existing) {
        conflicts.push({
          id: this.generateConflictId(),
          type: 'entity_deleted',
          severity: 'error',
          message: `Entity '${entity.name}' no longer exists in namespace '${entity.namespace}'`,
          localId: entity.localId,
          name: entity.name,
          namespace: entity.namespace,
          itemType: 'entity',
          localValue: entity.metadata,
          suggestedResolution: 'skip',
        });
      }
    }

    // Check entity deletions
    for (const entity of diff.entities.deleted) {
      const existing = await this.globalKG.getEntity(entity.name, entity.namespace);
      if (!existing) {
        conflicts.push({
          id: this.generateConflictId(),
          type: 'entity_deleted',
          severity: 'warning',
          message: `Entity '${entity.name}' was already deleted from namespace '${entity.namespace}'`,
          localId: entity.localId,
          name: entity.name,
          namespace: entity.namespace,
          itemType: 'entity',
          suggestedResolution: 'skip',
        });
      }
    }

    // Check relationship additions
    for (const rel of diff.relationships.added) {
      // Check if relationship already exists
      const exists = await this.globalKG.relationshipExists(
        rel.sourceName,
        rel.sourceNamespace,
        rel.targetName,
        rel.targetNamespace,
        rel.relationshipType
      );

      if (exists) {
        conflicts.push({
          id: this.generateConflictId(),
          type: 'relationship_exists',
          severity: 'warning',
          message: `Relationship '${rel.sourceName} --[${rel.relationshipType}]--> ${rel.targetName}' already exists`,
          localId: rel.localId ?? `${rel.sourceName}-${rel.targetName}`,
          name: `${rel.sourceName} -> ${rel.targetName}`,
          namespace: rel.sourceNamespace,
          itemType: 'relationship',
          localValue: rel.metadata,
          suggestedResolution: 'skip',
        });
      }

      // Check if source entity exists
      const sourceExists = await this.globalKG.entityExists(rel.sourceName, rel.sourceNamespace);
      if (!sourceExists) {
        conflicts.push({
          id: this.generateConflictId(),
          type: 'relationship_broken',
          severity: 'error',
          message: `Source entity '${rel.sourceName}' does not exist in namespace '${rel.sourceNamespace}'`,
          localId: rel.localId ?? `${rel.sourceName}-${rel.targetName}`,
          name: rel.sourceName,
          namespace: rel.sourceNamespace,
          itemType: 'relationship',
          suggestedResolution: 'skip',
        });
      }

      // Check if target entity exists
      const targetExists = await this.globalKG.entityExists(rel.targetName, rel.targetNamespace);
      if (!targetExists) {
        conflicts.push({
          id: this.generateConflictId(),
          type: 'relationship_broken',
          severity: 'error',
          message: `Target entity '${rel.targetName}' does not exist in namespace '${rel.targetNamespace}'`,
          localId: rel.localId ?? `${rel.sourceName}-${rel.targetName}`,
          name: rel.targetName,
          namespace: rel.targetNamespace,
          itemType: 'relationship',
          suggestedResolution: 'skip',
        });
      }

      // Check for circular dependencies
      if (this.globalKG.wouldCreateCycle) {
        const wouldCycle = await this.globalKG.wouldCreateCycle(
          rel.sourceName,
          rel.sourceNamespace,
          rel.targetName,
          rel.targetNamespace,
          rel.relationshipType
        );

        if (wouldCycle) {
          conflicts.push({
            id: this.generateConflictId(),
            type: 'circular_dependency',
            severity: 'error',
            message: `Adding relationship would create circular dependency: ${rel.sourceName} -> ${rel.targetName}`,
            localId: rel.localId ?? `${rel.sourceName}-${rel.targetName}`,
            name: `${rel.sourceName} -> ${rel.targetName}`,
            namespace: rel.sourceNamespace,
            itemType: 'relationship',
            suggestedResolution: 'skip',
          });
        }
      }
    }

    // Emit conflict events
    for (const conflict of conflicts) {
      this.emit('merge:conflict', { conflict });
    }

    return conflicts;
  }

  // ============================================================================
  // Merge Operations
  // ============================================================================

  /**
   * Merge a KGPR into the global knowledge graph
   */
  async merge(kgpr: KGPR, options: MergeOptions = {}): Promise<MergeResult> {
    const startTime = Date.now();
    const {
      conflictStrategy = 'fail',
      resolutions = new Map(),
      dryRun = false,
      mergerId = 'system',
      mergerName = 'System',
    } = options;

    this.emit('merge:started', { kgprId: kgpr.id });

    // Check conflicts
    this.emit('merge:progress', { phase: 'conflict_check', progress: 0, total: 1 });
    const conflicts = await this.checkConflicts(kgpr.diff);
    this.emit('merge:progress', { phase: 'conflict_check', progress: 1, total: 1 });

    // Handle conflicts based on strategy
    const errorConflicts = conflicts.filter((c) => c.severity === 'error');
    if (errorConflicts.length > 0 && conflictStrategy === 'fail') {
      const result: MergeResult = {
        success: false,
        kgprId: kgpr.id,
        conflicts,
        applied: {
          entitiesAdded: 0,
          entitiesUpdated: 0,
          entitiesDeleted: 0,
          relationshipsAdded: 0,
          relationshipsUpdated: 0,
          relationshipsDeleted: 0,
        },
        skipped: { entities: [], relationships: [] },
        auditLog: this.createAuditLog(kgpr, 'conflict_check', 'failed', {
          changes: {
            entitiesAdded: [],
            entitiesUpdated: [],
            entitiesDeleted: [],
            relationshipsAdded: [],
            relationshipsUpdated: [],
            relationshipsDeleted: [],
          },
          conflicts,
          resolutions: [],
          durationMs: Date.now() - startTime,
          mergerId,
          mergerName,
        }),
        error: `${errorConflicts.length} blocking conflict(s) found`,
      };

      this.emit('merge:failed', { kgprId: kgpr.id, error: result.error! });
      return result;
    }

    if (dryRun) {
      // Dry run - just return what would happen
      const result: MergeResult = {
        success: true,
        kgprId: kgpr.id,
        conflicts,
        applied: {
          entitiesAdded: kgpr.diff.entities.added.length,
          entitiesUpdated: kgpr.diff.entities.updated.length,
          entitiesDeleted: kgpr.diff.entities.deleted.length,
          relationshipsAdded: kgpr.diff.relationships.added.length,
          relationshipsUpdated: kgpr.diff.relationships.updated.length,
          relationshipsDeleted: kgpr.diff.relationships.deleted.length,
        },
        skipped: { entities: [], relationships: [] },
        auditLog: this.createAuditLog(kgpr, 'dry_run', 'success', {
          changes: {
            entitiesAdded: kgpr.diff.entities.added,
            entitiesUpdated: kgpr.diff.entities.updated,
            entitiesDeleted: kgpr.diff.entities.deleted,
            relationshipsAdded: kgpr.diff.relationships.added,
            relationshipsUpdated: kgpr.diff.relationships.updated,
            relationshipsDeleted: kgpr.diff.relationships.deleted,
          },
          conflicts,
          resolutions: [],
          durationMs: Date.now() - startTime,
          mergerId,
          mergerName,
        }),
      };

      this.emit('merge:completed', { result });
      return result;
    }

    // Actually apply the diff
    return this.applyDiff(kgpr, conflicts, resolutions, conflictStrategy, startTime, mergerId, mergerName);
  }

  /**
   * Apply diff to global KG
   */
  private async applyDiff(
    kgpr: KGPR,
    conflicts: MergeConflict[],
    resolutions: Map<string, ConflictResolution>,
    conflictStrategy: 'fail' | 'skip_conflicts' | 'force',
    startTime: number,
    mergerId: string,
    mergerName: string
  ): Promise<MergeResult> {
    if (!this.globalKG) {
      throw new Error('Global knowledge graph not connected');
    }

    const applied = {
      entitiesAdded: 0,
      entitiesUpdated: 0,
      entitiesDeleted: 0,
      relationshipsAdded: 0,
      relationshipsUpdated: 0,
      relationshipsDeleted: 0,
    };
    const skipped = { entities: [] as string[], relationships: [] as string[] };
    const appliedChanges = {
      entitiesAdded: [] as EntityChange[],
      entitiesUpdated: [] as EntityChange[],
      entitiesDeleted: [] as EntityChange[],
      relationshipsAdded: [] as RelationshipChange[],
      relationshipsUpdated: [] as RelationshipChange[],
      relationshipsDeleted: [] as RelationshipChange[],
    };
    const appliedResolutions: Array<{ conflictId: string; resolution: ConflictResolution }> = [];

    // Build conflict lookup
    const conflictsByLocalId = new Map<string, MergeConflict>();
    for (const conflict of conflicts) {
      conflictsByLocalId.set(conflict.localId, conflict);
    }

    // Apply entity additions
    const totalOps = 
      kgpr.diff.entities.added.length +
      kgpr.diff.entities.updated.length +
      kgpr.diff.entities.deleted.length +
      kgpr.diff.relationships.added.length +
      kgpr.diff.relationships.deleted.length;
    let completedOps = 0;

    for (const entity of kgpr.diff.entities.added) {
      this.emit('merge:progress', { phase: 'apply', progress: ++completedOps, total: totalOps });

      const conflict = conflictsByLocalId.get(entity.localId);
      if (conflict) {
        const resolution = resolutions.get(conflict.id) ?? conflict.suggestedResolution ?? 'skip';
        appliedResolutions.push({ conflictId: conflict.id, resolution });

        if (resolution === 'skip' || (conflictStrategy === 'skip_conflicts' && conflict.severity === 'error')) {
          skipped.entities.push(entity.localId);
          continue;
        }
      }

      await this.globalKG.addEntity({
        name: entity.name,
        type: entity.entityType,
        namespace: entity.namespace,
        metadata: entity.metadata,
      });
      applied.entitiesAdded++;
      appliedChanges.entitiesAdded.push(entity);
    }

    // Apply entity updates
    for (const entity of kgpr.diff.entities.updated) {
      this.emit('merge:progress', { phase: 'apply', progress: ++completedOps, total: totalOps });

      const conflict = conflictsByLocalId.get(entity.localId);
      if (conflict && conflict.severity === 'error') {
        skipped.entities.push(entity.localId);
        continue;
      }

      await this.globalKG.updateEntity(entity.name, entity.namespace, entity.metadata ?? {});
      applied.entitiesUpdated++;
      appliedChanges.entitiesUpdated.push(entity);
    }

    // Apply entity deletions
    for (const entity of kgpr.diff.entities.deleted) {
      this.emit('merge:progress', { phase: 'apply', progress: ++completedOps, total: totalOps });

      const conflict = conflictsByLocalId.get(entity.localId);
      if (conflict) {
        skipped.entities.push(entity.localId);
        continue;
      }

      await this.globalKG.deleteEntity(entity.name, entity.namespace);
      applied.entitiesDeleted++;
      appliedChanges.entitiesDeleted.push(entity);
    }

    // Apply relationship additions
    for (const rel of kgpr.diff.relationships.added) {
      this.emit('merge:progress', { phase: 'apply', progress: ++completedOps, total: totalOps });

      const relId = rel.localId ?? `${rel.sourceName}-${rel.targetName}`;
      const conflict = conflictsByLocalId.get(relId);
      if (conflict && conflict.severity === 'error') {
        skipped.relationships.push(relId);
        continue;
      }

      await this.globalKG.addRelationship({
        sourceName: rel.sourceName,
        sourceNamespace: rel.sourceNamespace,
        targetName: rel.targetName,
        targetNamespace: rel.targetNamespace,
        type: rel.relationshipType,
        metadata: rel.metadata,
      });
      applied.relationshipsAdded++;
      appliedChanges.relationshipsAdded.push(rel);
    }

    // Apply relationship deletions
    for (const rel of kgpr.diff.relationships.deleted) {
      this.emit('merge:progress', { phase: 'apply', progress: ++completedOps, total: totalOps });

      await this.globalKG.deleteRelationship(
        rel.sourceName,
        rel.sourceNamespace,
        rel.targetName,
        rel.targetNamespace,
        rel.relationshipType
      );
      applied.relationshipsDeleted++;
      appliedChanges.relationshipsDeleted.push(rel);
    }

    const result: MergeResult = {
      success: true,
      kgprId: kgpr.id,
      conflicts,
      applied,
      skipped,
      auditLog: this.createAuditLog(kgpr, 'merge', 'success', {
        changes: appliedChanges,
        conflicts,
        resolutions: appliedResolutions,
        durationMs: Date.now() - startTime,
        mergerId,
        mergerName,
      }),
    };

    this.emit('merge:completed', { result });
    return result;
  }

  // ============================================================================
  // Audit Logging
  // ============================================================================

  /**
   * Create an audit log entry
   */
  private createAuditLog(
    kgpr: KGPR,
    operation: 'merge' | 'dry_run' | 'conflict_check',
    result: 'success' | 'failed' | 'partial',
    data: {
      changes: MergeAuditLog['changes'];
      conflicts: MergeConflict[];
      resolutions: Array<{ conflictId: string; resolution: ConflictResolution }>;
      durationMs: number;
      mergerId: string;
      mergerName: string;
    }
  ): MergeAuditLog {
    const log: MergeAuditLog = {
      id: this.generateAuditLogId(),
      kgprId: kgpr.id,
      kgprTitle: kgpr.title,
      kgprAuthor: kgpr.authorName,
      mergerId: data.mergerId,
      mergerName: data.mergerName,
      operation,
      result,
      timestamp: new Date(),
      changes: data.changes,
      conflicts: data.conflicts,
      resolutions: data.resolutions,
      durationMs: data.durationMs,
    };

    this.auditLogs.push(log);
    return log;
  }

  /**
   * Get all audit logs
   */
  getAuditLogs(): MergeAuditLog[] {
    return [...this.auditLogs];
  }

  /**
   * Get audit logs for a specific KGPR
   */
  getAuditLogsForKGPR(kgprId: string): MergeAuditLog[] {
    return this.auditLogs.filter((log) => log.kgprId === kgprId);
  }

  /**
   * Clear audit logs
   */
  clearAuditLogs(): void {
    this.auditLogs = [];
  }
}
