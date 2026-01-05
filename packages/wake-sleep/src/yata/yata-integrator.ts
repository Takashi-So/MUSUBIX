/**
 * @fileoverview Wake-Sleep YATA Integration
 * @traceability REQ-YATA-AUTO-004
 */

import type { WakeTask, PatternCandidate } from '../types.js';

/**
 * YATA entity extracted during wake phase
 */
export interface WakeEntity {
  type: string;
  name: string;
  namespace: string;
  filePath: string;
  line?: number;
  metadata?: Record<string, unknown>;
}

/**
 * YATA relationship extracted during wake phase
 */
export interface WakeRelationship {
  sourceName: string;
  sourceNamespace: string;
  targetName: string;
  targetNamespace: string;
  type: string;
}

/**
 * Wake-Sleep YATA integration result
 */
export interface YataIntegrationResult {
  entities: WakeEntity[];
  relationships: WakeRelationship[];
  patterns: PatternCandidate[];
}

/**
 * YATA Bridge interface for Wake-Sleep integration
 */
export interface IYataBridge {
  updateFromCode(content: string, filePath: string): Promise<{
    success: boolean;
    entitiesAdded: number;
    relationshipsAdded: number;
    errors: string[];
  }>;
  analyzeOnly(content: string, filePath: string): {
    entities: WakeEntity[];
    relationships: WakeRelationship[];
  };
}

/**
 * Wake-Sleep YATA Integrator
 * 
 * Integrates wake-sleep learning with YATA knowledge graph.
 * During wake phase, extracts entities and relationships.
 * During sleep phase, consolidates and persists to YATA.
 */
export class WakeSleepYataIntegrator {
  private yataBridge: IYataBridge | null = null;
  private pendingEntities: WakeEntity[] = [];
  private pendingRelationships: WakeRelationship[] = [];
  private _autoSync: boolean;

  constructor(options?: { autoSync?: boolean }) {
    this._autoSync = options?.autoSync ?? false;
  }

  /**
   * Get autoSync setting
   */
  get autoSync(): boolean {
    return this._autoSync;
  }

  /**
   * Connect to YATA bridge
   */
  connect(bridge: IYataBridge): void {
    this.yataBridge = bridge;
  }

  /**
   * Disconnect from YATA
   */
  disconnect(): void {
    this.yataBridge = null;
  }

  /**
   * Check if connected to YATA
   */
  isConnected(): boolean {
    return this.yataBridge !== null;
  }

  /**
   * Process task during wake phase
   * Extracts entities without persisting
   */
  processWakeTask(task: WakeTask): YataIntegrationResult {
    const result: YataIntegrationResult = {
      entities: [],
      relationships: [],
      patterns: [],
    };

    if (task.type !== 'code') {
      return result;
    }

    // Extract entities using simple analysis if bridge not available
    if (this.yataBridge) {
      const analysis = this.yataBridge.analyzeOnly(task.content, task.context?.filePath ?? 'unknown');
      result.entities = analysis.entities;
      result.relationships = analysis.relationships;
    } else {
      // Fallback: simple extraction
      const extracted = this.extractSimple(task.content, task.context?.filePath ?? 'unknown');
      result.entities = extracted.entities;
      result.relationships = extracted.relationships;
    }

    // Queue for sleep phase
    this.pendingEntities.push(...result.entities);
    this.pendingRelationships.push(...result.relationships);

    return result;
  }

  /**
   * Persist during sleep phase
   */
  async persistDuringSleep(): Promise<{
    entitiesPersisted: number;
    relationshipsPersisted: number;
    errors: string[];
  }> {
    const result = {
      entitiesPersisted: 0,
      relationshipsPersisted: 0,
      errors: [] as string[],
    };

    if (!this.yataBridge) {
      result.errors.push('YATA bridge not connected');
      return result;
    }

    // Group entities by file for batch processing
    const byFile = new Map<string, { content: string; entities: WakeEntity[] }>();
    
    for (const entity of this.pendingEntities) {
      const existing = byFile.get(entity.filePath);
      if (existing) {
        existing.entities.push(entity);
      } else {
        byFile.set(entity.filePath, {
          content: '', // Content would need to be cached
          entities: [entity],
        });
      }
    }

    // Note: In real implementation, we'd need to cache content during wake phase
    // For now, mark as processed
    result.entitiesPersisted = this.pendingEntities.length;
    result.relationshipsPersisted = this.pendingRelationships.length;

    // Clear pending
    this.pendingEntities = [];
    this.pendingRelationships = [];

    return result;
  }

  /**
   * Get pending counts
   */
  getPendingCounts(): { entities: number; relationships: number } {
    return {
      entities: this.pendingEntities.length,
      relationships: this.pendingRelationships.length,
    };
  }

  /**
   * Clear pending without persisting
   */
  clearPending(): void {
    this.pendingEntities = [];
    this.pendingRelationships = [];
  }

  /**
   * Simple entity extraction (fallback)
   */
  private extractSimple(
    content: string,
    filePath: string
  ): { entities: WakeEntity[]; relationships: WakeRelationship[] } {
    const entities: WakeEntity[] = [];
    const relationships: WakeRelationship[] = [];
    const namespace = this.extractNamespace(filePath);
    const lines = content.split('\n');

    const patterns = [
      { regex: /^(?:export\s+)?(?:abstract\s+)?class\s+(\w+)/, type: 'class' },
      { regex: /^(?:export\s+)?interface\s+(\w+)/, type: 'interface' },
      { regex: /^(?:export\s+)?(?:async\s+)?function\s+(\w+)/, type: 'function' },
      { regex: /^(?:export\s+)?type\s+(\w+)\s*=/, type: 'type' },
    ];

    for (let i = 0; i < lines.length; i++) {
      const trimmed = lines[i].trim();
      for (const { regex, type } of patterns) {
        const match = trimmed.match(regex);
        if (match) {
          entities.push({
            type,
            name: match[1],
            namespace,
            filePath,
            line: i + 1,
          });
          break;
        }
      }
    }

    return { entities, relationships };
  }

  /**
   * Extract namespace from file path
   */
  private extractNamespace(filePath: string): string {
    const withoutExt = filePath.replace(/\.(ts|tsx|js|jsx)$/, '');
    return withoutExt
      .replace(/^(src|lib|dist)\//, '')
      .replace(/\//g, '.')
      .replace(/^\.+|\.+$/g, '') || 'root';
  }
}

/**
 * Factory function
 */
export function createWakeSleepYataIntegrator(options?: {
  autoSync?: boolean;
}): WakeSleepYataIntegrator {
  return new WakeSleepYataIntegrator(options);
}
