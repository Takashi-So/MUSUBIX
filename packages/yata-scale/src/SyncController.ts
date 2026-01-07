/**
 * @nahisaho/yata-scale - Sync Controller
 * 
 * Handles synchronization between nodes
 */

import { ok, err, type Result } from 'neverthrow';
import type { Entity, Relationship, ConflictStrategy, SyncSession, SyncChange, WALEntry } from './types.js';
import { SyncError } from './errors.js';

/**
 * Vector clock for causality tracking
 */
export class VectorClock {
  private clock: Map<string, number>;
  private nodeId: string;

  constructor(nodeId: string) {
    this.nodeId = nodeId;
    this.clock = new Map([[nodeId, 0]]);
  }

  increment(): void {
    this.clock.set(this.nodeId, (this.clock.get(this.nodeId) ?? 0) + 1);
  }

  get(nodeId: string): number {
    return this.clock.get(nodeId) ?? 0;
  }

  merge(other: VectorClock): void {
    for (const [nodeId, time] of other.clock) {
      const current = this.clock.get(nodeId) ?? 0;
      this.clock.set(nodeId, Math.max(current, time));
    }
  }

  compare(other: VectorClock): 'before' | 'after' | 'concurrent' | 'equal' {
    let thisGreater = false;
    let otherGreater = false;

    const allNodes = new Set([...this.clock.keys(), ...other.clock.keys()]);

    for (const nodeId of allNodes) {
      const thisTime = this.clock.get(nodeId) ?? 0;
      const otherTime = other.clock.get(nodeId) ?? 0;

      if (thisTime > otherTime) thisGreater = true;
      if (otherTime > thisTime) otherGreater = true;
    }

    if (thisGreater && otherGreater) return 'concurrent';
    if (thisGreater) return 'after';
    if (otherGreater) return 'before';
    return 'equal';
  }

  clone(): VectorClock {
    const cloned = new VectorClock(this.nodeId);
    cloned.clock = new Map(this.clock);
    return cloned;
  }

  entries(): Map<string, number> {
    return new Map(this.clock);
  }

  serialize(): string {
    return JSON.stringify({
      nodeId: this.nodeId,
      clock: Object.fromEntries(this.clock),
    });
  }

  static deserialize(data: string): VectorClock {
    const parsed = JSON.parse(data);
    const clock = new VectorClock(parsed.nodeId);
    clock.clock = new Map(Object.entries(parsed.clock as Record<string, number>));
    return clock;
  }
}

/**
 * Conflict resolver
 */
export class ConflictResolver {
  private strategy: ConflictStrategy;
  private customResolver?: (local: Entity, remote: Entity) => Entity;

  constructor(strategy: ConflictStrategy, customResolver?: (local: Entity, remote: Entity) => Entity) {
    this.strategy = strategy;
    this.customResolver = customResolver;
  }

  resolve(local: Entity, remote: Entity): Result<Entity, SyncError> {
    switch (this.strategy) {
      case 'lww':
        return ok(local.metadata.updatedAt >= remote.metadata.updatedAt ? local : remote);

      case 'fww':
        return ok(local.metadata.createdAt <= remote.metadata.createdAt ? local : remote);

      case 'merge':
        return ok({
          ...local,
          properties: { ...local.properties, ...remote.properties },
          metadata: {
            ...local.metadata,
            version: Math.max(local.metadata.version, remote.metadata.version) + 1,
            updatedAt: new Date(),
          },
        });

      case 'custom':
        if (this.customResolver) {
          return ok(this.customResolver(local, remote));
        }
        return err(new SyncError('Custom resolver not provided'));

      default:
        return err(new SyncError(`Unknown strategy: ${this.strategy}`));
    }
  }
}

/**
 * Write-ahead log manager
 */
export class WALManager {
  private entries: WALEntry[] = [];
  private sequence = 0;
  readonly maxSegmentSize: number;
  private maxSegments: number;

  constructor(config: { maxSegmentSize: number; maxSegments: number }) {
    this.maxSegmentSize = config.maxSegmentSize;
    this.maxSegments = config.maxSegments;
  }

  append(operation: string, data: Record<string, unknown>): Result<number, SyncError> {
    this.sequence++;
    const entry: WALEntry = {
      sequence: this.sequence,
      operation,
      timestamp: new Date(),
      data,
      checksum: this.calculateChecksum(operation, data),
    };

    this.entries.push(entry);

    // Trim old entries
    while (this.entries.length > this.maxSegments * 100) {
      this.entries.shift();
    }

    return ok(this.sequence);
  }

  read(fromSeq: number, toSeq: number): WALEntry[] {
    return this.entries.filter((e) => e.sequence >= fromSeq && e.sequence <= toSeq);
  }

  readFrom(sequence: number): WALEntry[] {
    return this.entries.filter((e) => e.sequence >= sequence);
  }

  replay(callback: (entry: WALEntry) => void): void {
    for (const entry of this.entries) {
      callback(entry);
    }
  }

  truncateBefore(sequence: number): void {
    this.entries = this.entries.filter((e) => e.sequence >= sequence);
  }

  get latestSequence(): number {
    return this.sequence;
  }

  getStats(): { entryCount: number; segmentCount: number } {
    return {
      entryCount: this.entries.length,
      segmentCount: Math.ceil(this.entries.length / 100),
    };
  }

  clear(): void {
    this.entries = [];
    this.sequence = 0;
  }

  private calculateChecksum(operation: string, data: Record<string, unknown>): string {
    const str = operation + JSON.stringify(data);
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
      hash = ((hash << 5) - hash + str.charCodeAt(i)) | 0;
    }
    return hash.toString(16);
  }
}

/**
 * Sync controller
 */
export class SyncController {
  private nodeId: string;
  private clock: VectorClock;
  private wal: WALManager;
  readonly resolver: ConflictResolver;
  private sessions: Map<string, SyncSession> = new Map();
  private peers: Map<string, { lastSync: Date; status: string }> = new Map();
  private changes: SyncChange[] = [];

  constructor(nodeId: string, strategy: ConflictStrategy = 'lww') {
    this.nodeId = nodeId;
    this.clock = new VectorClock(nodeId);
    this.wal = new WALManager({ maxSegmentSize: 10000, maxSegments: 10 });
    this.resolver = new ConflictResolver(strategy);
  }

  recordCreate(entity: Entity): void {
    this.clock.increment();
    const change: SyncChange = {
      sequence: this.clock.get(this.nodeId),
      operation: 'create',
      timestamp: new Date(),
      data: { entity },
    };
    this.changes.push(change);
    this.wal.append('create', { entityId: entity.id, entity });
  }

  recordUpdate(entity: Entity, _before: Entity): void {
    this.clock.increment();
    const change: SyncChange = {
      sequence: this.clock.get(this.nodeId),
      operation: 'update',
      timestamp: new Date(),
      data: { entity },
    };
    this.changes.push(change);
    this.wal.append('update', { entityId: entity.id, entity });
  }

  recordDelete(entityId: string, _entity: Entity): void {
    this.clock.increment();
    const change: SyncChange = {
      sequence: this.clock.get(this.nodeId),
      operation: 'delete',
      timestamp: new Date(),
      data: { entityId },
    };
    this.changes.push(change);
    this.wal.append('delete', { entityId });
  }

  recordRelationshipCreate(rel: Relationship): void {
    this.clock.increment();
    this.wal.append('rel_create', { relationshipId: rel.id, relationship: rel });
  }

  recordRelationshipDelete(relId: string): void {
    this.clock.increment();
    this.wal.append('rel_delete', { relationshipId: relId });
  }

  startSession(peerId: string): Result<SyncSession, SyncError> {
    if (this.sessions.has(peerId)) {
      return err(new SyncError(`Session with ${peerId} already exists`));
    }

    const session: SyncSession = {
      id: `session_${Date.now()}`,
      peerId,
      status: 'syncing',
      startTime: new Date(),
      lastActivity: new Date(),
      changesReceived: 0,
      changesSent: 0,
    };

    this.sessions.set(session.id, session);
    return ok(session);
  }

  endSession(sessionId: string): void {
    this.sessions.delete(sessionId);
  }

  getChanges(fromSequence: number): SyncChange[] {
    return this.changes.filter((c) => c.sequence > fromSequence);
  }

  getDelta(
    _peerId: string,
    fromSequence: number
  ): { changes: SyncChange[]; clock: VectorClock } {
    return {
      changes: this.getChanges(fromSequence),
      clock: this.clock.clone(),
    };
  }

  applyDelta(delta: {
    peerId: string;
    changes: SyncChange[];
    clock: VectorClock;
  }): Result<void, SyncError> {
    this.clock.merge(delta.clock);

    for (const change of delta.changes) {
      this.changes.push(change);
      this.wal.append(change.operation, change.data);
    }

    return ok(undefined);
  }

  registerPeer(peerId: string, info: { lastSync: Date; status: string }): void {
    this.peers.set(peerId, info);
  }

  unregisterPeer(peerId: string): void {
    this.peers.delete(peerId);
  }

  getPeers(): string[] {
    return Array.from(this.peers.keys());
  }

  getClock(): VectorClock {
    return this.clock.clone();
  }

  getStats(): {
    nodeId: string;
    activeSessions: number;
    walSequence: number;
    peerCount: number;
  } {
    return {
      nodeId: this.nodeId,
      activeSessions: this.sessions.size,
      walSequence: this.wal.latestSequence,
      peerCount: this.peers.size,
    };
  }
}
