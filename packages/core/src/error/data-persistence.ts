/**
 * Data Persistence
 * 
 * Ensures data durability and recovery capabilities
 * 
 * @packageDocumentation
 * @module error/data-persistence
 * 
 * @see REQ-ERR-002 - Data Persistence
 * @see Article V - Safety Assurance
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { createHash } from 'crypto';

/**
 * Storage backend type
 */
export type StorageBackend = 'memory' | 'file' | 'custom';

/**
 * Data state
 */
export type DataState = 'pending' | 'persisted' | 'corrupted' | 'recovered';

/**
 * Checkpoint
 */
export interface Checkpoint {
  /** Checkpoint ID */
  id: string;
  /** Timestamp */
  timestamp: Date;
  /** Data snapshot */
  data: unknown;
  /** Checksum */
  checksum: string;
  /** Version */
  version: number;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Transaction
 */
export interface Transaction {
  /** Transaction ID */
  id: string;
  /** Started at */
  startedAt: Date;
  /** Completed at */
  completedAt?: Date;
  /** Operations */
  operations: TransactionOperation[];
  /** Status */
  status: 'pending' | 'committed' | 'rolled-back' | 'failed';
  /** Checkpoint before transaction */
  beforeCheckpoint?: string;
}

/**
 * Transaction operation
 */
export interface TransactionOperation {
  /** Operation type */
  type: 'set' | 'delete' | 'update';
  /** Key */
  key: string;
  /** Value (for set/update) */
  value?: unknown;
  /** Previous value (for rollback) */
  previousValue?: unknown;
  /** Timestamp */
  timestamp: Date;
}

/**
 * Recovery result
 */
export interface RecoveryResult {
  /** Success */
  success: boolean;
  /** Recovered checkpoint */
  checkpoint?: Checkpoint;
  /** Data recovered */
  dataRecovered: boolean;
  /** Items recovered */
  itemsRecovered: number;
  /** Errors */
  errors: string[];
  /** Warnings */
  warnings: string[];
}

/**
 * Persistence statistics
 */
export interface PersistenceStatistics {
  /** Total items */
  totalItems: number;
  /** Total checkpoints */
  totalCheckpoints: number;
  /** Pending transactions */
  pendingTransactions: number;
  /** Last checkpoint */
  lastCheckpoint?: Date;
  /** Storage size (bytes) */
  storageSize: number;
  /** Corrupted items */
  corruptedItems: number;
}

/**
 * Data persistence config
 */
export interface DataPersistenceConfig {
  /** Storage backend */
  backend: StorageBackend;
  /** Storage path (for file backend) */
  storagePath?: string;
  /** Auto-checkpoint interval (ms) */
  autoCheckpointInterval?: number;
  /** Max checkpoints to keep */
  maxCheckpoints: number;
  /** Enable transactions */
  enableTransactions: boolean;
  /** Enable integrity checks */
  enableIntegrityChecks: boolean;
  /** Custom storage adapter */
  customAdapter?: StorageAdapter;
}

/**
 * Storage adapter interface
 */
export interface StorageAdapter {
  get(key: string): Promise<unknown | null>;
  set(key: string, value: unknown): Promise<void>;
  delete(key: string): Promise<void>;
  list(): Promise<string[]>;
  clear(): Promise<void>;
}

/**
 * In-memory storage adapter
 */
export class MemoryStorageAdapter implements StorageAdapter {
  private data = new Map<string, unknown>();

  async get(key: string): Promise<unknown | null> {
    return this.data.get(key) ?? null;
  }

  async set(key: string, value: unknown): Promise<void> {
    this.data.set(key, value);
  }

  async delete(key: string): Promise<void> {
    this.data.delete(key);
  }

  async list(): Promise<string[]> {
    return [...this.data.keys()];
  }

  async clear(): Promise<void> {
    this.data.clear();
  }
}

/**
 * File storage adapter
 */
export class FileStorageAdapter implements StorageAdapter {
  constructor(private basePath: string) {}

  private getFilePath(key: string): string {
    const safeKey = key.replace(/[^a-zA-Z0-9-_]/g, '_');
    return path.join(this.basePath, `${safeKey}.json`);
  }

  async get(key: string): Promise<unknown | null> {
    try {
      const filePath = this.getFilePath(key);
      const content = await fs.readFile(filePath, 'utf-8');
      return JSON.parse(content);
    } catch {
      return null;
    }
  }

  async set(key: string, value: unknown): Promise<void> {
    await fs.mkdir(this.basePath, { recursive: true });
    const filePath = this.getFilePath(key);
    await fs.writeFile(filePath, JSON.stringify(value, null, 2), 'utf-8');
  }

  async delete(key: string): Promise<void> {
    try {
      const filePath = this.getFilePath(key);
      await fs.unlink(filePath);
    } catch {
      // Ignore if file doesn't exist
    }
  }

  async list(): Promise<string[]> {
    try {
      await fs.mkdir(this.basePath, { recursive: true });
      const files = await fs.readdir(this.basePath);
      return files
        .filter((f) => f.endsWith('.json'))
        .map((f) => f.replace('.json', ''));
    } catch {
      return [];
    }
  }

  async clear(): Promise<void> {
    try {
      const files = await this.list();
      await Promise.all(files.map((f) => this.delete(f)));
    } catch {
      // Ignore errors
    }
  }
}

/**
 * Default configuration
 */
export const DEFAULT_PERSISTENCE_CONFIG: DataPersistenceConfig = {
  backend: 'memory',
  maxCheckpoints: 10,
  enableTransactions: true,
  enableIntegrityChecks: true,
};

/**
 * Data Persistence Manager
 */
export class DataPersistence {
  private config: DataPersistenceConfig;
  private adapter: StorageAdapter;
  private checkpoints: Checkpoint[] = [];
  private transactions: Map<string, Transaction> = new Map();
  private currentTransaction: Transaction | null = null;
  private version = 0;
  private checkpointCounter = 0;
  private transactionCounter = 0;
  private checkpointTimer?: NodeJS.Timeout;

  constructor(config?: Partial<DataPersistenceConfig>) {
    this.config = { ...DEFAULT_PERSISTENCE_CONFIG, ...config };
    this.adapter = this.createAdapter();

    // Start auto-checkpoint if configured
    if (this.config.autoCheckpointInterval) {
      this.startAutoCheckpoint();
    }
  }

  /**
   * Create storage adapter based on config
   */
  private createAdapter(): StorageAdapter {
    if (this.config.customAdapter) {
      return this.config.customAdapter;
    }

    switch (this.config.backend) {
      case 'file':
        return new FileStorageAdapter(this.config.storagePath ?? './data');
      case 'memory':
      default:
        return new MemoryStorageAdapter();
    }
  }

  /**
   * Start auto-checkpoint timer
   */
  private startAutoCheckpoint(): void {
    if (this.checkpointTimer) {
      clearInterval(this.checkpointTimer);
    }

    this.checkpointTimer = setInterval(
      () => this.createCheckpoint(),
      this.config.autoCheckpointInterval
    );
  }

  /**
   * Stop auto-checkpoint timer
   */
  stop(): void {
    if (this.checkpointTimer) {
      clearInterval(this.checkpointTimer);
      this.checkpointTimer = undefined;
    }
  }

  /**
   * Set a value
   */
  async set(key: string, value: unknown): Promise<void> {
    // Record operation if in transaction
    if (this.currentTransaction) {
      const previousValue = await this.adapter.get(key);
      this.currentTransaction.operations.push({
        type: previousValue ? 'update' : 'set',
        key,
        value,
        previousValue,
        timestamp: new Date(),
      });
    }

    await this.adapter.set(key, {
      value,
      checksum: this.config.enableIntegrityChecks
        ? this.calculateChecksum(value)
        : undefined,
      version: ++this.version,
      updatedAt: new Date().toISOString(),
    });
  }

  /**
   * Get a value
   */
  async get<T>(key: string): Promise<T | null> {
    const data = (await this.adapter.get(key)) as {
      value: T;
      checksum?: string;
      version: number;
    } | null;

    if (!data) return null;

    // Verify integrity
    if (this.config.enableIntegrityChecks && data.checksum) {
      const currentChecksum = this.calculateChecksum(data.value);
      if (currentChecksum !== data.checksum) {
        throw new Error(`Data integrity check failed for key: ${key}`);
      }
    }

    return data.value;
  }

  /**
   * Delete a value
   */
  async delete(key: string): Promise<void> {
    // Record operation if in transaction
    if (this.currentTransaction) {
      const previousValue = await this.adapter.get(key);
      this.currentTransaction.operations.push({
        type: 'delete',
        key,
        previousValue,
        timestamp: new Date(),
      });
    }

    await this.adapter.delete(key);
  }

  /**
   * List all keys
   */
  async keys(): Promise<string[]> {
    return this.adapter.list();
  }

  /**
   * Clear all data
   */
  async clear(): Promise<void> {
    await this.adapter.clear();
    this.version = 0;
  }

  /**
   * Begin a transaction
   */
  beginTransaction(): string {
    if (!this.config.enableTransactions) {
      throw new Error('Transactions are not enabled');
    }

    if (this.currentTransaction) {
      throw new Error('A transaction is already in progress');
    }

    const id = `tx-${Date.now()}-${++this.transactionCounter}`;
    this.currentTransaction = {
      id,
      startedAt: new Date(),
      operations: [],
      status: 'pending',
    };

    this.transactions.set(id, this.currentTransaction);
    return id;
  }

  /**
   * Commit the current transaction
   */
  async commit(): Promise<void> {
    if (!this.currentTransaction) {
      throw new Error('No transaction in progress');
    }

    this.currentTransaction.status = 'committed';
    this.currentTransaction.completedAt = new Date();
    this.currentTransaction = null;
  }

  /**
   * Rollback the current transaction
   */
  async rollback(): Promise<void> {
    if (!this.currentTransaction) {
      throw new Error('No transaction in progress');
    }

    // Reverse operations
    const operations = [...this.currentTransaction.operations].reverse();
    
    for (const op of operations) {
      switch (op.type) {
        case 'set':
          await this.adapter.delete(op.key);
          break;
        case 'update':
        case 'delete':
          if (op.previousValue !== undefined) {
            await this.adapter.set(op.key, op.previousValue);
          }
          break;
      }
    }

    this.currentTransaction.status = 'rolled-back';
    this.currentTransaction.completedAt = new Date();
    this.currentTransaction = null;
  }

  /**
   * Create a checkpoint
   */
  async createCheckpoint(metadata?: Record<string, unknown>): Promise<Checkpoint> {
    const keys = await this.adapter.list();
    const data: Record<string, unknown> = {};

    for (const key of keys) {
      data[key] = await this.adapter.get(key);
    }

    const checkpoint: Checkpoint = {
      id: `cp-${Date.now()}-${++this.checkpointCounter}`,
      timestamp: new Date(),
      data,
      checksum: this.calculateChecksum(data),
      version: this.version,
      metadata,
    };

    this.checkpoints.push(checkpoint);

    // Enforce max checkpoints
    while (this.checkpoints.length > this.config.maxCheckpoints) {
      this.checkpoints.shift();
    }

    return checkpoint;
  }

  /**
   * Restore from checkpoint
   */
  async restoreCheckpoint(checkpointId: string): Promise<RecoveryResult> {
    const checkpoint = this.checkpoints.find((c) => c.id === checkpointId);
    
    if (!checkpoint) {
      return {
        success: false,
        dataRecovered: false,
        itemsRecovered: 0,
        errors: [`Checkpoint ${checkpointId} not found`],
        warnings: [],
      };
    }

    // Verify checkpoint integrity
    const currentChecksum = this.calculateChecksum(checkpoint.data);
    if (currentChecksum !== checkpoint.checksum) {
      return {
        success: false,
        checkpoint,
        dataRecovered: false,
        itemsRecovered: 0,
        errors: ['Checkpoint data integrity check failed'],
        warnings: [],
      };
    }

    // Clear current data
    await this.adapter.clear();

    // Restore data
    const data = checkpoint.data as Record<string, unknown>;
    let itemsRecovered = 0;
    const errors: string[] = [];

    for (const [key, value] of Object.entries(data)) {
      try {
        await this.adapter.set(key, value);
        itemsRecovered++;
      } catch (error) {
        errors.push(`Failed to restore ${key}: ${(error as Error).message}`);
      }
    }

    this.version = checkpoint.version;

    return {
      success: errors.length === 0,
      checkpoint,
      dataRecovered: true,
      itemsRecovered,
      errors,
      warnings: [],
    };
  }

  /**
   * Restore from latest checkpoint
   */
  async restoreLatest(): Promise<RecoveryResult> {
    if (this.checkpoints.length === 0) {
      return {
        success: false,
        dataRecovered: false,
        itemsRecovered: 0,
        errors: ['No checkpoints available'],
        warnings: [],
      };
    }

    const latestCheckpoint = this.checkpoints[this.checkpoints.length - 1];
    return this.restoreCheckpoint(latestCheckpoint.id);
  }

  /**
   * Get all checkpoints
   */
  getCheckpoints(): Checkpoint[] {
    return [...this.checkpoints];
  }

  /**
   * Get latest checkpoint
   */
  getLatestCheckpoint(): Checkpoint | null {
    return this.checkpoints.length > 0
      ? this.checkpoints[this.checkpoints.length - 1]
      : null;
  }

  /**
   * Verify data integrity
   */
  async verifyIntegrity(): Promise<{
    valid: boolean;
    errors: string[];
    corruptedKeys: string[];
  }> {
    const keys = await this.adapter.list();
    const errors: string[] = [];
    const corruptedKeys: string[] = [];

    for (const key of keys) {
      try {
        const data = (await this.adapter.get(key)) as {
          value: unknown;
          checksum?: string;
        } | null;

        if (data && data.checksum) {
          const currentChecksum = this.calculateChecksum(data.value);
          if (currentChecksum !== data.checksum) {
            errors.push(`Integrity check failed for key: ${key}`);
            corruptedKeys.push(key);
          }
        }
      } catch (error) {
        errors.push(`Error checking ${key}: ${(error as Error).message}`);
        corruptedKeys.push(key);
      }
    }

    return {
      valid: errors.length === 0,
      errors,
      corruptedKeys,
    };
  }

  /**
   * Repair corrupted data
   */
  async repair(): Promise<RecoveryResult> {
    const integrity = await this.verifyIntegrity();
    
    if (integrity.valid) {
      return {
        success: true,
        dataRecovered: false,
        itemsRecovered: 0,
        errors: [],
        warnings: [],
      };
    }

    // Try to recover from checkpoint
    if (this.checkpoints.length > 0) {
      // Find a valid checkpoint
      for (let i = this.checkpoints.length - 1; i >= 0; i--) {
        const checkpoint = this.checkpoints[i];
        const checksum = this.calculateChecksum(checkpoint.data);
        
        if (checksum === checkpoint.checksum) {
          return this.restoreCheckpoint(checkpoint.id);
        }
      }
    }

    // No valid checkpoint, delete corrupted keys
    const errors: string[] = [];
    let itemsRecovered = 0;

    for (const key of integrity.corruptedKeys) {
      try {
        await this.adapter.delete(key);
        itemsRecovered++;
      } catch (error) {
        errors.push(`Failed to remove corrupted key ${key}: ${(error as Error).message}`);
      }
    }

    return {
      success: errors.length === 0,
      dataRecovered: false,
      itemsRecovered,
      errors,
      warnings: [`${integrity.corruptedKeys.length} corrupted items were removed`],
    };
  }

  /**
   * Get statistics
   */
  async getStatistics(): Promise<PersistenceStatistics> {
    const keys = await this.adapter.list();
    let storageSize = 0;
    let corruptedItems = 0;

    for (const key of keys) {
      try {
        const data = await this.adapter.get(key);
        if (data) {
          storageSize += JSON.stringify(data).length;
          
          const typedData = data as { value: unknown; checksum?: string };
          if (typedData.checksum) {
            const checksum = this.calculateChecksum(typedData.value);
            if (checksum !== typedData.checksum) {
              corruptedItems++;
            }
          }
        }
      } catch {
        corruptedItems++;
      }
    }

    const latestCheckpoint = this.getLatestCheckpoint();

    return {
      totalItems: keys.length,
      totalCheckpoints: this.checkpoints.length,
      pendingTransactions: [...this.transactions.values()].filter(
        (t) => t.status === 'pending'
      ).length,
      lastCheckpoint: latestCheckpoint?.timestamp,
      storageSize,
      corruptedItems,
    };
  }

  /**
   * Export all data
   */
  async export(): Promise<{
    data: Record<string, unknown>;
    checkpoints: Checkpoint[];
    version: number;
    exportedAt: Date;
  }> {
    const keys = await this.adapter.list();
    const data: Record<string, unknown> = {};

    for (const key of keys) {
      data[key] = await this.adapter.get(key);
    }

    return {
      data,
      checkpoints: [...this.checkpoints],
      version: this.version,
      exportedAt: new Date(),
    };
  }

  /**
   * Import data
   */
  async import(exportData: {
    data: Record<string, unknown>;
    checkpoints?: Checkpoint[];
    version?: number;
  }): Promise<void> {
    await this.adapter.clear();

    for (const [key, value] of Object.entries(exportData.data)) {
      await this.adapter.set(key, value);
    }

    if (exportData.checkpoints) {
      this.checkpoints = [...exportData.checkpoints];
    }

    if (exportData.version !== undefined) {
      this.version = exportData.version;
    }
  }

  /**
   * Calculate checksum
   */
  private calculateChecksum(data: unknown): string {
    const json = JSON.stringify(data);
    return createHash('sha256').update(json).digest('hex');
  }
}

/**
 * Create data persistence instance
 */
export function createDataPersistence(
  config?: Partial<DataPersistenceConfig>
): DataPersistence {
  return new DataPersistence(config);
}

/**
 * Write-ahead log
 */
export class WriteAheadLog {
  private log: TransactionOperation[] = [];
  private committed: Set<string> = new Set();

  /**
   * Append operation to log
   */
  append(operation: TransactionOperation): void {
    this.log.push(operation);
  }

  /**
   * Mark operations as committed
   */
  commit(transactionId: string): void {
    this.committed.add(transactionId);
  }

  /**
   * Get uncommitted operations
   */
  getUncommitted(): TransactionOperation[] {
    return this.log.filter(
      (op) => !this.committed.has(op.key)
    );
  }

  /**
   * Clear committed operations
   */
  cleanup(): void {
    this.log = this.getUncommitted();
  }

  /**
   * Get all operations
   */
  getAll(): TransactionOperation[] {
    return [...this.log];
  }

  /**
   * Clear log
   */
  clear(): void {
    this.log = [];
    this.committed.clear();
  }
}
