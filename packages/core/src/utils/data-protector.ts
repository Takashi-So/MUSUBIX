/**
 * Data Protector Utility
 * 
 * Provides data protection, encryption, and security features
 * 
 * @packageDocumentation
 * @module utils/data-protector
 * 
 * @see REQ-SEC-001 - Data Protector
 * @see REQ-ERR-002 - Data Persistence
 * @see DES-MUSUBIX-001 Section 14.1 - Data Protector Design
 */

import { createHash, createCipheriv, createDecipheriv, randomBytes, scrypt } from 'crypto';
import { promisify } from 'util';
import { readFile, writeFile, mkdir, access, unlink } from 'fs/promises';
import { join, dirname } from 'path';

const scryptAsync = promisify(scrypt);

/**
 * Encryption algorithm
 */
const ALGORITHM = 'aes-256-gcm';
const KEY_LENGTH = 32;
const IV_LENGTH = 16;
const SALT_LENGTH = 32;

/**
 * Data protection options
 */
export interface ProtectionOptions {
  /** Enable encryption */
  encrypt: boolean;
  /** Encryption key or password */
  key?: string;
  /** Enable integrity verification */
  verify: boolean;
  /** Enable backup */
  backup: boolean;
  /** Backup path */
  backupPath?: string;
}

/**
 * Protected data structure
 */
export interface ProtectedData {
  /** Data version */
  version: number;
  /** Encrypted flag */
  encrypted: boolean;
  /** Encryption salt (hex) */
  salt?: string;
  /** Initialization vector (hex) */
  iv?: string;
  /** Authentication tag (hex) */
  authTag?: string;
  /** Data payload (encrypted or plain) */
  payload: string;
  /** Integrity hash */
  hash: string;
  /** Timestamp */
  timestamp: string;
}

/**
 * Default protection options
 */
const DEFAULT_OPTIONS: ProtectionOptions = {
  encrypt: false,
  verify: true,
  backup: true,
};

/**
 * Data Protector class
 */
export class DataProtector {
  private options: ProtectionOptions;

  constructor(options?: Partial<ProtectionOptions>) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * Update options
   */
  configure(options: Partial<ProtectionOptions>): void {
    this.options = { ...this.options, ...options };
  }

  /**
   * Protect and save data to file
   */
  async save<T>(filePath: string, data: T, options?: Partial<ProtectionOptions>): Promise<void> {
    const opts = { ...this.options, ...options };
    
    // Create backup if enabled
    if (opts.backup) {
      await this.createBackup(filePath, opts.backupPath);
    }

    // Serialize data
    const serialized = JSON.stringify(data, null, 2);
    
    // Create protected structure
    const protected_: ProtectedData = opts.encrypt && opts.key
      ? await this.encrypt(serialized, opts.key)
      : this.createPlainProtected(serialized);

    // Ensure directory exists
    await mkdir(dirname(filePath), { recursive: true });

    // Write to file
    await writeFile(filePath, JSON.stringify(protected_, null, 2));
  }

  /**
   * Load and verify data from file
   */
  async load<T>(filePath: string, options?: Partial<ProtectionOptions>): Promise<T> {
    const opts = { ...this.options, ...options };

    // Read file
    const content = await readFile(filePath, 'utf-8');
    const protected_ = JSON.parse(content) as ProtectedData;

    // Verify integrity if enabled
    if (opts.verify) {
      const isValid = this.verifyIntegrity(protected_);
      if (!isValid) {
        throw new Error('Data integrity verification failed');
      }
    }

    // Decrypt if encrypted
    let payload: string;
    if (protected_.encrypted) {
      if (!opts.key) {
        throw new Error('Encryption key required to load encrypted data');
      }
      payload = await this.decrypt(protected_, opts.key);
    } else {
      payload = protected_.payload;
    }

    return JSON.parse(payload) as T;
  }

  /**
   * Check if file exists
   */
  async exists(filePath: string): Promise<boolean> {
    try {
      await access(filePath);
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Delete protected file
   */
  async delete(filePath: string, options?: { deleteBackups?: boolean }): Promise<void> {
    await unlink(filePath);
    
    if (options?.deleteBackups && this.options.backupPath) {
      const backupPath = this.getBackupPath(filePath, this.options.backupPath);
      try {
        await unlink(backupPath);
      } catch {
        // Backup may not exist
      }
    }
  }

  /**
   * Calculate hash of data
   */
  hash(data: string): string {
    return createHash('sha256').update(data).digest('hex');
  }

  /**
   * Verify data integrity
   */
  verifyIntegrity(protected_: ProtectedData): boolean {
    const calculatedHash = this.hash(protected_.payload);
    return calculatedHash === protected_.hash;
  }

  /**
   * Create plain protected data structure
   */
  private createPlainProtected(data: string): ProtectedData {
    return {
      version: 1,
      encrypted: false,
      payload: data,
      hash: this.hash(data),
      timestamp: new Date().toISOString(),
    };
  }

  /**
   * Encrypt data
   */
  private async encrypt(data: string, password: string): Promise<ProtectedData> {
    // Generate salt and derive key
    const salt = randomBytes(SALT_LENGTH);
    const key = await scryptAsync(password, salt, KEY_LENGTH) as Buffer;
    
    // Generate IV
    const iv = randomBytes(IV_LENGTH);
    
    // Encrypt
    const cipher = createCipheriv(ALGORITHM, key, iv);
    const encrypted = Buffer.concat([
      cipher.update(data, 'utf8'),
      cipher.final(),
    ]);
    const authTag = cipher.getAuthTag();

    return {
      version: 1,
      encrypted: true,
      salt: salt.toString('hex'),
      iv: iv.toString('hex'),
      authTag: authTag.toString('hex'),
      payload: encrypted.toString('hex'),
      hash: this.hash(encrypted.toString('hex')),
      timestamp: new Date().toISOString(),
    };
  }

  /**
   * Decrypt data
   */
  private async decrypt(protected_: ProtectedData, password: string): Promise<string> {
    if (!protected_.salt || !protected_.iv || !protected_.authTag) {
      throw new Error('Invalid encrypted data structure');
    }

    // Derive key from password
    const salt = Buffer.from(protected_.salt, 'hex');
    const key = await scryptAsync(password, salt, KEY_LENGTH) as Buffer;
    
    // Get IV and auth tag
    const iv = Buffer.from(protected_.iv, 'hex');
    const authTag = Buffer.from(protected_.authTag, 'hex');
    const encrypted = Buffer.from(protected_.payload, 'hex');

    // Decrypt
    const decipher = createDecipheriv(ALGORITHM, key, iv);
    decipher.setAuthTag(authTag);
    
    const decrypted = Buffer.concat([
      decipher.update(encrypted),
      decipher.final(),
    ]);

    return decrypted.toString('utf8');
  }

  /**
   * Create backup of file
   */
  private async createBackup(filePath: string, backupDir?: string): Promise<void> {
    try {
      const exists = await this.exists(filePath);
      if (!exists) {
        return;
      }

      const content = await readFile(filePath, 'utf-8');
      const backupPath = this.getBackupPath(filePath, backupDir);
      
      await mkdir(dirname(backupPath), { recursive: true });
      await writeFile(backupPath, content);
    } catch {
      // Silently fail backup - don't block main operation
    }
  }

  /**
   * Get backup file path
   */
  private getBackupPath(filePath: string, backupDir?: string): string {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const fileName = filePath.split('/').pop() ?? 'backup';
    const backupFileName = `${fileName}.${timestamp}.bak`;
    
    if (backupDir) {
      return join(backupDir, backupFileName);
    }
    
    return join(dirname(filePath), '.backups', backupFileName);
  }
}

/**
 * Sensitive data patterns for detection
 */
const SENSITIVE_PATTERNS = [
  /api[_-]?key/i,
  /secret/i,
  /password/i,
  /token/i,
  /credential/i,
  /private[_-]?key/i,
  /auth/i,
];

/**
 * Check if key might contain sensitive data
 */
export function isSensitiveKey(key: string): boolean {
  return SENSITIVE_PATTERNS.some(pattern => pattern.test(key));
}

/**
 * Mask sensitive value for logging
 */
export function maskValue(value: string): string {
  if (value.length <= 4) {
    return '****';
  }
  return value.slice(0, 2) + '*'.repeat(value.length - 4) + value.slice(-2);
}

/**
 * Redact sensitive data from object for logging
 */
export function redactSensitive<T extends Record<string, unknown>>(obj: T): T {
  const result = { ...obj };
  
  for (const key of Object.keys(result)) {
    const value = result[key];
    
    if (isSensitiveKey(key) && typeof value === 'string') {
      (result as Record<string, unknown>)[key] = maskValue(value);
    } else if (value && typeof value === 'object' && !Array.isArray(value)) {
      (result as Record<string, unknown>)[key] = redactSensitive(value as Record<string, unknown>);
    }
  }
  
  return result;
}

/**
 * Global data protector instance
 */
export const dataProtector = new DataProtector();
