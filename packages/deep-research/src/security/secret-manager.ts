// Secret Manager
// TSK-DR-013
// REQ: REQ-DR-NFR-001
// ADR: ADR-v3.4.0-001

/**
 * Secret Type
 */
export type SecretType = 'api-key' | 'token' | 'password' | 'other';

/**
 * Secret Entry
 */
export interface SecretEntry {
  /** Secret key/identifier */
  key: string;
  /** Secret type */
  type: SecretType;
  /** Encrypted value */
  encryptedValue: string;
  /** Creation timestamp */
  createdAt: number;
  /** Last access timestamp */
  lastAccessedAt?: number;
  /** Expiry timestamp (optional) */
  expiresAt?: number;
}

/**
 * Secret Manager
 * 
 * Secure storage and retrieval of API keys and secrets.
 * 
 * Features:
 * - In-memory secure storage
 * - Basic encryption (XOR-based for demo, use real crypto in production)
 * - Environment variable fallback
 * - Expiry support
 * - Access tracking
 * 
 * REQ: REQ-DR-NFR-001 - Secure API key management
 * ADR: ADR-v3.4.0-001 - Security best practices
 */
export class SecretManager {
  private readonly secrets = new Map<string, SecretEntry>();
  private readonly encryptionKey: string;
  
  constructor(encryptionKey?: string) {
    // Use provided key or generate a random one
    this.encryptionKey = encryptionKey || this.generateKey();
  }
  
  /**
   * Store a secret
   * 
   * REQ: REQ-DR-NFR-001
   */
  store(key: string, value: string, type: SecretType = 'api-key', expiresAt?: number): void {
    if (!key || key.trim().length === 0) {
      throw new Error('Secret key cannot be empty');
    }
    
    if (!value || value.trim().length === 0) {
      throw new Error('Secret value cannot be empty');
    }
    
    const encryptedValue = this.encrypt(value);
    
    const entry: SecretEntry = {
      key,
      type,
      encryptedValue,
      createdAt: Date.now(),
      expiresAt,
    };
    
    this.secrets.set(key, entry);
    
    console.log(`🔐 Stored secret: ${key} (type: ${type})`);
  }
  
  /**
   * Retrieve a secret
   * 
   * REQ: REQ-DR-NFR-001
   */
  retrieve(key: string): string | null {
    // Try in-memory storage first
    const entry = this.secrets.get(key);
    
    if (entry) {
      // Check expiry
      if (entry.expiresAt && Date.now() > entry.expiresAt) {
        console.warn(`⚠️  Secret expired: ${key}`);
        this.secrets.delete(key);
        return null;
      }
      
      // Update access time
      entry.lastAccessedAt = Date.now();
      
      // Decrypt and return
      return this.decrypt(entry.encryptedValue);
    }
    
    // Fallback to environment variable
    const envValue = this.getEnvVariable(key);
    if (envValue) {
      console.log(`🔍 Retrieved secret from environment: ${key}`);
      return envValue;
    }
    
    console.warn(`⚠️  Secret not found: ${key}`);
    return null;
  }
  
  /**
   * Check if a secret exists
   */
  has(key: string): boolean {
    if (this.secrets.has(key)) {
      const entry = this.secrets.get(key)!;
      
      // Check expiry
      if (entry.expiresAt && Date.now() > entry.expiresAt) {
        this.secrets.delete(key);
        return false;
      }
      
      return true;
    }
    
    // Check environment variable
    return this.getEnvVariable(key) !== null;
  }
  
  /**
   * Remove a secret
   */
  remove(key: string): boolean {
    const existed = this.secrets.has(key);
    this.secrets.delete(key);
    
    if (existed) {
      console.log(`🗑️  Removed secret: ${key}`);
    }
    
    return existed;
  }
  
  /**
   * Clear all secrets
   */
  clear(): void {
    const count = this.secrets.size;
    this.secrets.clear();
    console.log(`🗑️  Cleared ${count} secrets`);
  }
  
  /**
   * List all secret keys (not values!)
   */
  listKeys(): string[] {
    const keys: string[] = [];
    
    for (const [key, entry] of this.secrets.entries()) {
      // Skip expired secrets
      if (entry.expiresAt && Date.now() > entry.expiresAt) {
        this.secrets.delete(key);
        continue;
      }
      
      keys.push(key);
    }
    
    return keys;
  }
  
  /**
   * Get secret metadata (without value)
   */
  getMetadata(key: string): Omit<SecretEntry, 'encryptedValue'> | null {
    const entry = this.secrets.get(key);
    
    if (!entry) {
      return null;
    }
    
    // Check expiry
    if (entry.expiresAt && Date.now() > entry.expiresAt) {
      this.secrets.delete(key);
      return null;
    }
    
    return {
      key: entry.key,
      type: entry.type,
      createdAt: entry.createdAt,
      lastAccessedAt: entry.lastAccessedAt,
      expiresAt: entry.expiresAt,
    };
  }
  
  /**
   * Simple XOR encryption (for demo purposes only)
   * 
   * NOTE: In production, use a proper encryption library like:
   * - Node.js crypto module (AES-256-GCM)
   * - @noble/ciphers
   * - tweetnacl
   */
  private encrypt(value: string): string {
    let result = '';
    for (let i = 0; i < value.length; i++) {
      const charCode = value.charCodeAt(i) ^ this.encryptionKey.charCodeAt(i % this.encryptionKey.length);
      result += String.fromCharCode(charCode);
    }
    return Buffer.from(result, 'binary').toString('base64');
  }
  
  /**
   * Simple XOR decryption (for demo purposes only)
   */
  private decrypt(encrypted: string): string {
    const binary = Buffer.from(encrypted, 'base64').toString('binary');
    let result = '';
    for (let i = 0; i < binary.length; i++) {
      const charCode = binary.charCodeAt(i) ^ this.encryptionKey.charCodeAt(i % this.encryptionKey.length);
      result += String.fromCharCode(charCode);
    }
    return result;
  }
  
  /**
   * Generate a random encryption key
   */
  private generateKey(): string {
    const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    let key = '';
    for (let i = 0; i < 32; i++) {
      key += chars.charAt(Math.floor(Math.random() * chars.length));
    }
    return key;
  }
  
  /**
   * Get environment variable
   */
  private getEnvVariable(key: string): string | null {
    // Try exact match
    if (process.env[key]) {
      return process.env[key]!;
    }
    
    // Try uppercase variant
    const upperKey = key.toUpperCase().replace(/-/g, '_');
    if (process.env[upperKey]) {
      return process.env[upperKey]!;
    }
    
    return null;
  }
}

/**
 * Create a secret manager instance
 */
export function createSecretManager(encryptionKey?: string): SecretManager {
  return new SecretManager(encryptionKey);
}

/**
 * Global secret manager instance (singleton pattern)
 */
let globalSecretManager: SecretManager | null = null;

/**
 * Get or create global secret manager
 */
export function getGlobalSecretManager(): SecretManager {
  if (!globalSecretManager) {
    globalSecretManager = new SecretManager();
  }
  return globalSecretManager;
}
