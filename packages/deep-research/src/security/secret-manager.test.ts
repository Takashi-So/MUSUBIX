// Secret Manager Tests
// TSK-DR-013

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { SecretManager } from './secret-manager.js';

describe('SecretManager', () => {
  let manager: SecretManager;

  beforeEach(() => {
    manager = new SecretManager('test-encryption-key-12345678');
  });

  afterEach(() => {
    manager.clear();
  });

  describe('store and retrieve', () => {
    it('should store and retrieve a secret', () => {
      manager.store('api-key-1', 'secret-value-123', 'api-key');

      const value = manager.retrieve('api-key-1');

      expect(value).toBe('secret-value-123');
    });

    it('should store secrets with different types', () => {
      manager.store('key1', 'value1', 'api-key');
      manager.store('key2', 'value2', 'token');
      manager.store('key3', 'value3', 'password');

      expect(manager.retrieve('key1')).toBe('value1');
      expect(manager.retrieve('key2')).toBe('value2');
      expect(manager.retrieve('key3')).toBe('value3');
    });

    it('should throw error for empty key', () => {
      expect(() => manager.store('', 'value', 'api-key')).toThrow('Secret key cannot be empty');
    });

    it('should throw error for empty value', () => {
      expect(() => manager.store('key', '', 'api-key')).toThrow('Secret value cannot be empty');
    });

    it('should return null for non-existent secret', () => {
      const value = manager.retrieve('non-existent');

      expect(value).toBeNull();
    });
  });

  describe('encryption', () => {
    it('should encrypt stored values', () => {
      manager.store('test-key', 'test-value', 'api-key');

      const metadata = manager.getMetadata('test-key');
      expect(metadata).toBeDefined();
      // encryptedValue is not exposed in metadata
    });

    it('should decrypt correctly', () => {
      const originalValue = 'My Secret API Key 12345!@#$%';
      manager.store('complex-key', originalValue, 'api-key');

      const retrieved = manager.retrieve('complex-key');

      expect(retrieved).toBe(originalValue);
    });

    it('should use different encryption keys', () => {
      const manager1 = new SecretManager('key-1');
      const manager2 = new SecretManager('key-2');

      manager1.store('test', 'value', 'api-key');
      manager2.store('test', 'value', 'api-key');

      // Both should retrieve the same value despite different encryption
      expect(manager1.retrieve('test')).toBe('value');
      expect(manager2.retrieve('test')).toBe('value');
    });
  });

  describe('expiry', () => {
    it('should return secret before expiry', () => {
      const futureTime = Date.now() + 10000; // 10 seconds from now
      manager.store('temp-key', 'temp-value', 'api-key', futureTime);

      const value = manager.retrieve('temp-key');

      expect(value).toBe('temp-value');
    });

    it('should return null for expired secret', () => {
      const pastTime = Date.now() - 1000; // 1 second ago
      manager.store('expired-key', 'expired-value', 'api-key', pastTime);

      const value = manager.retrieve('expired-key');

      expect(value).toBeNull();
    });

    it('should remove expired secret from storage', () => {
      const pastTime = Date.now() - 1000;
      manager.store('expired', 'value', 'api-key', pastTime);

      manager.retrieve('expired'); // This should trigger cleanup

      expect(manager.has('expired')).toBe(false);
    });
  });

  describe('has', () => {
    it('should return true for existing secret', () => {
      manager.store('key', 'value', 'api-key');

      expect(manager.has('key')).toBe(true);
    });

    it('should return false for non-existent secret', () => {
      expect(manager.has('non-existent')).toBe(false);
    });

    it('should return false for expired secret', () => {
      const pastTime = Date.now() - 1000;
      manager.store('expired', 'value', 'api-key', pastTime);

      expect(manager.has('expired')).toBe(false);
    });
  });

  describe('remove', () => {
    it('should remove a secret', () => {
      manager.store('key', 'value', 'api-key');

      const removed = manager.remove('key');

      expect(removed).toBe(true);
      expect(manager.has('key')).toBe(false);
    });

    it('should return false for non-existent secret', () => {
      const removed = manager.remove('non-existent');

      expect(removed).toBe(false);
    });
  });

  describe('clear', () => {
    it('should clear all secrets', () => {
      manager.store('key1', 'value1', 'api-key');
      manager.store('key2', 'value2', 'token');
      manager.store('key3', 'value3', 'password');

      manager.clear();

      expect(manager.listKeys()).toHaveLength(0);
    });
  });

  describe('listKeys', () => {
    it('should list all secret keys', () => {
      manager.store('key1', 'value1', 'api-key');
      manager.store('key2', 'value2', 'token');
      manager.store('key3', 'value3', 'password');

      const keys = manager.listKeys();

      expect(keys).toHaveLength(3);
      expect(keys).toContain('key1');
      expect(keys).toContain('key2');
      expect(keys).toContain('key3');
    });

    it('should exclude expired secrets', () => {
      manager.store('active', 'value1', 'api-key');
      manager.store('expired', 'value2', 'api-key', Date.now() - 1000);

      const keys = manager.listKeys();

      expect(keys).toHaveLength(1);
      expect(keys).toContain('active');
      expect(keys).not.toContain('expired');
    });
  });

  describe('getMetadata', () => {
    it('should return secret metadata', () => {
      manager.store('key', 'value', 'api-key');

      const metadata = manager.getMetadata('key');

      expect(metadata).toBeDefined();
      expect(metadata?.key).toBe('key');
      expect(metadata?.type).toBe('api-key');
      expect(metadata?.createdAt).toBeDefined();
    });

    it('should update lastAccessedAt on retrieve', () => {
      manager.store('key', 'value', 'api-key');

      const before = manager.getMetadata('key');
      expect(before?.lastAccessedAt).toBeUndefined();

      manager.retrieve('key');

      const after = manager.getMetadata('key');
      expect(after?.lastAccessedAt).toBeDefined();
    });

    it('should return null for non-existent secret', () => {
      const metadata = manager.getMetadata('non-existent');

      expect(metadata).toBeNull();
    });
  });

  describe('environment variable fallback', () => {
    it('should fallback to environment variable', () => {
      // Set a test environment variable
      process.env.TEST_API_KEY = 'env-value';

      const value = manager.retrieve('TEST_API_KEY');

      expect(value).toBe('env-value');

      // Cleanup
      delete process.env.TEST_API_KEY;
    });

    it('should convert key format for environment lookup', () => {
      process.env.MY_SECRET_KEY = 'env-value-2';

      // Try with dash format
      const value = manager.retrieve('my-secret-key');

      expect(value).toBe('env-value-2');

      delete process.env.MY_SECRET_KEY;
    });
  });
});
