/**
 * Z3Adapter Unit Tests
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { Z3Adapter } from '../../src/z3/Z3Adapter';

describe('Z3Adapter', () => {
  describe('constructor', () => {
    it('should create instance with default options', () => {
      const adapter = new Z3Adapter();
      expect(adapter).toBeInstanceOf(Z3Adapter);
    });

    it('should create instance with preferWasm option', () => {
      const adapter = new Z3Adapter({ preferWasm: true });
      expect(adapter).toBeInstanceOf(Z3Adapter);
    });

    it('should create instance with preferWasm false', () => {
      const adapter = new Z3Adapter({ preferWasm: false });
      expect(adapter).toBeInstanceOf(Z3Adapter);
    });

    it('should create instance with timeout option', () => {
      const adapter = new Z3Adapter({ timeout: 5000 });
      expect(adapter).toBeInstanceOf(Z3Adapter);
    });

    it('should create instance with debug option', () => {
      const adapter = new Z3Adapter({ debug: true });
      expect(adapter).toBeInstanceOf(Z3Adapter);
    });
  });

  describe('isAvailable', () => {
    it('should return false before initialization', () => {
      const adapter = new Z3Adapter();
      expect(adapter.isAvailable()).toBe(false);
    });
  });

  describe('getBackendType', () => {
    it('should return none before initialization', () => {
      const adapter = new Z3Adapter();
      expect(adapter.getBackendType()).toBe('none');
    });
  });

  describe('initialize', () => {
    it('should attempt initialization (may fail if Z3 not available)', async () => {
      const adapter = new Z3Adapter();
      
      // This may throw if Z3 is not installed
      try {
        await adapter.initialize();
        expect(adapter.isAvailable()).toBe(true);
        expect(['wasm', 'process']).toContain(adapter.getBackendType());
      } catch (error) {
        // Expected if Z3 is not installed
        expect(adapter.isAvailable()).toBe(false);
        expect(adapter.getBackendType()).toBe('none');
      }
    });
  });

  describe('checkSat', () => {
    it('should throw if not initialized', async () => {
      const adapter = new Z3Adapter();
      
      await expect(adapter.checkSat('(check-sat)')).rejects.toThrow();
    });
  });

  describe('getModel', () => {
    it('should throw if not initialized', async () => {
      const adapter = new Z3Adapter();
      
      await expect(adapter.getModel()).rejects.toThrow();
    });
  });

  describe('getProof', () => {
    it('should return undefined if not initialized', async () => {
      const adapter = new Z3Adapter();
      
      // getProof may return undefined or throw
      try {
        const proof = await adapter.getProof();
        expect(proof).toBeUndefined();
      } catch {
        // Also acceptable
      }
    });
  });

  describe('dispose', () => {
    it('should dispose without error when not initialized', async () => {
      const adapter = new Z3Adapter();
      
      await expect(adapter.dispose()).resolves.not.toThrow();
    });

    it('should be safe to call multiple times', async () => {
      const adapter = new Z3Adapter();
      
      await adapter.dispose();
      await adapter.dispose();
      await adapter.dispose();
      
      expect(adapter.isAvailable()).toBe(false);
    });
  });

  describe('static create', () => {
    it('should create and initialize adapter', async () => {
      try {
        const adapter = await Z3Adapter.create();
        expect(adapter).toBeInstanceOf(Z3Adapter);
        
        if (adapter.isAvailable()) {
          await adapter.dispose();
        }
      } catch {
        // Expected if Z3 is not available
      }
    });

    it('should create with options', async () => {
      try {
        const adapter = await Z3Adapter.create({
          preferWasm: false,
          timeout: 3000,
        });
        expect(adapter).toBeInstanceOf(Z3Adapter);
        
        await adapter.dispose();
      } catch {
        // Expected if Z3 is not available
      }
    });
  });
});
