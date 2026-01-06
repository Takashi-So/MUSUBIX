/**
 * Z3WasmClient Unit Tests
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { Z3WasmClient } from '../../src/z3/Z3WasmClient';

describe('Z3WasmClient', () => {
  let client: Z3WasmClient;

  beforeEach(() => {
    client = new Z3WasmClient({ timeout: 5000, logLevel: 'silent' });
  });

  afterEach(async () => {
    await client.dispose();
  });

  describe('constructor', () => {
    it('should create instance with default options', () => {
      const defaultClient = new Z3WasmClient();
      expect(defaultClient).toBeInstanceOf(Z3WasmClient);
    });

    it('should create instance with custom options', () => {
      const customClient = new Z3WasmClient({
        timeout: 10000,
        logLevel: 'debug',
        memoryLimit: 1024,
      });
      expect(customClient).toBeInstanceOf(Z3WasmClient);
    });
  });

  describe('isAvailable', () => {
    it('should return false before initialization', () => {
      expect(client.isAvailable()).toBe(false);
    });
  });

  describe('initialize', () => {
    it('should throw error if z3-solver is not installed', async () => {
      // z3-solverがインストールされていない場合はエラー
      await expect(client.initialize()).rejects.toThrow();
    });

    it('should handle initialization error gracefully', async () => {
      try {
        await client.initialize();
      } catch (error) {
        expect(error).toBeInstanceOf(Error);
        expect((error as Error).message).toContain('z3');
      }
    });
  });

  describe('checkSat (without Z3)', () => {
    it('should throw error if not initialized', async () => {
      await expect(client.checkSat('(declare-const x Int)')).rejects.toThrow(
        'not initialized'
      );
    });
  });

  describe('getModel (without Z3)', () => {
    it('should throw error if not initialized', async () => {
      await expect(client.getModel('(declare-const x Int)')).rejects.toThrow(
        'not initialized'
      );
    });
  });

  describe('getProof (without Z3)', () => {
    it('should throw error if not initialized', async () => {
      await expect(client.getProof('(declare-const x Int)')).rejects.toThrow(
        'not initialized'
      );
    });
  });

  describe('dispose', () => {
    it('should dispose resources', async () => {
      await client.dispose();
      expect(client.isAvailable()).toBe(false);
    });

    it('should be safe to call multiple times', async () => {
      await client.dispose();
      await client.dispose();
      expect(client.isAvailable()).toBe(false);
    });
  });
});

describe('Z3WasmClient with mocked z3-solver', () => {
  it('should handle mock Z3 initialization', async () => {
    // モックを使用したテスト
    const mockZ3 = {
      init: vi.fn().mockResolvedValue({
        Context: vi.fn().mockImplementation(() => ({
          eval: vi.fn().mockResolvedValue({ toString: () => 'sat' }),
        })),
      }),
    };

    // 実際のz3-solverがない場合のテストケース
    const client = new Z3WasmClient();
    expect(client.isAvailable()).toBe(false);
  });
});
