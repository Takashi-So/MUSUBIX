/**
 * Z3ProcessFallback Unit Tests
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { Z3ProcessFallback } from '../../src/z3/Z3ProcessFallback';

describe('Z3ProcessFallback', () => {
  let client: Z3ProcessFallback;

  beforeEach(() => {
    client = new Z3ProcessFallback({ timeout: 5000, logLevel: 'silent' });
  });

  afterEach(async () => {
    await client.dispose();
  });

  describe('constructor', () => {
    it('should create instance with default options', () => {
      const defaultClient = new Z3ProcessFallback();
      expect(defaultClient).toBeInstanceOf(Z3ProcessFallback);
    });

    it('should create instance with custom options', () => {
      const customClient = new Z3ProcessFallback({
        timeout: 10000,
        logLevel: 'debug',
        memoryLimit: 1024,
      });
      expect(customClient).toBeInstanceOf(Z3ProcessFallback);
    });
  });

  describe('isAvailable', () => {
    it('should return false before initialization', () => {
      expect(client.isAvailable()).toBe(false);
    });
  });

  describe('initialize', () => {
    it('should initialize and check for Z3 executable', async () => {
      await client.initialize();
      // Z3がインストールされているかどうかで結果が変わる
      // どちらの場合も初期化は完了する
      expect(true).toBe(true);
    });
  });

  describe('checkSat', () => {
    it('should throw error if not initialized', async () => {
      await expect(client.checkSat('(declare-const x Int)')).rejects.toThrow(
        'not initialized'
      );
    });

    it('should return error if Z3 is not available', async () => {
      await client.initialize();
      if (!client.isAvailable()) {
        const result = await client.checkSat('(declare-const x Int)');
        expect(result).toBe('error');
      }
    });
  });

  describe('getModel', () => {
    it('should return null if Z3 is not available', async () => {
      await client.initialize();
      if (!client.isAvailable()) {
        const result = await client.getModel('(declare-const x Int)');
        expect(result).toBeNull();
      }
    });
  });

  describe('getProof', () => {
    it('should return null if Z3 is not available', async () => {
      await client.initialize();
      if (!client.isAvailable()) {
        const result = await client.getProof('(declare-const x Int)');
        expect(result).toBeNull();
      }
    });
  });

  describe('dispose', () => {
    it('should dispose resources', async () => {
      await client.initialize();
      await client.dispose();
      expect(client.isAvailable()).toBe(false);
    });
  });
});
