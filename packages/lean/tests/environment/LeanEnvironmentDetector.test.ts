/**
 * @fileoverview Unit tests for LeanEnvironmentDetector
 * @module @nahisaho/musubix-lean/tests/environment/LeanEnvironmentDetector
 * @traceability REQ-LEAN-CORE-001
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  validateLeanVersion,
  clearEnvironmentCache,
  LeanEnvironmentDetector,
} from '../../src/environment/LeanEnvironmentDetector.ts';
import { getInstallInstructions } from '../../src/errors.ts';

describe('LeanEnvironmentDetector', () => {
  beforeEach(() => {
    clearEnvironmentCache();
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('validateLeanVersion', () => {
    it('should validate version meets minimum', () => {
      const version = { major: 4, minor: 3, patch: 0, full: '4.3.0' };
      const result = validateLeanVersion(version, '4.0.0');
      expect(result).toBe(true);
    });

    it('should reject version below minimum', () => {
      const version = { major: 3, minor: 9, patch: 0, full: '3.9.0' };
      const result = validateLeanVersion(version, '4.0.0');
      expect(result).toBe(false);
    });

    it('should handle patch version differences', () => {
      const version = { major: 4, minor: 0, patch: 1, full: '4.0.1' };
      const result = validateLeanVersion(version, '4.0.0');
      expect(result).toBe(true);
    });

    it('should return false for null version', () => {
      const result = validateLeanVersion(null, '4.0.0');
      expect(result).toBe(false);
    });

    it('should handle equal versions', () => {
      const version = { major: 4, minor: 0, patch: 0, full: '4.0.0' };
      const result = validateLeanVersion(version, '4.0.0');
      expect(result).toBe(true);
    });

    it('should handle minor version greater', () => {
      const version = { major: 4, minor: 5, patch: 0, full: '4.5.0' };
      const result = validateLeanVersion(version, '4.3.0');
      expect(result).toBe(true);
    });

    it('should handle minor version less', () => {
      const version = { major: 4, minor: 1, patch: 0, full: '4.1.0' };
      const result = validateLeanVersion(version, '4.3.0');
      expect(result).toBe(false);
    });
  });

  describe('LeanEnvironmentDetector class', () => {
    it('should create instance', () => {
      const detector = new LeanEnvironmentDetector();
      expect(detector).toBeDefined();
    });

    it('should return false for validateVersion before detect', () => {
      const detector = new LeanEnvironmentDetector();
      // No detection performed, should return false
      expect(detector.validateVersion('4.0.0')).toBe(false);
    });

    it('should get install instructions for linux', () => {
      const detector = new LeanEnvironmentDetector();
      const instructions = detector.getInstallInstructions('linux');
      expect(instructions).toContain('elan');
    });

    it('should get install instructions for macos', () => {
      const detector = new LeanEnvironmentDetector();
      const instructions = detector.getInstallInstructions('macos');
      expect(instructions).toContain('elan');
    });

    it('should get install instructions for windows', () => {
      const detector = new LeanEnvironmentDetector();
      const instructions = detector.getInstallInstructions('windows');
      expect(instructions).toBeDefined();
    });

    it('should clear cache', () => {
      const detector = new LeanEnvironmentDetector();
      // This should not throw
      expect(() => detector.clearCache()).not.toThrow();
    });
  });

  describe('clearEnvironmentCache', () => {
    it('should clear global cache without error', () => {
      expect(() => clearEnvironmentCache()).not.toThrow();
    });
  });

  describe('getInstallInstructions', () => {
    it('should return instructions for linux', () => {
      const instructions = getInstallInstructions('linux');
      expect(instructions).toContain('elan');
    });

    it('should return instructions for darwin (macOS)', () => {
      const instructions = getInstallInstructions('darwin');
      expect(instructions).toContain('elan');
    });

    it('should return instructions for win32 (Windows)', () => {
      const instructions = getInstallInstructions('win32');
      expect(instructions).toBeDefined();
    });

    it('should return generic instructions for unknown OS', () => {
      const instructions = getInstallInstructions('freebsd');
      expect(instructions).toBeDefined();
    });
  });
});
