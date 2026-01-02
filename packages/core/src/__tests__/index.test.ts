/**
 * @musubix/core - Basic Tests
 */
import { describe, it, expect } from 'vitest';

describe('@musubix/core', () => {
  describe('Package Export', () => {
    it('should export VERSION', async () => {
      const { VERSION } = await import('../index.js');
      expect(VERSION).toBeDefined();
      expect(typeof VERSION).toBe('string');
    });

    it('should export core modules', async () => {
      const core = await import('../index.js');
      
      // Check that exports exist
      expect(core).toBeDefined();
      expect(Object.keys(core).length).toBeGreaterThan(0);
    });
  });

  describe('Version', () => {
    it('should have valid semver format', async () => {
      const { VERSION } = await import('../index.js');
      const semverPattern = /^\d+\.\d+\.\d+(-[\w.]+)?$/;
      expect(VERSION).toMatch(semverPattern);
    });
  });
});
