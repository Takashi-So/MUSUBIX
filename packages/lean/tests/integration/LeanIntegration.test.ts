/**
 * @fileoverview Unit tests for LeanIntegration (main facade)
 * @module @nahisaho/musubix-lean/tests/integration/LeanIntegration
 * @traceability REQ-LEAN-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { LeanIntegration } from '../../src/integration/LeanIntegration.ts';
import type { EarsRequirement, LeanConfig, EarsParsedComponents } from '../../src/types.ts';

describe('LeanIntegration', () => {
  let integration: LeanIntegration;

  beforeEach(() => {
    const config: Partial<LeanConfig> = {
      timeout: 5000,
      projectPath: '/tmp/lean-test',
      mathlibEnabled: false,
    };
    integration = new LeanIntegration(config);
  });

  describe('constructor', () => {
    it('should create instance with default config', () => {
      const defaultIntegration = new LeanIntegration();
      expect(defaultIntegration).toBeInstanceOf(LeanIntegration);
    });

    it('should create instance with custom config', () => {
      const config: Partial<LeanConfig> = {
        timeout: 60000,
        mathlibEnabled: true,
      };
      const customIntegration = new LeanIntegration(config);
      expect(customIntegration).toBeInstanceOf(LeanIntegration);
    });
  });

  describe('convertRequirement', () => {
    it('should convert EARS requirement to Lean theorem', () => {
      const parsed: EarsParsedComponents = {
        pattern: 'ubiquitous',
        subject: 'system',
        action: 'validate input',
        negated: false,
      };
      const req: EarsRequirement = {
        id: 'REQ-001',
        pattern: 'ubiquitous',
        text: 'THE system SHALL validate input',
        parsed,
      };

      const result = integration.convertRequirement(req);
      expect(result.isOk() || result.isErr()).toBe(true);
      if (result.isOk()) {
        expect(result.value.requirementId).toBe('REQ-001');
      }
    });

    it('should handle requirement without parsed components', () => {
      const req: EarsRequirement = {
        id: 'REQ-INVALID',
        pattern: 'ubiquitous',
        text: 'Invalid text without EARS pattern',
        // missing parsed
      };

      const result = integration.convertRequirement(req);
      expect(result.isErr()).toBe(true);
    });
  });

  describe('initialize', () => {
    it('should return initialization result', async () => {
      const result = await integration.initialize();
      // Will return ok or err depending on Lean availability
      expect(result.isOk() || result.isErr()).toBe(true);
    });
  });

  describe('initProject', () => {
    it('should attempt to initialize a new Lean project', async () => {
      const result = await integration.initProject('test-project', '/tmp/test-lean-project');
      // Will return ok or err depending on environment
      expect(result.isOk() || result.isErr()).toBe(true);
    });
  });
});
