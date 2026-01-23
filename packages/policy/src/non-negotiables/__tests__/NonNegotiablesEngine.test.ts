/**
 * NonNegotiablesEngine Unit Tests
 *
 * @see TSK-FR-007〜012 - NonNegotiablesEngine
 * @see REQ-FR-020〜023 - NonNegotiablesEngine
 * @trace DES-MUSUBIX-FR-001 DES-POLICY-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  NonNegotiablesEngine,
  createNonNegotiablesEngine,
  type INonNegotiablesEngine,
} from '../NonNegotiablesEngine.js';
import {
  type NonNegotiableRule,
  type ValidationContext,
  createNonNegotiableRule,
  DEFAULT_NON_NEGOTIABLE_RULES,
} from '../types.js';

describe('NonNegotiablesEngine', () => {
  let engine: INonNegotiablesEngine;

  beforeEach(() => {
    engine = createNonNegotiablesEngine();
  });

  describe('createNonNegotiableRule', () => {
    it('should create a rule with default enabled=true', () => {
      const rule = createNonNegotiableRule({
        id: 'TEST-001',
        name: 'Test Rule',
        description: 'A test rule',
        category: 'quality',
        severity: 'medium',
      });

      expect(rule.id).toBe('TEST-001');
      expect(rule.enabled).toBe(true);
    });

    it('should allow overriding enabled', () => {
      const rule = createNonNegotiableRule({
        id: 'TEST-002',
        name: 'Disabled Rule',
        description: 'A disabled rule',
        category: 'quality',
        severity: 'medium',
        enabled: false,
      });

      expect(rule.enabled).toBe(false);
    });
  });

  describe('DEFAULT_NON_NEGOTIABLE_RULES', () => {
    it('should contain security rules', () => {
      const securityRules = DEFAULT_NON_NEGOTIABLE_RULES.filter(
        r => r.category === 'security'
      );
      expect(securityRules.length).toBeGreaterThan(0);
    });

    it('should contain architecture rules', () => {
      const archRules = DEFAULT_NON_NEGOTIABLE_RULES.filter(
        r => r.category === 'architecture'
      );
      expect(archRules.length).toBeGreaterThan(0);
    });

    it('should contain quality rules', () => {
      const qualityRules = DEFAULT_NON_NEGOTIABLE_RULES.filter(
        r => r.category === 'quality'
      );
      expect(qualityRules.length).toBeGreaterThan(0);
    });
  });

  describe('validateContent', () => {
    it('should pass for clean code', () => {
      const context: ValidationContext = {
        filePath: 'src/service.ts',
        content: `
          export function processData(input: string): string {
            return input.trim();
          }
        `,
      };

      const report = engine.validateContent(context);

      expect(report.passed).toBe(true);
      expect(report.violations).toHaveLength(0);
    });

    it('should detect hardcoded secrets', () => {
      const context: ValidationContext = {
        filePath: 'src/config.ts',
        content: `
          const apiKey = "sk-1234567890abcdef";
          const password = "supersecret123";
        `,
      };

      const report = engine.validateContent(context);

      expect(report.passed).toBe(false);
      expect(report.violations.some(v => v.rule.id === 'NN-SEC-001')).toBe(true);
    });

    it('should detect console.log statements', () => {
      const context: ValidationContext = {
        filePath: 'src/utils.ts',
        content: `
          export function debug(msg: string) {
            console.log(msg);
          }
        `,
      };

      const report = engine.validateContent(context);

      expect(report.violations.some(v => v.rule.id === 'NN-QUAL-001')).toBe(true);
    });

    it('should detect TODO/FIXME comments', () => {
      const context: ValidationContext = {
        filePath: 'src/handler.ts',
        content: `
          // TODO: Implement proper error handling
          export function handle() {}
        `,
      };

      const report = engine.validateContent(context);

      expect(report.violations.some(v => v.rule.id === 'NN-QUAL-002')).toBe(true);
    });

    it('should count violations by severity', () => {
      const context: ValidationContext = {
        filePath: 'src/bad-code.ts',
        content: `
          const password = "hardcoded123";
          console.log("debug");
          // TODO: Fix this
        `,
      };

      const report = engine.validateContent(context);

      expect(report.counts.total).toBeGreaterThan(0);
      expect(report.counts.critical + report.counts.high + report.counts.medium).toBe(
        report.counts.total
      );
    });
  });

  describe('validateDesignArtifacts', () => {
    it('should pass for valid design artifacts', async () => {
      const artifacts = [
        {
          type: 'design',
          content: 'Valid design document content',
          id: 'DES-001',
        },
      ];

      const result = await engine.validateDesignArtifacts(artifacts as any);

      expect(result.passed).toBe(true);
    });

    it('should return violations for invalid artifacts', async () => {
      const artifacts = [
        {
          type: 'design',
          content: 'Design with password = "secret123" hardcoded',
          id: 'DES-002',
        },
      ];

      const result = await engine.validateDesignArtifacts(artifacts as any);

      expect(result.passed).toBe(false);
      expect(result.violations.length).toBeGreaterThan(0);
    });
  });

  describe('validateImplementation', () => {
    it('should pass for valid file list', async () => {
      const changedFiles = ['src/service.ts', 'src/handler.ts'];

      // This test validates the interface, actual file reading would be mocked
      const result = await engine.validateImplementation(changedFiles);

      // Without actual file content, validation passes
      expect(result.passed).toBe(true);
    });
  });

  describe('getRules', () => {
    it('should return all registered rules', () => {
      const rules = engine.getRules();

      expect(rules.length).toBe(DEFAULT_NON_NEGOTIABLE_RULES.length);
    });

    it('should return filtered rules by category', () => {
      const securityRules = engine.getRules('security');

      expect(securityRules.every(r => r.category === 'security')).toBe(true);
    });
  });

  describe('getEnabledRules', () => {
    it('should return only enabled rules', () => {
      const enabledRules = engine.getEnabledRules();

      expect(enabledRules.every(r => r.enabled)).toBe(true);
    });
  });

  describe('custom rules', () => {
    it('should support custom rules', () => {
      const customRule = createNonNegotiableRule({
        id: 'CUSTOM-001',
        name: 'Custom Rule',
        description: 'A custom validation rule',
        category: 'quality',
        severity: 'high',
        pattern: /FORBIDDEN_PATTERN/,
      });

      const customEngine = createNonNegotiablesEngine({
        rules: [...DEFAULT_NON_NEGOTIABLE_RULES, customRule],
      });

      const context: ValidationContext = {
        filePath: 'src/test.ts',
        content: 'const x = FORBIDDEN_PATTERN;',
      };

      const report = customEngine.validateContent(context);

      expect(report.violations.some(v => v.rule.id === 'CUSTOM-001')).toBe(true);
    });
  });

  describe('failFast mode', () => {
    it('should stop on first violation when failFast is true', () => {
      const failFastEngine = createNonNegotiablesEngine({
        rules: DEFAULT_NON_NEGOTIABLE_RULES,
        failFast: true,
      });

      const context: ValidationContext = {
        filePath: 'src/multi-violation.ts',
        content: `
          const password = "secret123";
          console.log("debug");
          // TODO: Fix
        `,
      };

      const report = failFastEngine.validateContent(context);

      // Should stop after first violation
      expect(report.violations.length).toBe(1);
    });
  });
});
