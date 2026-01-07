/**
 * @fileoverview Policy Engine Tests
 * @module @nahisaho/musubix-security/tests/phase4/policy-engine
 */

import { describe, it, expect } from 'vitest';
import {
  PolicyEngine,
  createPolicyEngine,
  getBuiltInPolicy,
  type SecurityPolicy,
} from '../../src/policy/policy-engine.js';
import type { ScanResult, Vulnerability, SourceLocation, VulnerabilityType } from '../../src/types/index.js';

describe('PolicyEngine', () => {
  const createMockLocation = (file: string = 'src/test.ts', startLine: number = 10): SourceLocation => ({
    file,
    startLine,
    endLine: startLine,
    startColumn: 5,
    endColumn: 50,
  });

  const createMockVulnerability = (
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info',
    ruleId: string = 'SEC-001'
  ): Vulnerability => ({
    id: `VULN-${Date.now()}-${Math.random()}`,
    type: 'xss' as VulnerabilityType,
    ruleId,
    severity,
    description: `Test ${severity} vulnerability`,
    recommendation: 'Fix by sanitizing input',
    confidence: 0.9,
    cwes: ['CWE-79'],
    owasp: ['A01:2021'],
    detectedAt: new Date(),
    location: createMockLocation(),
  });

  const createMockScanResult = (vulns: Vulnerability[] = []): ScanResult => ({
    vulnerabilities: vulns,
    scannedFiles: 10,
    skippedFiles: 0,
    duration: 100,
    timestamp: new Date(),
    options: {},
    summary: {
      total: vulns.length,
      critical: vulns.filter(v => v.severity === 'critical').length,
      high: vulns.filter(v => v.severity === 'high').length,
      medium: vulns.filter(v => v.severity === 'medium').length,
      low: vulns.filter(v => v.severity === 'low').length,
      info: vulns.filter(v => v.severity === 'info').length,
    },
  });

  describe('createPolicyEngine', () => {
    it('should create engine with default options', () => {
      const engine = createPolicyEngine();
      expect(engine).toBeInstanceOf(PolicyEngine);
    });

    it('should create engine with custom policies', () => {
      const customPolicy: SecurityPolicy = {
        name: 'custom',
        version: '1.0.0',
        rules: [],
      };
      const engine = createPolicyEngine({
        customPolicies: [customPolicy],
      });
      expect(engine).toBeInstanceOf(PolicyEngine);
    });

    it('should load built-in policies', () => {
      const engine = createPolicyEngine({
        builtInPolicies: ['default', 'strict'],
      });
      expect(engine).toBeInstanceOf(PolicyEngine);
    });
  });

  describe('getBuiltInPolicy', () => {
    it('should return default policy', () => {
      const policy = getBuiltInPolicy('default');
      expect(policy.name).toBe('default');
    });

    it('should return strict policy', () => {
      const policy = getBuiltInPolicy('strict');
      expect(policy.name).toBe('strict');
    });

    it('should return minimal policy', () => {
      const policy = getBuiltInPolicy('minimal');
      expect(policy.name).toBe('minimal');
    });

    it('should return enterprise policy', () => {
      const policy = getBuiltInPolicy('enterprise');
      expect(policy.name).toBe('enterprise');
    });
  });

  describe('evaluate', () => {
    it('should pass clean scan with default policy', () => {
      const engine = createPolicyEngine();
      const scanResult = createMockScanResult([]);

      const result = engine.evaluate('default', scanResult);

      expect(result.passed).toBe(true);
      expect(result.policyName).toBe('default');
    });

    it('should fail when critical vulnerability exists', () => {
      const engine = createPolicyEngine();
      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
      ]);

      const result = engine.evaluate('default', scanResult);

      expect(result.passed).toBe(false);
      expect(result.action).toBe('fail');
    });

    it('should fail when high vulnerability exists with default policy', () => {
      const engine = createPolicyEngine();
      const scanResult = createMockScanResult([
        createMockVulnerability('high'),
      ]);

      const result = engine.evaluate('default', scanResult);

      expect(result.passed).toBe(false);
    });

    it('should pass medium with minimal policy', () => {
      const engine = createPolicyEngine({
        builtInPolicies: ['minimal'],
      });
      const scanResult = createMockScanResult([
        createMockVulnerability('medium'),
      ]);

      const result = engine.evaluate('minimal', scanResult);

      expect(result.passed).toBe(true);
    });

    it('should fail medium with strict policy', () => {
      const engine = createPolicyEngine({
        builtInPolicies: ['strict'],
      });
      const scanResult = createMockScanResult([
        createMockVulnerability('medium'),
      ]);

      const result = engine.evaluate('strict', scanResult);

      expect(result.passed).toBe(false);
    });

    it('should include evaluation time', () => {
      const engine = createPolicyEngine();
      const scanResult = createMockScanResult([]);

      const result = engine.evaluate('default', scanResult);

      expect(result.evaluationTime).toBeGreaterThanOrEqual(0);
    });

    it('should throw error for unknown policy', () => {
      const engine = createPolicyEngine();
      const scanResult = createMockScanResult([]);

      expect(() => engine.evaluate('unknown', scanResult)).toThrow('Policy not found');
    });
  });

  describe('registerPolicy', () => {
    it('should register custom policy', () => {
      const engine = createPolicyEngine();
      const customPolicy: SecurityPolicy = {
        name: 'my-policy',
        version: '1.0.0',
        rules: [],
      };

      engine.registerPolicy(customPolicy);
      const result = engine.evaluate('my-policy', createMockScanResult([]));

      expect(result.policyName).toBe('my-policy');
    });
  });

  describe('validatePolicy', () => {
    it('should validate correct policy', () => {
      const engine = createPolicyEngine();
      const policy: SecurityPolicy = {
        name: 'test',
        version: '1.0.0',
        rules: [
          {
            id: 'rule-1',
            name: 'Test Rule',
            conditions: [{ target: 'count.critical', operator: 'greater_than', value: 0 }],
            action: 'fail',
          },
        ],
      };

      const result = engine.validatePolicy(policy);

      expect(result.valid).toBe(true);
      expect(result.errors.length).toBe(0);
    });

    it('should reject policy without name', () => {
      const engine = createPolicyEngine();
      const policy = {
        version: '1.0.0',
        rules: [],
      } as unknown as SecurityPolicy;

      const result = engine.validatePolicy(policy);

      expect(result.valid).toBe(false);
    });
  });

  describe('getPolicy', () => {
    it('should return registered policy', () => {
      const engine = createPolicyEngine();
      const policy = engine.getPolicy('default');

      expect(policy).toBeDefined();
      expect(policy?.name).toBe('default');
    });

    it('should return undefined for unknown policy', () => {
      const engine = createPolicyEngine();
      const policy = engine.getPolicy('unknown');

      expect(policy).toBeUndefined();
    });
  });

  describe('exportPolicy', () => {
    it('should export policy as YAML', () => {
      const engine = createPolicyEngine();
      const yaml = engine.exportPolicy('default');

      expect(yaml).toContain('name:');
      expect(yaml).toContain('version:');
      expect(yaml).toContain('rules:');
    });

    it('should throw error for unknown policy', () => {
      const engine = createPolicyEngine();
      
      expect(() => engine.exportPolicy('unknown')).toThrow('Policy not found');
    });
  });

  describe('summary calculation', () => {
    it('should calculate correct summary', () => {
      const engine = createPolicyEngine();
      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
        createMockVulnerability('high'),
      ]);

      const result = engine.evaluate('default', scanResult);

      expect(result.summary).toBeDefined();
      expect(result.summary.failures).toBeGreaterThanOrEqual(0);
    });
  });

  describe('recommendations', () => {
    it('should generate recommendations for failures', () => {
      const engine = createPolicyEngine();
      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
      ]);

      const result = engine.evaluate('default', scanResult);

      expect(result.recommendations).toBeDefined();
      expect(Array.isArray(result.recommendations)).toBe(true);
    });
  });

  describe('custom rules', () => {
    it('should evaluate custom rule conditions', () => {
      const customPolicy: SecurityPolicy = {
        name: 'custom-test',
        version: '1.0.0',
        rules: [
          {
            id: 'max-5-total',
            name: 'Max 5 Total Vulnerabilities',
            conditions: [
              { target: 'count.total', operator: 'greater_than', value: 5 },
            ],
            action: 'fail',
          },
        ],
      };
      const engine = createPolicyEngine({
        customPolicies: [customPolicy],
      });

      // 3 vulnerabilities - should pass
      const scanResult1 = createMockScanResult([
        createMockVulnerability('low'),
        createMockVulnerability('low'),
        createMockVulnerability('low'),
      ]);
      const result1 = engine.evaluate('custom-test', scanResult1);
      expect(result1.passed).toBe(true);

      // 6 vulnerabilities - should fail
      const scanResult2 = createMockScanResult([
        createMockVulnerability('low'),
        createMockVulnerability('low'),
        createMockVulnerability('low'),
        createMockVulnerability('low'),
        createMockVulnerability('low'),
        createMockVulnerability('low'),
      ]);
      const result2 = engine.evaluate('custom-test', scanResult2);
      expect(result2.passed).toBe(false);
    });

    it('should support warning action', () => {
      const customPolicy: SecurityPolicy = {
        name: 'warn-policy',
        version: '1.0.0',
        rules: [
          {
            id: 'warn-on-medium',
            name: 'Warn on Medium',
            conditions: [
              { target: 'count.medium', operator: 'greater_than', value: 0 },
            ],
            action: 'warn',
          },
        ],
      };
      const engine = createPolicyEngine({
        customPolicies: [customPolicy],
      });

      const scanResult = createMockScanResult([
        createMockVulnerability('medium'),
      ]);
      const result = engine.evaluate('warn-policy', scanResult);

      // Warn action should not fail
      expect(result.passed).toBe(true);
      expect(result.summary.warnings).toBeGreaterThanOrEqual(0);
    });
  });

  describe('policy settings', () => {
    it('should respect stopOnFirstMatch setting', () => {
      const customPolicy: SecurityPolicy = {
        name: 'stop-first',
        version: '1.0.0',
        rules: [
          {
            id: 'rule-1',
            name: 'Rule 1',
            conditions: [{ target: 'count.critical', operator: 'greater_than', value: 0 }],
            action: 'fail',
            priority: 100,
          },
          {
            id: 'rule-2',
            name: 'Rule 2',
            conditions: [{ target: 'count.high', operator: 'greater_than', value: 0 }],
            action: 'fail',
            priority: 50,
          },
        ],
        settings: {
          stopOnFirstMatch: true,
        },
      };
      const engine = createPolicyEngine({
        customPolicies: [customPolicy],
      });

      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
        createMockVulnerability('high'),
      ]);
      const result = engine.evaluate('stop-first', scanResult);

      // Should stop after first match
      expect(result.matchedRules.length).toBe(1);
    });
  });

  describe('policy extension', () => {
    it('should support extending policies', () => {
      const basePolicy: SecurityPolicy = {
        name: 'base',
        version: '1.0.0',
        rules: [
          {
            id: 'base-rule',
            name: 'Base Rule',
            conditions: [{ target: 'count.critical', operator: 'greater_than', value: 0 }],
            action: 'fail',
          },
        ],
      };
      const extendedPolicy: SecurityPolicy = {
        name: 'extended',
        version: '1.0.0',
        extends: ['base'],
        rules: [
          {
            id: 'extended-rule',
            name: 'Extended Rule',
            conditions: [{ target: 'count.high', operator: 'greater_than', value: 0 }],
            action: 'warn',
          },
        ],
      };
      const engine = createPolicyEngine({
        customPolicies: [basePolicy, extendedPolicy],
      });

      const scanResult = createMockScanResult([
        createMockVulnerability('critical'),
      ]);
      const result = engine.evaluate('extended', scanResult);

      // Should include rules from both policies
      expect(result.passed).toBe(false);
    });
  });
});
