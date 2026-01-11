import { describe, it, expect, beforeEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  createPolicyEngine,
  PolicyEngine,
  Policy,
  constitutionPolicies,
  ValidationContext,
} from '../src/index.js';

describe('@musubix/policy', () => {
  let engine: PolicyEngine;

  beforeEach(() => {
    engine = createPolicyEngine() as PolicyEngine;
  });

  describe('createPolicyEngine', () => {
    it('should create a PolicyEngine instance', () => {
      expect(engine).toBeInstanceOf(PolicyEngine);
    });

    it('should register built-in constitution policies', () => {
      const policies = engine.listPolicies('constitution');
      expect(policies.length).toBe(9);
    });
  });

  describe('Policy Management', () => {
    it('should register a custom policy', () => {
      const customPolicy: Policy = {
        id: 'CUSTOM-001',
        name: 'Custom Policy',
        description: 'Test policy',
        severity: 'warning',
        category: 'custom',
        validate: async () => ({ passed: true, violations: [] }),
      };

      engine.registerPolicy(customPolicy);
      const policy = engine.getPolicy('CUSTOM-001');
      expect(policy).toBeDefined();
      expect(policy?.name).toBe('Custom Policy');
    });

    it('should list policies by category', () => {
      const constitutionPolicies = engine.listPolicies('constitution');
      expect(constitutionPolicies.every(p => p.category === 'constitution')).toBe(true);
    });

    it('should list all policies when no category specified', () => {
      const allPolicies = engine.listPolicies();
      expect(allPolicies.length).toBeGreaterThanOrEqual(9);
    });
  });

  describe('Validation', () => {
    it('should validate and return report', async () => {
      const context: ValidationContext = {};
      const report = await engine.validate(context);

      expect(report).toHaveProperty('passed');
      expect(report).toHaveProperty('totalPolicies');
      expect(report).toHaveProperty('violations');
      expect(report).toHaveProperty('timestamp');
    });

    it('should run only specified policies', async () => {
      const context: ValidationContext = {};
      const report = await engine.validate(context, ['CONST-001']);

      expect(report.totalPolicies).toBe(1);
    });

    it('should skip disabled policies', async () => {
      const engineWithConfig = createPolicyEngine({
        config: { disabled: ['CONST-001'] },
      });

      const context: ValidationContext = {};
      const report = await engineWithConfig.validate(context);

      expect(report.violations.find(v => v.policyId === 'CONST-001')).toBeUndefined();
    });
  });

  describe('Constitution Policies', () => {
    let tempDir: string;

    beforeEach(async () => {
      tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'policy-test-'));
    });

    afterEach(async () => {
      await fs.rm(tempDir, { recursive: true, force: true });
    });

    describe('CONST-001: Library-First', () => {
      it('should pass when packages/ exists', async () => {
        await fs.mkdir(path.join(tempDir, 'packages'));

        const policy = engine.getPolicy('CONST-001')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });

      it('should fail when packages/ does not exist', async () => {
        const policy = engine.getPolicy('CONST-001')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(false);
        expect(result.violations[0].policyId).toBe('CONST-001');
      });
    });

    describe('CONST-002: CLI Interface', () => {
      it('should pass when bin/ exists', async () => {
        await fs.mkdir(path.join(tempDir, 'bin'));
        await fs.writeFile(path.join(tempDir, 'package.json'), '{}');

        const policy = engine.getPolicy('CONST-002')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });

      it('should pass when package.json has bin field', async () => {
        await fs.writeFile(
          path.join(tempDir, 'package.json'),
          JSON.stringify({ bin: { test: './bin/test.js' } })
        );

        const policy = engine.getPolicy('CONST-002')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });
    });

    describe('CONST-003: Test-First', () => {
      it('should pass when __tests__ exists', async () => {
        await fs.mkdir(path.join(tempDir, '__tests__'));

        const policy = engine.getPolicy('CONST-003')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });

      it('should pass when .test.ts files exist', async () => {
        await fs.writeFile(path.join(tempDir, 'index.test.ts'), '');

        const policy = engine.getPolicy('CONST-003')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });
    });

    describe('CONST-004: EARS Format', () => {
      it('should pass for files with EARS patterns', async () => {
        const content = 'THE system SHALL validate user input';
        
        const policy = engine.getPolicy('CONST-004')!;
        const result = await policy.validate({
          filePath: 'REQ-001.md',
          content,
        });

        expect(result.passed).toBe(true);
      });

      it('should fail for requirement files without EARS', async () => {
        const content = 'The system should validate user input';
        
        const policy = engine.getPolicy('CONST-004')!;
        const result = await policy.validate({
          filePath: 'REQ-001.md',
          content,
        });

        expect(result.passed).toBe(false);
      });

      it('should pass for non-requirement files', async () => {
        const content = 'Some random content';
        
        const policy = engine.getPolicy('CONST-004')!;
        const result = await policy.validate({
          filePath: 'readme.md',
          content,
        });

        expect(result.passed).toBe(true);
      });
    });

    describe('CONST-005: Traceability', () => {
      it('should pass when storage/traceability exists', async () => {
        await fs.mkdir(path.join(tempDir, 'storage', 'traceability'), { recursive: true });

        const policy = engine.getPolicy('CONST-005')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });
    });

    describe('CONST-006: Project Memory', () => {
      it('should pass when steering/ exists', async () => {
        await fs.mkdir(path.join(tempDir, 'steering'));

        const policy = engine.getPolicy('CONST-006')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });
    });

    describe('CONST-007: Design Patterns', () => {
      it('should pass when storage/design exists', async () => {
        await fs.mkdir(path.join(tempDir, 'storage', 'design'), { recursive: true });

        const policy = engine.getPolicy('CONST-007')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });
    });

    describe('CONST-008: Decision Records', () => {
      it('should pass when docs/decisions exists', async () => {
        await fs.mkdir(path.join(tempDir, 'docs', 'decisions'), { recursive: true });

        const policy = engine.getPolicy('CONST-008')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });
    });

    describe('CONST-009: Quality Gates', () => {
      it('should pass when .github/workflows exists', async () => {
        await fs.mkdir(path.join(tempDir, '.github', 'workflows'), { recursive: true });

        const policy = engine.getPolicy('CONST-009')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });

      it('should pass when vitest.config.ts exists', async () => {
        await fs.writeFile(path.join(tempDir, 'vitest.config.ts'), '');

        const policy = engine.getPolicy('CONST-009')!;
        const result = await policy.validate({ projectPath: tempDir });

        expect(result.passed).toBe(true);
      });
    });
  });

  describe('Fix', () => {
    it('should return empty array when no fix functions', async () => {
      const context: ValidationContext = {};
      const results = await engine.fix(context);

      // Built-in policies don't have fix functions
      expect(results).toHaveLength(0);
    });

    it('should call fix function when available', async () => {
      const customPolicy: Policy = {
        id: 'CUSTOM-FIX',
        name: 'Fixable Policy',
        description: 'Policy with fix',
        severity: 'warning',
        category: 'custom',
        validate: async () => ({ passed: false, violations: [] }),
        fix: async () => ({ fixed: true, changes: [] }),
      };

      engine.registerPolicy(customPolicy);
      const results = await engine.fix({}, ['CUSTOM-FIX']);

      expect(results).toHaveLength(1);
      expect(results[0].fixed).toBe(true);
    });
  });
});
