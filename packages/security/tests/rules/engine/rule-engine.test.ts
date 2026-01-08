/**
 * @fileoverview Rule Engine Tests
 * @module @nahisaho/musubix-security/rules/engine/rule-engine.test
 * @trace TSK-RULE-001
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as os from 'node:os';
import { RuleEngine, createRuleEngine } from '../../../src/rules/engine/rule-engine.js';
import { RuleRegistry, createRegistry } from '../../../src/rules/engine/rule-registry.js';
import type { SecurityRule, RuleContext, RuleFinding, RuleConfig } from '../../../src/rules/types.js';

// Mock rule for testing
function createMockRule(overrides: Partial<SecurityRule> = {}): SecurityRule {
  return {
    id: 'test-rule-001',
    name: 'Test Rule',
    description: 'A test security rule',
    defaultSeverity: 'medium',
    detectionMethod: 'pattern-match',
    tags: ['test'],
    analyze: async (_context: RuleContext): Promise<RuleFinding[]> => [],
    ...overrides,
  };
}

// Default test config - no profile to ensure all registered rules run
const defaultConfig: RuleConfig = {
  profile: undefined,
  rules: {},
  exclude: ['**/node_modules/**'],
  include: ['**/*.ts'],
  severityThreshold: 'info',
  enableTaintAnalysis: false,
  enableDFG: false,
};

describe('RuleEngine', () => {
  let tempDir: string;
  let registry: RuleRegistry;
  let engine: RuleEngine;

  beforeEach(() => {
    // Create temp directory
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'rule-engine-test-'));
    
    // Create a test file
    fs.writeFileSync(
      path.join(tempDir, 'test.ts'),
      `const password = "secret123";
export function getPassword() {
  return password;
}`
    );

    // Create registry with test rule
    registry = createRegistry();
    engine = createRuleEngine({
      registry,
      projectRoot: tempDir,
    });
  });

  afterEach(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  describe('run', () => {
    it('should run rules against files and return results', async () => {
      const mockRule = createMockRule({
        id: 'test-rule',
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => {
          // Simple rule that detects "password" in source
          if (context.sourceCode.includes('password')) {
            return [{
              id: 'finding-1',
              ruleId: 'test-rule',
              severity: 'medium',
              message: 'Hardcoded password detected',
              location: {
                file: context.filePath,
                startLine: 1,
                startColumn: 6,
                endLine: 1,
                endColumn: 14,
              },
            }];
          }
          return [];
        },
      });
      
      registry.register(mockRule);
      
      const result = await engine.run(defaultConfig);
      
      expect(result.filesProcessed).toBe(1);
      expect(result.findings).toHaveLength(1);
      expect(result.findings[0].message).toBe('Hardcoded password detected');
    });

    it('should track progress', async () => {
      const mockRule = createMockRule();
      registry.register(mockRule);
      
      const progressEvents: any[] = [];
      const engineWithProgress = createRuleEngine({
        registry,
        projectRoot: tempDir,
        onProgress: (progress) => progressEvents.push({ ...progress }),
      });
      
      await engineWithProgress.run(defaultConfig);
      
      expect(progressEvents.length).toBeGreaterThan(0);
      expect(progressEvents.find(p => p.phase === 'init')).toBeDefined();
      expect(progressEvents.find(p => p.phase === 'complete')).toBeDefined();
    });

    it('should filter by severity threshold', async () => {
      const mockRule = createMockRule({
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => [{
          id: 'finding-1',
          ruleId: 'test-rule-001',
          severity: 'info',
          message: 'Info level finding',
          location: {
            file: context.filePath,
            startLine: 1,
                startColumn: 0,
            endLine: 1,
                endColumn: 10,
          },
        }],
      });
      
      registry.register(mockRule);
      
      const result = await engine.run({
        ...defaultConfig,
        severityThreshold: 'warning',
      });
      
      expect(result.findings).toHaveLength(0);
    });

    it('should respect rule enabled/disabled config', async () => {
      const mockRule = createMockRule({
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => [{
          id: 'finding-1',
          ruleId: 'test-rule-001',
          severity: 'medium',
          message: 'Test finding',
          location: {
            file: context.filePath,
            startLine: 1,
                startColumn: 0,
            endLine: 1,
                endColumn: 10,
          },
        }],
      });
      
      registry.register(mockRule);
      
      const result = await engine.run({
        ...defaultConfig,
        rules: {
          'test-rule-001': { enabled: false },
        },
      });
      
      expect(result.findings).toHaveLength(0);
    });

    it('should override severity from config', async () => {
      const mockRule = createMockRule({
        defaultSeverity: 'info',
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => [{
          id: 'finding-1',
          ruleId: 'test-rule-001',
          severity: 'info',
          message: 'Test finding',
          location: {
            file: context.filePath,
            startLine: 1,
                startColumn: 0,
            endLine: 1,
                endColumn: 10,
          },
        }],
      });
      
      registry.register(mockRule);
      
      const result = await engine.run({
        ...defaultConfig,
        rules: {
          'test-rule-001': { enabled: true, severity: 'high' },
        },
      });
      
      expect(result.findings).toHaveLength(1);
      expect(result.findings[0].severity).toBe('high');
    });

    it('should capture errors without crashing', async () => {
      const mockRule = createMockRule({
        analyze: async (): Promise<RuleFinding[]> => {
          throw new Error('Rule execution error');
        },
      });
      
      registry.register(mockRule);
      
      const result = await engine.run(defaultConfig);
      
      expect(result.errors.length).toBeGreaterThan(0);
      expect(result.errors[0].type).toBe('rule');
      expect(result.errors[0].message).toContain('Rule execution error');
    });

    it('should calculate summary statistics', async () => {
      const mockRule = createMockRule({
        owasp: ['A01:2021'],
        cwe: ['79'],
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => [{
          id: 'finding-1',
          ruleId: 'test-rule-001',
          severity: 'high',
          message: 'Test error',
          location: {
            file: context.filePath,
            startLine: 1,
                startColumn: 0,
            endLine: 1,
                endColumn: 10,
          },
        }],
      });
      
      registry.register(mockRule);
      
      const result = await engine.run(defaultConfig);
      
      expect(result.summary.totalFindings).toBe(1);
      expect(result.summary.bySeverity.high).toBe(1);
      expect(result.summary.byRule['test-rule-001']).toBe(1);
      expect(result.summary.byCategory['A01:2021']).toBe(1);
      expect(result.summary.byCategory['CWE-79']).toBe(1);
    });
  });

  describe('runOnFile', () => {
    it('should run rules on a single file', async () => {
      const mockRule = createMockRule({
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => [{
          id: 'finding-1',
          ruleId: 'test-rule-001',
          severity: 'medium',
          message: 'Test finding',
          location: {
            file: context.filePath,
            startLine: 1,
                startColumn: 0,
            endLine: 1,
                endColumn: 10,
          },
        }],
      });
      
      registry.register(mockRule);
      
      const findings = await engine.runOnFile(
        path.join(tempDir, 'test.ts'),
        defaultConfig
      );
      
      expect(findings).toHaveLength(1);
    });
  });

  describe('runOnSource', () => {
    it('should run rules on source string', async () => {
      const mockRule = createMockRule({
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => {
          if (context.sourceCode.includes('eval')) {
            return [{
              id: 'finding-1',
              ruleId: 'test-rule-001',
              severity: 'high',
              message: 'eval detected',
              location: {
                file: context.filePath,
                startLine: 1,
                startColumn: 0,
                endLine: 1,
                endColumn: 4,
              },
            }];
          }
          return [];
        },
      });
      
      registry.register(mockRule);
      
      const findings = await engine.runOnSource(
        'eval("console.log(1)")',
        defaultConfig
      );
      
      expect(findings).toHaveLength(1);
      expect(findings[0].message).toBe('eval detected');
    });

    it('should use custom file name', async () => {
      const mockRule = createMockRule({
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => [{
          id: 'finding-1',
          ruleId: 'test-rule-001',
          severity: 'medium',
          message: 'Test',
          location: {
            file: context.filePath,
            startLine: 1,
                startColumn: 0,
            endLine: 1,
                endColumn: 10,
          },
        }],
      });
      
      registry.register(mockRule);
      
      const findings = await engine.runOnSource(
        'const x = 1;',
        defaultConfig,
        'custom.ts'
      );
      
      expect(findings[0].location.file).toContain('custom.ts');
    });
  });

  describe('createRuleEngine', () => {
    it('should create engine with default options', () => {
      const engine = createRuleEngine();
      expect(engine).toBeInstanceOf(RuleEngine);
    });

    it('should create engine with custom options', () => {
      const customRegistry = createRegistry();
      const engine = createRuleEngine({
        registry: customRegistry,
        projectRoot: '/custom/path',
        concurrency: 8,
      });
      
      expect(engine).toBeInstanceOf(RuleEngine);
    });
  });

  describe('abort signal', () => {
    it('should abort execution when signal is triggered', async () => {
      const mockRule = createMockRule({
        analyze: async (context: RuleContext): Promise<RuleFinding[]> => {
          // Simulate slow rule
          await new Promise(resolve => setTimeout(resolve, 100));
          return [{
            id: 'finding-1',
            ruleId: 'test-rule-001',
            severity: 'medium',
            message: 'Test',
            location: {
              file: context.filePath,
              startLine: 1,
                startColumn: 0,
              endLine: 1,
                endColumn: 10,
            },
          }];
        },
      });
      
      registry.register(mockRule);
      
      // Create multiple test files
      for (let i = 0; i < 10; i++) {
        fs.writeFileSync(
          path.join(tempDir, `test${i}.ts`),
          `const x${i} = ${i};`
        );
      }
      
      const controller = new AbortController();
      const abortEngine = createRuleEngine({
        registry,
        projectRoot: tempDir,
        signal: controller.signal,
      });
      
      // Abort immediately
      controller.abort();
      
      const result = await abortEngine.run(defaultConfig);
      
      expect(result.errors.some(e => e.message.includes('aborted'))).toBe(true);
    });
  });

  describe('profiles', () => {
    it('should use minimal profile', async () => {
      // Register rules with different IDs
      registry.register(createMockRule({ id: 'owasp-a01' }));
      registry.register(createMockRule({ id: 'owasp-a02' }));
      registry.register(createMockRule({ id: 'custom-rule' }));
      
      const result = await engine.run({
        ...defaultConfig,
        profile: 'minimal',
      });
      
      // Minimal profile only includes specific rules
      expect(result.filesProcessed).toBe(1);
    });

    it('should use strict profile with all rules', async () => {
      registry.register(createMockRule({ id: 'rule-1' }));
      registry.register(createMockRule({ id: 'rule-2' }));
      registry.register(createMockRule({ id: 'rule-3' }));
      
      const result = await engine.run({
        ...defaultConfig,
        profile: 'strict',
      });
      
      // Strict profile includes all rules
      expect(result.filesProcessed).toBe(1);
    });
  });
});
