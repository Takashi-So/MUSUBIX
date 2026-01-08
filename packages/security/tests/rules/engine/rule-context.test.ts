/**
 * @fileoverview Rule Context Tests
 * @module @nahisaho/musubix-security/rules/engine/rule-context.test
 * @trace TSK-RULE-001
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as os from 'node:os';
import { RuleContextBuilder, createContextBuilder } from '../../../src/rules/engine/rule-context.js';

describe('RuleContextBuilder', () => {
  let tempDir: string;
  let testFile: string;
  const testCode = `
import express from 'express';

const app = express();

app.get('/users/:id', (req, res) => {
  const userId = req.params.id;
  res.json({ id: userId });
});

export default app;
`;

  beforeEach(() => {
    // Create temp directory and test file
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'rule-context-test-'));
    testFile = path.join(tempDir, 'test.ts');
    fs.writeFileSync(testFile, testCode);
  });

  afterEach(() => {
    // Clean up
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  describe('build', () => {
    it('should build context from file', async () => {
      const builder = new RuleContextBuilder();
      
      const context = await builder.build(testFile);
      
      expect(context.filePath).toBe(testFile);
      expect(context.sourceCode).toBe(testCode);
      expect(context.sourceFile).toBeDefined();
    });

    it('should use project root for relative paths', async () => {
      const builder = new RuleContextBuilder()
        .withProjectRoot(tempDir);
      
      const context = await builder.build('test.ts');
      
      expect(context.filePath).toBe(testFile);
    });

    it('should apply config', async () => {
      const builder = new RuleContextBuilder()
        .withConfig({
          profile: 'strict',
          severityThreshold: 'medium',
        });
      
      const context = await builder.build(testFile);
      
      expect(context.config.profile).toBe('strict');
      expect(context.config.severityThreshold).toBe('medium');
    });

    it('should store previous results', async () => {
      const previousResults = new Map([['rule-1', {
        ruleId: 'rule-1',
        ruleName: 'Test Rule',
        findings: [],
        executionTime: 100,
        errors: [],
        success: true,
      }]]);
      
      const builder = new RuleContextBuilder()
        .withPreviousResults(previousResults);
      
      const context = await builder.build(testFile);
      
      expect(context.previousResults.get('rule-1')).toBeDefined();
    });
  });

  describe('buildFromSource', () => {
    it('should build context from source string', () => {
      const builder = new RuleContextBuilder();
      const sourceCode = 'const x = 1;';
      
      const context = builder.buildFromSource('test.ts', sourceCode);
      
      expect(context.sourceCode).toBe(sourceCode);
      expect(context.sourceFile).toBeDefined();
    });

    it('should parse TypeScript correctly', () => {
      const builder = new RuleContextBuilder();
      const sourceCode = `
interface User {
  id: string;
  name: string;
}

function getUser(id: string): User {
  return { id, name: 'Test' };
}
`;
      
      const context = builder.buildFromSource('user.ts', sourceCode);
      
      // Check that it parsed correctly
      const interfaces = context.sourceFile.getInterfaces();
      expect(interfaces).toHaveLength(1);
      expect(interfaces[0].getName()).toBe('User');
      
      const functions = context.sourceFile.getFunctions();
      expect(functions).toHaveLength(1);
      expect(functions[0].getName()).toBe('getUser');
    });
  });

  describe('context methods', () => {
    it('should report findings', () => {
      const builder = new RuleContextBuilder();
      const context = builder.buildFromSource('test.ts', 'const x = 1;');
      
      // Set current rule (normally done by engine)
      (context as any).setCurrentRule('test-rule');
      
      // Report a finding
      context.report({
        severity: 'medium',
        message: 'Test finding',
        location: {
          file: 'test.ts',
          startLine: 1,
          endLine: 1,
          startColumn: 0,
          endColumn: 10,
        },
      });
      
      const findings = (context as any).getFindings();
      expect(findings).toHaveLength(1);
      expect(findings[0].ruleId).toBe('test-rule');
      expect(findings[0].message).toBe('Test finding');
      expect(findings[0].id).toBeDefined();
    });

    it('should get rule options with defaults', () => {
      const builder = new RuleContextBuilder()
        .withConfig({
          rules: {
            'test-rule': {
              enabled: true,
              options: {
                maxLength: 100,
              },
            },
          },
        });
      
      const context = builder.buildFromSource('test.ts', 'const x = 1;');
      (context as any).setCurrentRule('test-rule');
      
      // Get configured option
      expect(context.getOption('maxLength', 50)).toBe(100);
      
      // Get default for unconfigured option
      expect(context.getOption('minLength', 10)).toBe(10);
    });
  });

  describe('createContextBuilder', () => {
    it('should return a RuleContextBuilder instance', () => {
      const builder = createContextBuilder();
      
      expect(builder).toBeInstanceOf(RuleContextBuilder);
    });
  });

  describe('withTaintAnalysis', () => {
    it('should enable taint analysis', () => {
      const builder = new RuleContextBuilder()
        .withTaintAnalysis(true);
      
      const context = builder.buildFromSource('test.ts', 'const x = 1;');
      
      expect(context.config.enableTaintAnalysis).toBe(true);
    });

    it('should disable taint analysis', () => {
      const builder = new RuleContextBuilder()
        .withTaintAnalysis(false);
      
      const context = builder.buildFromSource('test.ts', 'const x = 1;');
      
      expect(context.config.enableTaintAnalysis).toBe(false);
    });
  });

  describe('withDFG', () => {
    it('should enable DFG analysis', () => {
      const builder = new RuleContextBuilder()
        .withDFG(true);
      
      const context = builder.buildFromSource('test.ts', 'const x = 1;');
      
      expect(context.config.enableDFG).toBe(true);
    });
  });
});
