/**
 * Tests for EnhancedCodeGenerator
 *
 * @see REQ-YI-GEN-001 - C4 Design to Code
 * @see REQ-YI-GEN-002 - EARS to Test
 * @see REQ-YI-GEN-003 - Traceability Maintenance
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import {
  EnhancedCodeGenerator,
  createEnhancedCodeGenerator,
} from '../enhanced-generator.js';
import type {
  C4Design,
  EARSRequirement,
} from '../enhanced-generator.js';

describe('EnhancedCodeGenerator', () => {
  let generator: EnhancedCodeGenerator;
  const testOutputDir = '/tmp/musubix-test-codegen';

  beforeEach(() => {
    generator = new EnhancedCodeGenerator({
      outputDir: testOutputDir,
      language: 'typescript',
      includeTests: true,
      testFramework: 'vitest',
      dryRun: true,
    });

    // Clean up test directory
    if (fs.existsSync(testOutputDir)) {
      fs.rmSync(testOutputDir, { recursive: true });
    }
  });

  afterEach(() => {
    // Clean up
    if (fs.existsSync(testOutputDir)) {
      fs.rmSync(testOutputDir, { recursive: true });
    }
  });

  // ============================================================
  // Factory Function
  // ============================================================

  describe('createEnhancedCodeGenerator', () => {
    it('should create generator instance', () => {
      const gen = createEnhancedCodeGenerator({
        outputDir: testOutputDir,
        dryRun: true,
      });
      expect(gen).toBeInstanceOf(EnhancedCodeGenerator);
    });
  });

  // ============================================================
  // Design Parsing (REQ-YI-GEN-001)
  // ============================================================

  describe('parseDesign', () => {
    it('should parse title from markdown', () => {
      const content = '# User Management System Design\n\nVersion: 1.0.0';
      const design = generator.parseDesign(content);

      expect(design.title).toBe('User Management System Design');
      expect(design.version).toBe('1.0.0');
    });

    it('should parse TypeScript interfaces', () => {
      const content = `
# Design

\`\`\`typescript
interface UserEntity {
  id: string;
  name: string;
  email: string;
}
\`\`\`
`;
      const design = generator.parseDesign(content);

      expect(design.components.length).toBeGreaterThanOrEqual(1);
      const user = design.components.find(c => c.name === 'UserEntity');
      expect(user).toBeDefined();
      expect(user?.properties).toHaveLength(3);
    });

    it('should parse component sections', () => {
      const content = `
# Design

## 1. Components

### 1.1 Component: UserRepository

REQ-USER-001
DES-USER-REPO-001

This is the user repository.
`;
      const design = generator.parseDesign(content);

      const repo = design.components.find(c => c.name === 'UserRepository');
      expect(repo).toBeDefined();
      expect(repo?.type).toBe('repository');
      expect(repo?.requirementIds).toContain('REQ-USER-001');
      expect(repo?.designElementIds).toContain('DES-USER-REPO-001');
    });

    it('should infer component type from name', () => {
      const content = `
\`\`\`typescript
interface OrderService {}
interface OrderRepository {}
interface OrderController {}
interface OrderFactory {}
interface Price {}
\`\`\`
`;
      const design = generator.parseDesign(content);

      expect(design.components.find(c => c.name === 'OrderService')?.type).toBe('service');
      expect(design.components.find(c => c.name === 'OrderRepository')?.type).toBe('repository');
      expect(design.components.find(c => c.name === 'OrderController')?.type).toBe('controller');
      expect(design.components.find(c => c.name === 'OrderFactory')?.type).toBe('factory');
      expect(design.components.find(c => c.name === 'Price')?.type).toBe('entity');
    });

    it('should parse relationships', () => {
      const content = `
# Design

UserService --> UserRepository: uses
OrderController --> OrderService: delegates
`;
      const design = generator.parseDesign(content);

      expect(design.relationships).toHaveLength(2);
      expect(design.relationships[0]).toEqual({
        source: 'UserService',
        target: 'UserRepository',
        label: 'uses',
      });
    });
  });

  // ============================================================
  // Code Generation (REQ-YI-GEN-001)
  // ============================================================

  describe('generateFromDesign', () => {
    it('should generate entity code', async () => {
      const design: C4Design = {
        title: 'Test Design',
        components: [{
          id: 'DES-USER',
          name: 'User',
          type: 'entity',
          properties: [
            { name: 'name', type: 'string' },
            { name: 'email', type: 'string' },
          ],
          methods: [],
          dependencies: [],
          requirementIds: ['REQ-USER-001'],
          designElementIds: ['DES-USER'],
        }],
        relationships: [],
      };

      const result = await generator.generateFromDesign(design);

      expect(result.success).toBe(true);
      expect(result.stats.entities).toBe(1);
      expect(result.stats.tests).toBe(1);

      const entityFile = result.files.find(f => f.fileType === 'entity');
      expect(entityFile).toBeDefined();
      expect(entityFile?.content).toContain('interface User');
      expect(entityFile?.content).toContain('createUser');
      expect(entityFile?.content).toContain('@see REQ-USER-001');
    });

    it('should generate repository code', async () => {
      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-REPO',
          name: 'UserRepository',
          type: 'repository',
          properties: [],
          methods: [],
          dependencies: [],
          requirementIds: ['REQ-REPO-001'],
          designElementIds: ['DES-REPO'],
        }],
        relationships: [],
      };

      const result = await generator.generateFromDesign(design);

      expect(result.success).toBe(true);
      expect(result.stats.repositories).toBe(1);

      const repoFile = result.files.find(f => f.fileType === 'repository');
      expect(repoFile).toBeDefined();
      expect(repoFile?.content).toContain('interface UserRepository');
      expect(repoFile?.content).toContain('InMemoryUserRepository');
    });

    it('should generate service code', async () => {
      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-SVC',
          name: 'OrderService',
          type: 'service',
          properties: [],
          methods: [{
            name: 'placeOrder',
            parameters: [{ name: 'order', type: 'Order' }],
            returnType: 'Promise<void>',
            async: true,
          }],
          dependencies: [],
          requirementIds: [],
          designElementIds: ['DES-SVC'],
        }],
        relationships: [],
      };

      const result = await generator.generateFromDesign(design);

      expect(result.success).toBe(true);
      expect(result.stats.services).toBe(1);

      const svcFile = result.files.find(f => f.fileType === 'service');
      expect(svcFile).toBeDefined();
      expect(svcFile?.content).toContain('class OrderService');
      expect(svcFile?.content).toContain('async placeOrder');
    });

    it('should generate controller code', async () => {
      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-CTRL',
          name: 'UserController',
          type: 'controller',
          properties: [],
          methods: [],
          dependencies: [],
          requirementIds: [],
          designElementIds: ['DES-CTRL'],
        }],
        relationships: [],
      };

      const result = await generator.generateFromDesign(design);

      expect(result.stats.controllers).toBe(1);
    });

    it('should generate value object code', async () => {
      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-VO',
          name: 'Price',
          type: 'value-object',
          properties: [
            { name: 'amount', type: 'number' },
            { name: 'currency', type: 'string' },
          ],
          methods: [],
          dependencies: [],
          requirementIds: ['REQ-PRICE-001'],
          designElementIds: ['DES-VO'],
        }],
        relationships: [],
      };

      const result = await generator.generateFromDesign(design);

      const voFile = result.files.find(f => f.path === 'price.ts');
      expect(voFile).toBeDefined();
      expect(voFile?.content).toContain('interface Price');
      expect(voFile?.content).toContain('createPrice');
      expect(voFile?.content).toContain('readonly amount');
    });

    it('should generate traceability entries', async () => {
      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-USER',
          name: 'User',
          type: 'entity',
          properties: [],
          methods: [],
          dependencies: [],
          requirementIds: ['REQ-USER-001', 'REQ-USER-002'],
          designElementIds: ['DES-USER'],
        }],
        relationships: [],
      };

      const result = await generator.generateFromDesign(design);

      expect(result.traceabilityMap.length).toBeGreaterThanOrEqual(2);
      const entry = result.traceabilityMap.find(e => e.requirementId === 'REQ-USER-001');
      expect(entry).toBeDefined();
      expect(entry?.designElementId).toBe('DES-USER');
    });

    it('should skip test generation when includeTests is false', async () => {
      const noTestGenerator = new EnhancedCodeGenerator({
        outputDir: testOutputDir,
        includeTests: false,
        dryRun: true,
      });

      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-USER',
          name: 'User',
          type: 'entity',
          properties: [],
          methods: [],
          dependencies: [],
          requirementIds: [],
          designElementIds: ['DES-USER'],
        }],
        relationships: [],
      };

      const result = await noTestGenerator.generateFromDesign(design);

      expect(result.stats.tests).toBe(0);
    });
  });

  // ============================================================
  // EARS Parsing (REQ-YI-GEN-002)
  // ============================================================

  describe('parseEARSRequirements', () => {
    it('should parse ubiquitous requirements', () => {
      const content = 'REQ-001 THE system SHALL validate all inputs.';
      const reqs = generator.parseEARSRequirements(content);

      expect(reqs).toHaveLength(1);
      expect(reqs[0].id).toBe('REQ-001');
      expect(reqs[0].type).toBe('ubiquitous');
      expect(reqs[0].subject).toBe('system');
      expect(reqs[0].requirement).toContain('validate');
    });

    it('should parse event-driven requirements', () => {
      const content = 'REQ-002 WHEN user submits form, THE system SHALL process the data.';
      const reqs = generator.parseEARSRequirements(content);

      expect(reqs).toHaveLength(1);
      expect(reqs[0].type).toBe('event-driven');
      expect(reqs[0].trigger).toBe('user submits form');
    });

    it('should parse state-driven requirements', () => {
      const content = 'REQ-003 WHILE system is in maintenance mode, THE application SHALL display maintenance page.';
      const reqs = generator.parseEARSRequirements(content);

      expect(reqs).toHaveLength(1);
      expect(reqs[0].type).toBe('state-driven');
      expect(reqs[0].trigger).toContain('maintenance');
    });

    it('should parse unwanted requirements', () => {
      const content = 'REQ-004 THE system SHALL NOT expose sensitive data.';
      const reqs = generator.parseEARSRequirements(content);

      expect(reqs).toHaveLength(1);
      expect(reqs[0].type).toBe('unwanted');
      expect(reqs[0].requirement).toContain('NOT');
    });

    it('should parse optional requirements', () => {
      const content = 'REQ-005 IF user is premium, THEN THE system SHALL show advanced features.';
      const reqs = generator.parseEARSRequirements(content);

      expect(reqs).toHaveLength(1);
      expect(reqs[0].type).toBe('optional');
      expect(reqs[0].trigger).toContain('premium');
    });
  });

  // ============================================================
  // Test Generation from EARS (REQ-YI-GEN-002)
  // ============================================================

  describe('generateTestsFromEARS', () => {
    it('should generate test file from requirements', () => {
      const requirements: EARSRequirement[] = [
        {
          id: 'REQ-001',
          type: 'ubiquitous',
          subject: 'UserService',
          requirement: 'validate all user inputs',
          text: 'THE UserService SHALL validate all user inputs',
        },
        {
          id: 'REQ-002',
          type: 'event-driven',
          subject: 'UserService',
          trigger: 'user registers',
          requirement: 'send confirmation email',
          text: 'WHEN user registers, THE UserService SHALL send confirmation email',
        },
      ];

      const files = generator.generateTestsFromEARS(requirements);

      expect(files).toHaveLength(1);
      expect(files[0].path).toBe('user-service.test.ts');
      expect(files[0].content).toContain('describe(\'UserService\'');
      expect(files[0].content).toContain('REQ-001');
      expect(files[0].content).toContain('REQ-002');
      expect(files[0].requirementIds).toContain('REQ-001');
      expect(files[0].requirementIds).toContain('REQ-002');
    });

    it('should group requirements by subject', () => {
      const requirements: EARSRequirement[] = [
        {
          id: 'REQ-001',
          type: 'ubiquitous',
          subject: 'UserService',
          requirement: 'test',
          text: 'THE UserService SHALL test',
        },
        {
          id: 'REQ-002',
          type: 'ubiquitous',
          subject: 'OrderService',
          requirement: 'test',
          text: 'THE OrderService SHALL test',
        },
      ];

      const files = generator.generateTestsFromEARS(requirements);

      expect(files).toHaveLength(2);
      expect(files.find(f => f.path === 'user-service.test.ts')).toBeDefined();
      expect(files.find(f => f.path === 'order-service.test.ts')).toBeDefined();
    });

    it('should generate appropriate test names for each requirement type', () => {
      const requirements: EARSRequirement[] = [
        {
          id: 'REQ-001',
          type: 'event-driven',
          subject: 'System',
          trigger: 'error occurs',
          requirement: 'log the error',
          text: 'WHEN error occurs, THE System SHALL log the error',
        },
        {
          id: 'REQ-002',
          type: 'unwanted',
          subject: 'System',
          requirement: 'NOT crash on invalid input',
          text: 'THE System SHALL NOT crash on invalid input',
        },
      ];

      const files = generator.generateTestsFromEARS(requirements);
      const content = files[0].content;

      expect(content).toContain('should log the error when error occurs');
      expect(content).toContain('should not crash on invalid input');
    });
  });

  // ============================================================
  // Traceability Matrix (REQ-YI-GEN-003)
  // ============================================================

  describe('generateTraceabilityMatrix', () => {
    it('should generate markdown table', () => {
      const entries = [
        {
          requirementId: 'REQ-001',
          designElementId: 'DES-001',
          filePath: 'user.ts',
          lineNumbers: [10, 25],
          codeElement: 'User',
        },
        {
          requirementId: 'REQ-002',
          designElementId: 'DES-002',
          filePath: 'order.ts',
          lineNumbers: [5],
        },
      ];

      const matrix = generator.generateTraceabilityMatrix(entries);

      expect(matrix).toContain('# Traceability Matrix');
      expect(matrix).toContain('| Requirement | Design Element | File | Lines | Code Element |');
      expect(matrix).toContain('| REQ-001 | DES-001 | user.ts | 10, 25 | User |');
      expect(matrix).toContain('| REQ-002 | DES-002 | order.ts | 5 | - |');
    });
  });

  // ============================================================
  // File Writing
  // ============================================================

  describe('file writing', () => {
    it('should write files when dryRun is false', async () => {
      const realGenerator = new EnhancedCodeGenerator({
        outputDir: testOutputDir,
        dryRun: false,
      });

      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-TEST',
          name: 'TestEntity',
          type: 'entity',
          properties: [{ name: 'value', type: 'string' }],
          methods: [],
          dependencies: [],
          requirementIds: [],
          designElementIds: ['DES-TEST'],
        }],
        relationships: [],
      };

      const result = await realGenerator.generateFromDesign(design);

      expect(result.success).toBe(true);
      expect(fs.existsSync(path.join(testOutputDir, 'test-entity.ts'))).toBe(true);
    });

    it('should not overwrite existing files by default', async () => {
      // Create output directory and file first
      fs.mkdirSync(testOutputDir, { recursive: true });
      fs.writeFileSync(path.join(testOutputDir, 'test-entity.ts'), 'existing content');

      const realGenerator = new EnhancedCodeGenerator({
        outputDir: testOutputDir,
        dryRun: false,
        overwrite: false,
      });

      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-TEST',
          name: 'TestEntity',
          type: 'entity',
          properties: [],
          methods: [],
          dependencies: [],
          requirementIds: [],
          designElementIds: ['DES-TEST'],
        }],
        relationships: [],
      };

      const result = await realGenerator.generateFromDesign(design);

      expect(result.warnings).toContainEqual(expect.stringContaining('already exists'));
      expect(fs.readFileSync(path.join(testOutputDir, 'test-entity.ts'), 'utf-8')).toBe('existing content');
    });

    it('should overwrite when overwrite option is true', async () => {
      // Create output directory and file first
      fs.mkdirSync(testOutputDir, { recursive: true });
      fs.writeFileSync(path.join(testOutputDir, 'test-entity.ts'), 'existing content');

      const realGenerator = new EnhancedCodeGenerator({
        outputDir: testOutputDir,
        dryRun: false,
        overwrite: true,
      });

      const design: C4Design = {
        title: 'Test',
        components: [{
          id: 'DES-TEST',
          name: 'TestEntity',
          type: 'entity',
          properties: [{ name: 'value', type: 'string' }],
          methods: [],
          dependencies: [],
          requirementIds: [],
          designElementIds: ['DES-TEST'],
        }],
        relationships: [],
      };

      const result = await realGenerator.generateFromDesign(design);

      expect(result.success).toBe(true);
      const content = fs.readFileSync(path.join(testOutputDir, 'test-entity.ts'), 'utf-8');
      expect(content).toContain('interface TestEntity');
    });
  });
});
