/**
 * E2E Tests for Git-Native Knowledge System
 * 
 * Tests MCP tools and CLI commands integration
 * 
 * @packageDocumentation
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';

// Test directories
const TEST_BASE = path.join(process.cwd(), 'tmp', 'e2e-test');
const KNOWLEDGE_DIR = path.join(TEST_BASE, '.knowledge');
const DECISIONS_DIR = path.join(TEST_BASE, 'docs', 'decisions');

describe('E2E: Git-Native Knowledge System', () => {
  beforeAll(async () => {
    // Create test directories
    await fs.mkdir(TEST_BASE, { recursive: true });
    await fs.mkdir(KNOWLEDGE_DIR, { recursive: true });
    await fs.mkdir(DECISIONS_DIR, { recursive: true });
  });

  afterAll(async () => {
    // Cleanup
    await fs.rm(TEST_BASE, { recursive: true, force: true });
  });

  describe('Knowledge Store Integration', () => {
    it('should perform full knowledge store operations', async () => {
      const { createKnowledgeStore } = await import('@musubix/knowledge');
      const store = createKnowledgeStore(KNOWLEDGE_DIR);

      // 1. Create entities
      await store.putEntity({
        id: 'REQ-E2E-001',
        type: 'requirement',
        name: 'User Authentication',
        properties: { priority: 'P0' },
      });

      // Retrieve entity
      const retrieved = await store.getEntity('REQ-E2E-001');
      expect(retrieved).toBeDefined();
      expect(retrieved?.id).toBe('REQ-E2E-001');
      expect(retrieved?.type).toBe('requirement');
      expect(retrieved?.name).toBe('User Authentication');

      // 2. Create more entities
      await store.putEntity({ id: 'DES-E2E-001', type: 'design', name: 'Auth Design' });

      // 3. Create relation
      await store.addRelation({
        source: 'REQ-E2E-001',
        target: 'DES-E2E-001',
        type: 'implements',
      });

      // Verify relation exists
      const relations = await store.getRelations('REQ-E2E-001', 'out');
      expect(relations).toHaveLength(1);
      expect(relations[0].target).toBe('DES-E2E-001');
      expect(relations[0].type).toBe('implements');

      // 4. Query by type
      const requirements = await store.query({ type: 'requirement' });
      expect(requirements.length).toBeGreaterThanOrEqual(1);
      expect(requirements.some(e => e.id === 'REQ-E2E-001')).toBe(true);

      // 5. Create task for traverse test
      await store.putEntity({ id: 'TSK-E2E-001', type: 'task', name: 'Implement Auth' });
      await store.addRelation({ source: 'DES-E2E-001', target: 'TSK-E2E-001', type: 'implements' });

      // 6. Traverse graph
      const traversed = await store.traverse('REQ-E2E-001', { maxDepth: 2 });
      expect(traversed.length).toBeGreaterThanOrEqual(2);
      expect(traversed.map(e => e.id)).toContain('DES-E2E-001');
    });
  });

  describe('Policy Engine Integration', () => {
    it('should list all constitution policies', async () => {
      const { createPolicyEngine } = await import('@musubix/policy');
      const engine = createPolicyEngine();

      const policies = engine.listPolicies();
      
      expect(policies.length).toBe(9);
      expect(policies.map(p => p.id)).toContain('CONST-001');
      expect(policies.map(p => p.id)).toContain('CONST-009');
    });

    it('should get specific policy details', async () => {
      const { createPolicyEngine } = await import('@musubix/policy');
      const engine = createPolicyEngine();

      const policy = engine.getPolicy('CONST-004');
      
      expect(policy).toBeDefined();
      expect(policy?.name).toBe('EARS Format');
      expect(policy?.category).toBe('constitution');
    });

    it('should validate EARS format in content', async () => {
      const { createPolicyEngine } = await import('@musubix/policy');
      const engine = createPolicyEngine();

      // Valid EARS content
      const validContent = `
# REQ-001: User Login

THE system SHALL provide user authentication.
WHEN user enters credentials, THE system SHALL validate them.
`;

      const validReport = await engine.validate(
        { content: validContent, filePath: 'REQ-001.md' },
        ['CONST-004']
      );
      
      expect(validReport.passed).toBe(true);

      // Invalid content (no EARS patterns)
      const invalidContent = `
# REQ-002: Some Feature

Users should be able to do things.
`;

      const invalidReport = await engine.validate(
        { content: invalidContent, filePath: 'REQ-002.md' },
        ['CONST-004']
      );
      
      expect(invalidReport.passed).toBe(false);
      expect(invalidReport.violations.length).toBeGreaterThan(0);
    });
  });

  describe('Decision Manager Integration', () => {
    it('should perform full ADR lifecycle', async () => {
      const { createDecisionManager } = await import('@musubix/decisions');
      const manager = createDecisionManager(DECISIONS_DIR);

      // 1. Create ADR
      const adr = await manager.create({
        title: 'E2E Test: Use TypeScript',
        context: 'Need type safety',
        decision: 'Use TypeScript for all code',
        rationale: 'Better developer experience',
      });

      expect(adr.id).toBeDefined();
      expect(adr.status).toBe('proposed');
      expect(adr.title).toBe('E2E Test: Use TypeScript');

      // 2. Retrieve ADR
      const retrieved = await manager.get(adr.id);
      expect(retrieved).toBeDefined();
      expect(retrieved?.title).toBe('E2E Test: Use TypeScript');

      // 3. Transition status - accept
      const accepted = await manager.accept(adr.id);
      expect(accepted.status).toBe('accepted');

      // 4. Create another ADR for search test
      const adr2 = await manager.create({
        title: 'E2E Test: Database Choice',
        context: 'Need persistence',
        decision: 'Use PostgreSQL',
      });

      // 5. Deprecate first ADR
      const deprecated = await manager.deprecate(adr.id);
      expect(deprecated.status).toBe('deprecated');

      // 6. Search ADRs by keyword
      const typeResults = await manager.search('TypeScript');
      expect(typeResults.length).toBeGreaterThanOrEqual(1);
      expect(typeResults.some(r => r.title.includes('TypeScript'))).toBe(true);

      const dbResults = await manager.search('PostgreSQL');
      expect(dbResults.length).toBeGreaterThanOrEqual(1);

      // 7. Generate index
      await manager.generateIndex();
      
      // Check index file exists
      const indexPath = path.join(DECISIONS_DIR, 'index.md');
      const indexContent = await fs.readFile(indexPath, 'utf-8');
      expect(indexContent).toContain('E2E Test');

      // 8. Verify file persistence
      const files = await fs.readdir(DECISIONS_DIR);
      const adrFile = files.find(f => f.includes(adr.id) && f.endsWith('.md'));
      expect(adrFile).toBeDefined();

      // Read file content
      const content = await fs.readFile(path.join(DECISIONS_DIR, adrFile!), 'utf-8');
      expect(content).toContain('TypeScript');
      expect(content).toContain('Better developer experience');
    });
  });

  describe('Full Workflow Integration', () => {
    it('should support complete SDD workflow', async () => {
      const { createKnowledgeStore } = await import('@musubix/knowledge');
      const { createPolicyEngine } = await import('@musubix/policy');
      const { createDecisionManager } = await import('@musubix/decisions');

      const store = createKnowledgeStore(KNOWLEDGE_DIR);
      const engine = createPolicyEngine();
      const manager = createDecisionManager(DECISIONS_DIR);

      // 1. Create requirement
      await store.putEntity({
        id: 'REQ-FLOW-001',
        type: 'requirement',
        name: 'User Registration',
        properties: { priority: 'P0' },
      });

      // 2. Create ADR for design decision
      const adr = await manager.create({
        title: 'Registration Flow Design',
        context: 'Need user registration',
        decision: 'Use email verification',
        relatedRequirements: ['REQ-FLOW-001'],
      });
      await manager.accept(adr.id);

      // 3. Create design entity
      await store.putEntity({
        id: 'DES-FLOW-001',
        type: 'design',
        name: 'Registration Design',
        properties: { adrId: adr.id },
      });

      // 4. Link requirement to design
      await store.addRelation({
        source: 'REQ-FLOW-001',
        target: 'DES-FLOW-001',
        type: 'implements',
      });

      // 5. Create task
      await store.putEntity({
        id: 'TSK-FLOW-001',
        type: 'task',
        name: 'Implement Registration',
      });

      await store.addRelation({
        source: 'DES-FLOW-001',
        target: 'TSK-FLOW-001',
        type: 'implements',
      });

      // 6. Verify traceability
      const chain = await store.traverse('REQ-FLOW-001', { maxDepth: 3 });
      expect(chain.map(e => e.id)).toContain('REQ-FLOW-001');
      expect(chain.map(e => e.id)).toContain('DES-FLOW-001');
      expect(chain.map(e => e.id)).toContain('TSK-FLOW-001');

      // 7. Validate policy (traceability)
      const policies = engine.listPolicies('constitution');
      expect(policies.map(p => p.id)).toContain('CONST-005'); // Traceability
    });
  });
});