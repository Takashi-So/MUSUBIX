import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  createDecisionManager,
  DecisionManager,
  ADRDraft,
  ADR_TEMPLATE,
} from '../src/index.js';

describe('@musubix/decisions', () => {
  let tempDir: string;
  let manager: DecisionManager;

  beforeEach(async () => {
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'decisions-test-'));
    manager = createDecisionManager(tempDir) as DecisionManager;
  });

  afterEach(async () => {
    await fs.rm(tempDir, { recursive: true, force: true });
  });

  describe('createDecisionManager', () => {
    it('should create a DecisionManager instance', () => {
      expect(manager).toBeInstanceOf(DecisionManager);
    });
  });

  describe('ADR CRUD', () => {
    const createTestDraft = (title: string = 'Test Decision'): ADRDraft => ({
      title,
      context: 'We need to make a decision',
      decision: 'We decided to do X',
      rationale: 'Because of Y',
      alternatives: ['Option A', 'Option B'],
      consequences: ['Impact 1', 'Impact 2'],
      relatedRequirements: ['REQ-001'],
      decider: 'Test User',
    });

    it('should create an ADR', async () => {
      const draft = createTestDraft();
      const adr = await manager.create(draft);

      expect(adr.id).toBe('0001');
      expect(adr.title).toBe('Test Decision');
      expect(adr.status).toBe('proposed');
      expect(adr.decider).toBe('Test User');
    });

    it('should auto-increment ID', async () => {
      await manager.create(createTestDraft('First'));
      const second = await manager.create(createTestDraft('Second'));

      expect(second.id).toBe('0002');
    });

    it('should get an ADR by ID', async () => {
      await manager.create(createTestDraft());
      const adr = await manager.get('0001');

      expect(adr).toBeDefined();
      expect(adr?.title).toBe('Test Decision');
    });

    it('should return undefined for non-existent ADR', async () => {
      const adr = await manager.get('9999');
      expect(adr).toBeUndefined();
    });

    it('should list all ADRs', async () => {
      await manager.create(createTestDraft('First'));
      await manager.create(createTestDraft('Second'));

      const adrs = await manager.list();
      expect(adrs).toHaveLength(2);
    });

    it('should filter by status', async () => {
      const adr = await manager.create(createTestDraft());
      await manager.accept(adr.id);

      const proposed = await manager.list({ status: 'proposed' });
      const accepted = await manager.list({ status: 'accepted' });

      expect(proposed).toHaveLength(0);
      expect(accepted).toHaveLength(1);
    });

    it('should filter by keyword', async () => {
      await manager.create(createTestDraft('Authentication'));
      await manager.create(createTestDraft('Database'));

      const results = await manager.list({ keyword: 'auth' });
      expect(results).toHaveLength(1);
      expect(results[0].title).toBe('Authentication');
    });

    it('should update an ADR', async () => {
      const adr = await manager.create(createTestDraft());
      const updated = await manager.update(adr.id, { rationale: 'New rationale' });

      expect(updated.rationale).toBe('New rationale');
    });

    it('should throw when updating non-existent ADR', async () => {
      await expect(manager.update('9999', { rationale: 'test' })).rejects.toThrow('ADR not found');
    });
  });

  describe('Status Management', () => {
    it('should accept an ADR', async () => {
      const adr = await manager.create({
        title: 'Test',
        context: 'Context',
        decision: 'Decision',
      });

      const accepted = await manager.accept(adr.id);
      expect(accepted.status).toBe('accepted');
    });

    it('should deprecate an ADR', async () => {
      const adr = await manager.create({
        title: 'Test',
        context: 'Context',
        decision: 'Decision',
      });

      const deprecated = await manager.deprecate(adr.id);
      expect(deprecated.status).toBe('deprecated');
    });

    it('should mark as superseded with reference', async () => {
      const first = await manager.create({
        title: 'First',
        context: 'Context',
        decision: 'Decision',
      });
      const second = await manager.create({
        title: 'Second',
        context: 'Context',
        decision: 'Decision',
      });

      const superseded = await manager.deprecate(first.id, second.id);
      expect(superseded.status).toBe('superseded');
      expect(superseded.relatedADRs).toContain(second.id);
    });
  });

  describe('Index Generation', () => {
    it('should generate index.md', async () => {
      await manager.create({
        title: 'First Decision',
        context: 'Context',
        decision: 'Decision',
      });

      await manager.generateIndex();

      const indexPath = path.join(tempDir, 'index.md');
      const content = await fs.readFile(indexPath, 'utf-8');

      expect(content).toContain('Architecture Decision Records');
      expect(content).toContain('First Decision');
    });

    it('should categorize by status', async () => {
      const adr1 = await manager.create({
        title: 'Proposed One',
        context: 'Context',
        decision: 'Decision',
      });
      const adr2 = await manager.create({
        title: 'Accepted One',
        context: 'Context',
        decision: 'Decision',
      });
      await manager.accept(adr2.id);

      await manager.generateIndex();

      const indexPath = path.join(tempDir, 'index.md');
      const content = await fs.readFile(indexPath, 'utf-8');

      expect(content).toContain('## Accepted');
      expect(content).toContain('## Proposed');
    });
  });

  describe('Search', () => {
    it('should search ADRs', async () => {
      await manager.create({
        title: 'Authentication',
        context: 'User auth context',
        decision: 'Use OAuth',
      });
      await manager.create({
        title: 'Database',
        context: 'Data storage',
        decision: 'Use PostgreSQL',
      });

      const results = await manager.search('OAuth');
      expect(results).toHaveLength(1);
      expect(results[0].title).toBe('Authentication');
    });
  });

  describe('Find by Requirement', () => {
    it('should find ADRs by requirement ID', async () => {
      await manager.create({
        title: 'Related to REQ-001',
        context: 'Context',
        decision: 'Decision',
        relatedRequirements: ['REQ-001'],
      });
      await manager.create({
        title: 'Related to REQ-002',
        context: 'Context',
        decision: 'Decision',
        relatedRequirements: ['REQ-002'],
      });

      const results = await manager.findByRequirement('REQ-001');
      expect(results).toHaveLength(1);
      expect(results[0].title).toBe('Related to REQ-001');
    });
  });

  describe('File Persistence', () => {
    it('should create markdown file on create', async () => {
      await manager.create({
        title: 'Test Decision',
        context: 'Context',
        decision: 'Decision',
      });

      const files = await fs.readdir(tempDir);
      const adrFile = files.find(f => f.startsWith('0001-'));

      expect(adrFile).toBeDefined();
      expect(adrFile).toMatch(/\.md$/);
    });

    it('should persist content correctly', async () => {
      await manager.create({
        title: 'Test Decision',
        context: 'My context',
        decision: 'My decision',
        decider: 'John Doe',
      });

      const files = await fs.readdir(tempDir);
      const adrFile = files.find(f => f.startsWith('0001-'))!;
      const content = await fs.readFile(path.join(tempDir, adrFile), 'utf-8');

      expect(content).toContain('# ADR-0001: Test Decision');
      expect(content).toContain('My context');
      expect(content).toContain('My decision');
      expect(content).toContain('John Doe');
    });

    it('should load existing ADRs', async () => {
      // Create ADR
      await manager.create({
        title: 'Existing',
        context: 'Context',
        decision: 'Decision',
      });

      // Create new manager instance
      const newManager = createDecisionManager(tempDir);
      const adrs = await newManager.list();

      expect(adrs).toHaveLength(1);
      expect(adrs[0].title).toBe('Existing');
    });
  });

  describe('Template', () => {
    it('should export ADR template', () => {
      expect(ADR_TEMPLATE).toContain('# ADR-NNNN');
      expect(ADR_TEMPLATE).toContain('コンテキスト');
      expect(ADR_TEMPLATE).toContain('決定');
      expect(ADR_TEMPLATE).toContain('理由');
    });
  });
});
