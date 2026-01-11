import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  createKnowledgeStore,
  FileKnowledgeStore,
  Entity,
  Relation,
  EntityType,
} from '../src/index.js';

describe('@musubix/knowledge', () => {
  let tempDir: string;
  let store: FileKnowledgeStore;

  beforeEach(async () => {
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'knowledge-test-'));
    store = createKnowledgeStore(tempDir) as FileKnowledgeStore;
  });

  afterEach(async () => {
    await fs.rm(tempDir, { recursive: true, force: true });
  });

  describe('createKnowledgeStore', () => {
    it('should create a FileKnowledgeStore instance', () => {
      expect(store).toBeInstanceOf(FileKnowledgeStore);
    });
  });

  describe('Entity CRUD', () => {
    const createTestEntity = (id: string, type: EntityType = 'requirement'): Entity => ({
      id,
      type,
      name: `Test ${id}`,
      description: `Description for ${id}`,
      properties: { priority: 'P0' },
      tags: ['test', type],
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
    });

    it('should put and get an entity', async () => {
      const entity = createTestEntity('REQ-001');
      await store.putEntity(entity);
      
      const retrieved = await store.getEntity('REQ-001');
      expect(retrieved).toBeDefined();
      expect(retrieved?.id).toBe('REQ-001');
      expect(retrieved?.name).toBe('Test REQ-001');
    });

    it('should return undefined for non-existent entity', async () => {
      const retrieved = await store.getEntity('NON-EXISTENT');
      expect(retrieved).toBeUndefined();
    });

    it('should update an existing entity', async () => {
      const entity = createTestEntity('REQ-001');
      await store.putEntity(entity);
      
      const updated = { ...entity, name: 'Updated Name' };
      await store.putEntity(updated);
      
      const retrieved = await store.getEntity('REQ-001');
      expect(retrieved?.name).toBe('Updated Name');
    });

    it('should delete an entity', async () => {
      const entity = createTestEntity('REQ-001');
      await store.putEntity(entity);
      
      const deleted = await store.deleteEntity('REQ-001');
      expect(deleted).toBe(true);
      
      const retrieved = await store.getEntity('REQ-001');
      expect(retrieved).toBeUndefined();
    });

    it('should return false when deleting non-existent entity', async () => {
      const deleted = await store.deleteEntity('NON-EXISTENT');
      expect(deleted).toBe(false);
    });
  });

  describe('Relations', () => {
    beforeEach(async () => {
      await store.putEntity({
        id: 'REQ-001',
        type: 'requirement',
        name: 'Requirement 1',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await store.putEntity({
        id: 'DES-001',
        type: 'design',
        name: 'Design 1',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
    });

    it('should add a relation', async () => {
      const relation: Relation = {
        id: 'rel-1',
        source: 'DES-001',
        target: 'REQ-001',
        type: 'implements',
      };
      
      await store.addRelation(relation);
      const relations = await store.getRelations('DES-001', 'out');
      
      expect(relations).toHaveLength(1);
      expect(relations[0].type).toBe('implements');
    });

    it('should throw error when adding relation with non-existent source', async () => {
      const relation: Relation = {
        id: 'rel-1',
        source: 'NON-EXISTENT',
        target: 'REQ-001',
        type: 'implements',
      };
      
      await expect(store.addRelation(relation)).rejects.toThrow('Source entity not found');
    });

    it('should get relations by direction', async () => {
      await store.addRelation({
        id: 'rel-1',
        source: 'DES-001',
        target: 'REQ-001',
        type: 'implements',
      });
      
      const outgoing = await store.getRelations('DES-001', 'out');
      expect(outgoing).toHaveLength(1);
      
      const incoming = await store.getRelations('REQ-001', 'in');
      expect(incoming).toHaveLength(1);
      
      const both = await store.getRelations('DES-001', 'both');
      expect(both).toHaveLength(1);
    });

    it('should remove relations when entity is deleted', async () => {
      await store.addRelation({
        id: 'rel-1',
        source: 'DES-001',
        target: 'REQ-001',
        type: 'implements',
      });
      
      await store.deleteEntity('DES-001');
      
      const relations = await store.getRelations('REQ-001');
      expect(relations).toHaveLength(0);
    });
  });

  describe('Query', () => {
    beforeEach(async () => {
      await store.putEntity({
        id: 'REQ-001',
        type: 'requirement',
        name: 'User Authentication',
        description: 'Handle user login',
        properties: {},
        tags: ['security', 'auth'],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await store.putEntity({
        id: 'REQ-002',
        type: 'requirement',
        name: 'User Registration',
        description: 'Handle user signup',
        properties: {},
        tags: ['auth'],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await store.putEntity({
        id: 'DES-001',
        type: 'design',
        name: 'Auth Service Design',
        properties: {},
        tags: ['security'],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
    });

    it('should filter by type', async () => {
      const results = await store.query({ type: 'requirement' });
      expect(results).toHaveLength(2);
    });

    it('should filter by multiple types', async () => {
      const results = await store.query({ type: ['requirement', 'design'] });
      expect(results).toHaveLength(3);
    });

    it('should filter by tags', async () => {
      const results = await store.query({ tags: ['security'] });
      expect(results).toHaveLength(2);
    });

    it('should filter by text', async () => {
      const results = await store.query({ text: 'login' });
      expect(results).toHaveLength(1);
      expect(results[0].id).toBe('REQ-001');
    });

    it('should apply pagination', async () => {
      const results = await store.query({ limit: 1, offset: 1 });
      expect(results).toHaveLength(1);
    });
  });

  describe('Search', () => {
    beforeEach(async () => {
      await store.putEntity({
        id: 'REQ-001',
        type: 'requirement',
        name: 'Authentication Feature',
        description: 'Implement secure login',
        properties: {},
        tags: ['security'],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
    });

    it('should search in name', async () => {
      const results = await store.search('Authentication');
      expect(results).toHaveLength(1);
    });

    it('should search in description', async () => {
      const results = await store.search('secure login');
      expect(results).toHaveLength(1);
    });

    it('should search in tags', async () => {
      const results = await store.search('security');
      expect(results).toHaveLength(1);
    });

    it('should be case insensitive by default', async () => {
      const results = await store.search('AUTHENTICATION');
      expect(results).toHaveLength(1);
    });
  });

  describe('Traverse', () => {
    beforeEach(async () => {
      // Create a chain: REQ-001 <- DES-001 <- TSK-001
      await store.putEntity({
        id: 'REQ-001',
        type: 'requirement',
        name: 'Requirement',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await store.putEntity({
        id: 'DES-001',
        type: 'design',
        name: 'Design',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await store.putEntity({
        id: 'TSK-001',
        type: 'task',
        name: 'Task',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      
      await store.addRelation({
        id: 'rel-1',
        source: 'DES-001',
        target: 'REQ-001',
        type: 'implements',
      });
      await store.addRelation({
        id: 'rel-2',
        source: 'TSK-001',
        target: 'DES-001',
        type: 'implements',
      });
    });

    it('should traverse the graph', async () => {
      const results = await store.traverse('REQ-001', { depth: 3 });
      expect(results).toHaveLength(3);
    });

    it('should respect depth limit', async () => {
      const results = await store.traverse('REQ-001', { depth: 1 });
      expect(results).toHaveLength(2);
    });

    it('should filter by relation type', async () => {
      const results = await store.traverse('REQ-001', {
        depth: 3,
        relationTypes: ['depends_on'],
      });
      expect(results).toHaveLength(1); // Only the start node
    });
  });

  describe('Persistence', () => {
    it('should save and load graph', async () => {
      await store.putEntity({
        id: 'REQ-001',
        type: 'requirement',
        name: 'Test',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      
      await store.save();
      
      // Create new store and load
      const newStore = createKnowledgeStore(tempDir) as FileKnowledgeStore;
      await newStore.load();
      
      const entity = await newStore.getEntity('REQ-001');
      expect(entity).toBeDefined();
      expect(entity?.name).toBe('Test');
    });

    it('should create directory if not exists', async () => {
      const nestedPath = path.join(tempDir, 'nested', 'dir');
      const nestedStore = createKnowledgeStore(nestedPath);
      
      await nestedStore.putEntity({
        id: 'REQ-001',
        type: 'requirement',
        name: 'Test',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await nestedStore.save();
      
      const exists = await fs.access(path.join(nestedPath, 'graph.json')).then(() => true).catch(() => false);
      expect(exists).toBe(true);
    });
  });

  describe('Stats', () => {
    it('should return correct stats', async () => {
      await store.putEntity({
        id: 'REQ-001',
        type: 'requirement',
        name: 'Req 1',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await store.putEntity({
        id: 'REQ-002',
        type: 'requirement',
        name: 'Req 2',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      await store.putEntity({
        id: 'DES-001',
        type: 'design',
        name: 'Des 1',
        properties: {},
        tags: [],
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
      });
      
      const stats = store.getStats();
      expect(stats.entityCount).toBe(3);
      expect(stats.types.requirement).toBe(2);
      expect(stats.types.design).toBe(1);
    });
  });
});
