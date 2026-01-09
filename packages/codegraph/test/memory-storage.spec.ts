/**
 * @nahisaho/musubix-codegraph - Memory Storage Tests
 *
 * @see TSK-CG-051
 * @see REQ-CG-API-005
 * @see DES-CG-006
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { MemoryStorage } from '../src/storage/memory-storage.js';
import type { Entity, Relation, EntityType, RelationType } from '../src/types.js';

describe('MemoryStorage', () => {
  let storage: MemoryStorage;

  beforeEach(async () => {
    storage = new MemoryStorage();
    await storage.initialize();
  });

  afterEach(async () => {
    await storage.close();
  });

  describe('lifecycle', () => {
    it('should initialize successfully', async () => {
      const newStorage = new MemoryStorage();
      expect(newStorage.isInitialized()).toBe(false);
      await newStorage.initialize();
      expect(newStorage.isInitialized()).toBe(true);
      await newStorage.close();
    });

    it('should close and clear data', async () => {
      await storage.saveEntity(createTestEntity('test-1', 'class'));
      await storage.close();

      const stats = await storage.getStats();
      expect(stats.entityCount).toBe(0);
    });
  });

  describe('entity operations', () => {
    it('should save and retrieve entity', async () => {
      const entity = createTestEntity('func-1', 'function');
      await storage.saveEntity(entity);

      const retrieved = await storage.getEntity('func-1');
      expect(retrieved).toEqual(entity);
    });

    it('should return null for non-existent entity', async () => {
      const result = await storage.getEntity('non-existent');
      expect(result).toBeNull();
    });

    it('should delete entity', async () => {
      const entity = createTestEntity('delete-me', 'class');
      await storage.saveEntity(entity);
      await storage.deleteEntity('delete-me');

      const result = await storage.getEntity('delete-me');
      expect(result).toBeNull();
    });

    it('should delete related relations when deleting entity', async () => {
      const source = createTestEntity('source-1', 'class');
      const target = createTestEntity('target-1', 'class');
      const relation = createTestRelation('source-1', 'target-1', 'calls');

      await storage.saveEntity(source);
      await storage.saveEntity(target);
      await storage.saveRelation(relation);

      await storage.deleteEntity('source-1');

      const relations = await storage.getRelations('target-1');
      expect(relations).toHaveLength(0);
    });
  });

  describe('query operations', () => {
    beforeEach(async () => {
      // Set up test data
      await storage.saveEntity(createTestEntity('class-1', 'class', '/src/user.ts'));
      await storage.saveEntity(createTestEntity('func-1', 'function', '/src/utils.ts'));
      await storage.saveEntity(createTestEntity('func-2', 'function', '/src/user.ts'));
      await storage.saveEntity(createTestEntity('var-1', 'variable', '/src/config.ts'));
    });

    it('should filter by entity type', async () => {
      const results = await storage.queryEntities({ entityTypes: ['function'] });
      expect(results).toHaveLength(2);
      expect(results.every((e) => e.type === 'function')).toBe(true);
    });

    it('should filter by file path', async () => {
      const results = await storage.queryEntities({ filePath: '/src/user.ts' });
      expect(results).toHaveLength(2);
    });

    it('should filter by text search', async () => {
      const results = await storage.queryEntities({ textSearch: 'func' });
      expect(results).toHaveLength(2);
    });

    it('should apply limit', async () => {
      const results = await storage.queryEntities({ limit: 2 });
      expect(results).toHaveLength(2);
    });

    it('should combine filters', async () => {
      const results = await storage.queryEntities({
        entityTypes: ['function'],
        filePath: '/src/user.ts',
      });
      expect(results).toHaveLength(1);
      expect(results[0].id).toBe('func-2');
    });
  });

  describe('relation operations', () => {
    beforeEach(async () => {
      await storage.saveEntity(createTestEntity('class-a', 'class'));
      await storage.saveEntity(createTestEntity('class-b', 'class'));
      await storage.saveEntity(createTestEntity('func-x', 'function'));
    });

    it('should save and retrieve relation', async () => {
      const relation = createTestRelation('class-a', 'class-b', 'extends');
      await storage.saveRelation(relation);

      const outgoing = await storage.getRelations('class-a', 'out');
      expect(outgoing).toHaveLength(1);
      expect(outgoing[0]).toEqual(relation);

      const incoming = await storage.getRelations('class-b', 'in');
      expect(incoming).toHaveLength(1);
    });

    it('should get both directions by default', async () => {
      const rel1 = createTestRelation('class-a', 'class-b', 'extends');
      const rel2 = createTestRelation('func-x', 'class-a', 'calls');

      await storage.saveRelation(rel1);
      await storage.saveRelation(rel2);

      const both = await storage.getRelations('class-a');
      expect(both).toHaveLength(2);
    });

    it('should delete relation', async () => {
      const relation = createTestRelation('class-a', 'class-b', 'extends');
      await storage.saveRelation(relation);
      await storage.deleteRelation(relation.id);

      const relations = await storage.getRelations('class-a');
      expect(relations).toHaveLength(0);
    });
  });

  describe('bulk operations', () => {
    it('should bulk save entities and relations', async () => {
      const entities = [
        createTestEntity('bulk-1', 'class'),
        createTestEntity('bulk-2', 'class'),
        createTestEntity('bulk-3', 'function'),
      ];
      const relations = [
        createTestRelation('bulk-1', 'bulk-2', 'extends'),
        createTestRelation('bulk-3', 'bulk-1', 'calls'),
      ];

      await storage.bulkSave(entities, relations);

      const stats = await storage.getStats();
      expect(stats.entityCount).toBe(3);
      expect(stats.relationCount).toBe(2);
    });

    it('should clear all data', async () => {
      await storage.saveEntity(createTestEntity('to-clear', 'class'));
      await storage.clear();

      const stats = await storage.getStats();
      expect(stats.entityCount).toBe(0);
      expect(stats.relationCount).toBe(0);
    });
  });

  describe('statistics', () => {
    it('should count entities and relations', async () => {
      await storage.saveEntity(createTestEntity('stat-1', 'class', '/a.ts'));
      await storage.saveEntity(createTestEntity('stat-2', 'class', '/b.ts'));
      await storage.saveRelation(createTestRelation('stat-1', 'stat-2', 'extends'));

      const stats = await storage.getStats();
      expect(stats.entityCount).toBe(2);
      expect(stats.relationCount).toBe(1);
      expect(stats.fileCount).toBe(2);
    });

    it('should count unique files', async () => {
      await storage.saveEntity(createTestEntity('same-1', 'class', '/same.ts'));
      await storage.saveEntity(createTestEntity('same-2', 'function', '/same.ts'));

      const stats = await storage.getStats();
      expect(stats.fileCount).toBe(1);
    });
  });

  describe('helper methods', () => {
    beforeEach(async () => {
      await storage.saveEntity(createTestEntity('UserService', 'class'));
      await storage.saveEntity(createTestEntity('UserRepository', 'class'));
      await storage.saveEntity(createTestEntity('createUser', 'function'));
    });

    it('should find by name (partial match)', async () => {
      const results = await storage.findByName('User');
      // UserService, UserRepository, createUser all contain 'User'
      expect(results).toHaveLength(3);
    });

    it('should find by name (exact match)', async () => {
      const results = await storage.findByName('UserService', true);
      expect(results).toHaveLength(1);
      expect(results[0].name).toBe('UserService');
    });

    it('should get entities by type', async () => {
      const results = await storage.getEntitiesByType('class');
      expect(results).toHaveLength(2);
    });

    it('should get relations by type', async () => {
      await storage.saveRelation(createTestRelation('UserService', 'UserRepository', 'calls'));
      await storage.saveRelation(createTestRelation('UserService', 'createUser', 'calls'));

      const results = await storage.getRelationsByType('calls');
      expect(results).toHaveLength(2);
    });
  });
});

// ============================================================================
// Test Helpers
// ============================================================================

function createTestEntity(
  id: string,
  type: EntityType,
  filePath?: string
): Entity {
  return {
    id,
    name: id,
    type,
    language: 'typescript',
    filePath,
    startLine: 1,
    endLine: 10,
    sourceCode: `// ${id}`,
  };
}

function createTestRelation(
  sourceId: string,
  targetId: string,
  type: RelationType
): Relation {
  return {
    id: `${sourceId}-${type}-${targetId}`,
    sourceId,
    targetId,
    type,
  };
}
