/**
 * @nahisaho/musubix-codegraph - Knowledge Adapter Tests
 *
 * Tests for the @musubix/knowledge storage adapter.
 *
 * @see REQ-CG-API-005
 * @see DES-CG-006
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { KnowledgeAdapter } from '../src/storage/knowledge-adapter.js';
import { createKnowledgeStore } from '@musubix/knowledge';
import type { KnowledgeStore } from '@musubix/knowledge';
import type { Entity, Relation, EntityType, RelationType } from '../src/types.js';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';

describe('KnowledgeAdapter', () => {
  let adapter: KnowledgeAdapter;
  let store: KnowledgeStore;
  let tmpDir: string;

  beforeEach(async () => {
    tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), 'codegraph-ka-'));
    store = createKnowledgeStore(tmpDir);
    adapter = new KnowledgeAdapter(store);
    await adapter.initialize();
  });

  afterEach(async () => {
    await adapter.close();
    await fs.rm(tmpDir, { recursive: true, force: true });
  });

  describe('lifecycle', () => {
    it('should initialize successfully', async () => {
      const newAdapter = new KnowledgeAdapter(createKnowledgeStore(tmpDir));
      expect(newAdapter.isInitialized()).toBe(false);
      await newAdapter.initialize();
      expect(newAdapter.isInitialized()).toBe(true);
      await newAdapter.close();
    });

    it('should be idempotent on initialize', async () => {
      await adapter.initialize(); // second call
      expect(adapter.isInitialized()).toBe(true);
    });

    it('should close and reset state', async () => {
      await adapter.saveEntity(createTestEntity('test-1', 'class'));
      await adapter.close();
      expect(adapter.isInitialized()).toBe(false);
    });
  });

  describe('entity operations', () => {
    it('should save and retrieve entity', async () => {
      const entity = createTestEntity('func-1', 'function');
      await adapter.saveEntity(entity);

      const retrieved = await adapter.getEntity('func-1');
      expect(retrieved).not.toBeNull();
      expect(retrieved!.id).toBe('func-1');
      expect(retrieved!.name).toBe('func-1');
      expect(retrieved!.type).toBe('function');
    });

    it('should return null for non-existent entity', async () => {
      const result = await adapter.getEntity('non-existent');
      expect(result).toBeNull();
    });

    it('should preserve entity fields through round-trip', async () => {
      const entity: Entity = {
        id: 'detailed-1',
        type: 'class',
        name: 'UserService',
        qualifiedName: 'app.services.UserService',
        namespace: 'app.services',
        filePath: '/src/services/user.ts',
        startLine: 10,
        endLine: 50,
        signature: 'class UserService',
        docstring: 'User service for managing users',
        sourceCode: 'class UserService { }',
        communityId: 'comm-1',
        language: 'typescript',
        metadata: { complexity: 5, isPublic: true },
      };

      await adapter.saveEntity(entity);
      const retrieved = await adapter.getEntity('detailed-1');

      expect(retrieved).not.toBeNull();
      expect(retrieved!.id).toBe('detailed-1');
      expect(retrieved!.type).toBe('class');
      expect(retrieved!.name).toBe('UserService');
      expect(retrieved!.qualifiedName).toBe('app.services.UserService');
      expect(retrieved!.namespace).toBe('app.services');
      expect(retrieved!.filePath).toBe('/src/services/user.ts');
      expect(retrieved!.startLine).toBe(10);
      expect(retrieved!.endLine).toBe(50);
      expect(retrieved!.signature).toBe('class UserService');
      expect(retrieved!.docstring).toBe('User service for managing users');
      expect(retrieved!.sourceCode).toBe('class UserService { }');
      expect(retrieved!.communityId).toBe('comm-1');
      expect(retrieved!.language).toBe('typescript');
      expect(retrieved!.metadata).toEqual({ complexity: 5, isPublic: true });
    });

    it('should delete entity', async () => {
      const entity = createTestEntity('delete-me', 'class');
      await adapter.saveEntity(entity);
      await adapter.deleteEntity('delete-me');

      const result = await adapter.getEntity('delete-me');
      expect(result).toBeNull();
    });

    it('should update existing entity', async () => {
      const entity = createTestEntity('update-me', 'class');
      await adapter.saveEntity(entity);

      const updated = { ...entity, name: 'UpdatedName' };
      await adapter.saveEntity(updated);

      const retrieved = await adapter.getEntity('update-me');
      expect(retrieved!.name).toBe('UpdatedName');
    });
  });

  describe('query operations', () => {
    beforeEach(async () => {
      await adapter.saveEntity(createTestEntity('class-1', 'class', '/src/user.ts'));
      await adapter.saveEntity(createTestEntity('func-1', 'function', '/src/utils.ts'));
      await adapter.saveEntity(createTestEntity('func-2', 'function', '/src/user.ts'));
      await adapter.saveEntity(createTestEntity('var-1', 'variable', '/src/config.ts'));
    });

    it('should filter by entity type', async () => {
      const results = await adapter.queryEntities({ entityTypes: ['function'] });
      expect(results).toHaveLength(2);
      expect(results.every((e) => e.type === 'function')).toBe(true);
    });

    it('should filter by file path', async () => {
      const results = await adapter.queryEntities({ filePath: '/src/user.ts' });
      expect(results).toHaveLength(2);
    });

    it('should filter by text search', async () => {
      const results = await adapter.queryEntities({ textSearch: 'func' });
      expect(results).toHaveLength(2);
    });

    it('should apply limit', async () => {
      const results = await adapter.queryEntities({ limit: 2 });
      expect(results).toHaveLength(2);
    });

    it('should combine filters', async () => {
      const results = await adapter.queryEntities({
        entityTypes: ['function'],
        filePath: '/src/user.ts',
      });
      expect(results).toHaveLength(1);
      expect(results[0].id).toBe('func-2');
    });
  });

  describe('relation operations', () => {
    beforeEach(async () => {
      await adapter.saveEntity(createTestEntity('class-a', 'class'));
      await adapter.saveEntity(createTestEntity('class-b', 'class'));
      await adapter.saveEntity(createTestEntity('func-x', 'function'));
    });

    it('should save and retrieve relation', async () => {
      const relation = createTestRelation('class-a', 'class-b', 'extends');
      await adapter.saveRelation(relation);

      const outgoing = await adapter.getRelations('class-a', 'out');
      expect(outgoing).toHaveLength(1);
      expect(outgoing[0].sourceId).toBe('class-a');
      expect(outgoing[0].targetId).toBe('class-b');
      expect(outgoing[0].type).toBe('extends');

      const incoming = await adapter.getRelations('class-b', 'in');
      expect(incoming).toHaveLength(1);
    });

    it('should get both directions by default', async () => {
      const rel1 = createTestRelation('class-a', 'class-b', 'extends');
      const rel2 = createTestRelation('func-x', 'class-a', 'calls');

      await adapter.saveRelation(rel1);
      await adapter.saveRelation(rel2);

      const both = await adapter.getRelations('class-a');
      expect(both).toHaveLength(2);
    });

    it('should delete relation', async () => {
      const relation = createTestRelation('class-a', 'class-b', 'extends');
      await adapter.saveRelation(relation);
      await adapter.deleteRelation(relation.id);

      const relations = await adapter.getRelations('class-a');
      expect(relations).toHaveLength(0);
    });

    it('should preserve relation type through round-trip', async () => {
      const relation = createTestRelation('class-a', 'class-b', 'implements');
      await adapter.saveRelation(relation);

      const retrieved = await adapter.getRelations('class-a', 'out');
      expect(retrieved).toHaveLength(1);
      expect(retrieved[0].type).toBe('implements');
    });

    it('should handle non-shared relation types', async () => {
      const relation = createTestRelation('class-a', 'func-x', 'calls');
      await adapter.saveRelation(relation);

      const retrieved = await adapter.getRelations('class-a', 'out');
      expect(retrieved).toHaveLength(1);
      expect(retrieved[0].type).toBe('calls');
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

      await adapter.bulkSave(entities, relations);

      const stats = await adapter.getStats();
      expect(stats.entityCount).toBe(3);
      expect(stats.relationCount).toBe(2);
    });

    it('should clear all data', async () => {
      await adapter.saveEntity(createTestEntity('to-clear', 'class'));
      await adapter.clear();

      const stats = await adapter.getStats();
      expect(stats.entityCount).toBe(0);
      expect(stats.relationCount).toBe(0);
    });
  });

  describe('statistics', () => {
    it('should count entities and relations', async () => {
      await adapter.saveEntity(createTestEntity('stat-1', 'class', '/a.ts'));
      await adapter.saveEntity(createTestEntity('stat-2', 'class', '/b.ts'));
      await adapter.saveRelation(createTestRelation('stat-1', 'stat-2', 'extends'));

      const stats = await adapter.getStats();
      expect(stats.entityCount).toBe(2);
      expect(stats.relationCount).toBe(1);
      expect(stats.fileCount).toBe(2);
    });

    it('should count unique files', async () => {
      await adapter.saveEntity(createTestEntity('same-1', 'class', '/same.ts'));
      await adapter.saveEntity(createTestEntity('same-2', 'function', '/same.ts'));

      const stats = await adapter.getStats();
      expect(stats.fileCount).toBe(1);
    });
  });

  describe('persistence', () => {
    it('should persist data with autoSave', async () => {
      const autoAdapter = new KnowledgeAdapter(store, { autoSave: true });
      await autoAdapter.initialize();

      await autoAdapter.saveEntity(createTestEntity('persist-1', 'class'));
      await autoAdapter.close();

      // Reopen and verify
      const store2 = createKnowledgeStore(tmpDir);
      const adapter2 = new KnowledgeAdapter(store2);
      await adapter2.initialize();

      const retrieved = await adapter2.getEntity('persist-1');
      expect(retrieved).not.toBeNull();
      expect(retrieved!.name).toBe('persist-1');

      await adapter2.close();
    });

    it('should persist data with explicit save', async () => {
      await adapter.saveEntity(createTestEntity('explicit-1', 'function'));
      await adapter.save();

      // Reopen and verify
      const store2 = createKnowledgeStore(tmpDir);
      const adapter2 = new KnowledgeAdapter(store2);
      await adapter2.initialize();

      const retrieved = await adapter2.getEntity('explicit-1');
      expect(retrieved).not.toBeNull();

      await adapter2.close();
    });
  });

  describe('edge cases', () => {
    it('should handle entity without optional fields', async () => {
      const minimal: Entity = {
        id: 'minimal-1',
        type: 'unknown',
        name: 'minimal',
        metadata: {},
      };

      await adapter.saveEntity(minimal);
      const retrieved = await adapter.getEntity('minimal-1');

      expect(retrieved).not.toBeNull();
      expect(retrieved!.id).toBe('minimal-1');
      expect(retrieved!.type).toBe('unknown');
      expect(retrieved!.name).toBe('minimal');
    });

    it('should handle deleting non-existent entity gracefully', async () => {
      // Should not throw
      await adapter.deleteEntity('does-not-exist');
    });

    it('should handle querying empty store', async () => {
      const results = await adapter.queryEntities({ entityTypes: ['class'] });
      expect(results).toHaveLength(0);
    });

    it('should handle getting relations for non-existent entity', async () => {
      const relations = await adapter.getRelations('non-existent');
      expect(relations).toHaveLength(0);
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
    metadata: {},
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
    weight: 1,
    metadata: {},
  };
}
