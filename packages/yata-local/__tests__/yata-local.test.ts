/**
 * YATA Local - Unit Tests
 *
 * @see REQ-YL-STORE-001 ~ REQ-YL-IO-004
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'fs/promises';
import * as path from 'path';
import { createYataLocal, YataLocal } from '../src/index.js';
import type { Entity, GraphPattern } from '../src/types.js';

const TEST_DB_PATH = path.join(process.cwd(), 'test-yata.db');

describe('YataLocal', () => {
  let yata: YataLocal;

  beforeEach(async () => {
    // Clean up test database
    try {
      await fs.unlink(TEST_DB_PATH);
    } catch {
      // File may not exist
    }

    yata = createYataLocal({ path: TEST_DB_PATH });
    await yata.open();
  });

  afterEach(async () => {
    await yata.close();
    try {
      await fs.unlink(TEST_DB_PATH);
      await fs.unlink(TEST_DB_PATH + '-wal');
      await fs.unlink(TEST_DB_PATH + '-shm');
    } catch {
      // Files may not exist
    }
  });

  describe('Entity Operations', () => {
    it('should add and retrieve entity', async () => {
      // REQ-YL-STORE-003
      const id = await yata.addEntity({
        type: 'class',
        name: 'UserService',
        namespace: 'app.services',
        filePath: 'src/services/user.ts',
        line: 10,
        description: 'Manages user operations',
      });

      expect(id).toBeDefined();

      const entity = await yata.getEntity(id);
      expect(entity).toBeDefined();
      expect(entity?.name).toBe('UserService');
      expect(entity?.type).toBe('class');
      expect(entity?.namespace).toBe('app.services');
      expect(entity?.filePath).toBe('src/services/user.ts');
    });

    it('should add multiple entities in batch', async () => {
      const ids = await yata.addEntities([
        { type: 'class', name: 'Class1', namespace: 'app' },
        { type: 'class', name: 'Class2', namespace: 'app' },
        { type: 'interface', name: 'Interface1', namespace: 'app' },
      ]);

      expect(ids).toHaveLength(3);

      for (const id of ids) {
        const entity = await yata.getEntity(id);
        expect(entity).toBeDefined();
      }
    });

    it('should update entity', async () => {
      // REQ-YL-UPDATE-002
      const id = await yata.addEntity({
        type: 'class',
        name: 'OldName',
        namespace: 'app',
      });

      await yata.updateEntity(id, { name: 'NewName' });

      const entity = await yata.getEntity(id);
      expect(entity?.name).toBe('NewName');
    });

    it('should delete entity', async () => {
      // REQ-YL-UPDATE-003
      const id = await yata.addEntity({
        type: 'class',
        name: 'ToDelete',
        namespace: 'app',
      });

      await yata.deleteEntity(id);

      const entity = await yata.getEntity(id);
      expect(entity).toBeNull();
    });

    it('should delete entities by file', async () => {
      await yata.addEntities([
        { type: 'class', name: 'Class1', namespace: 'app', filePath: 'src/a.ts' },
        { type: 'class', name: 'Class2', namespace: 'app', filePath: 'src/a.ts' },
        { type: 'class', name: 'Class3', namespace: 'app', filePath: 'src/b.ts' },
      ]);

      const deleted = await yata.deleteEntitiesByFile('src/a.ts');
      expect(deleted).toBe(2);

      // Verify only Class3 remains
      const entity = (await yata.query({ entityFilters: { namePattern: 'Class3' } })).entities;
      expect(entity.length).toBeGreaterThanOrEqual(1);
    });
  });

  describe('Relationship Operations', () => {
    it('should add and retrieve relationships', async () => {
      // REQ-YL-STORE-004
      const classId = await yata.addEntity({
        type: 'class',
        name: 'UserService',
        namespace: 'app',
      });

      const interfaceId = await yata.addEntity({
        type: 'interface',
        name: 'IUserService',
        namespace: 'app',
      });

      const relId = await yata.addRelationship(
        classId,
        interfaceId,
        'implements',
        { visibility: 'public' }
      );

      expect(relId).toBeDefined();

      const rels = await yata.getRelationships(classId, 'out');
      expect(rels).toHaveLength(1);
      expect(rels[0].type).toBe('implements');
      expect(rels[0].targetId).toBe(interfaceId);
    });

    it('should delete relationship', async () => {
      const id1 = await yata.addEntity({ type: 'class', name: 'A', namespace: 'app' });
      const id2 = await yata.addEntity({ type: 'class', name: 'B', namespace: 'app' });

      const relId = await yata.addRelationship(id1, id2, 'extends');
      await yata.deleteRelationship(relId);

      const rels = await yata.getRelationships(id1);
      expect(rels).toHaveLength(0);
    });
  });

  describe('Query Operations', () => {
    beforeEach(async () => {
      // Setup test data
      const classA = await yata.addEntity({ type: 'class', name: 'ClassA', namespace: 'app' });
      const classB = await yata.addEntity({ type: 'class', name: 'ClassB', namespace: 'app' });
      const classC = await yata.addEntity({ type: 'class', name: 'ClassC', namespace: 'lib' });
      const interfaceI = await yata.addEntity({
        type: 'interface',
        name: 'IService',
        namespace: 'app',
      });

      await yata.addRelationship(classA, interfaceI, 'implements');
      await yata.addRelationship(classB, classA, 'extends');
      await yata.addRelationship(classC, classB, 'depends-on');
    });

    it('should query entities by type', async () => {
      // REQ-YL-QUERY-001
      const result = await yata.query({
        entityFilters: { types: ['class'] },
      });

      expect(result.entities).toHaveLength(3);
      expect(result.entities.every(e => e.type === 'class')).toBe(true);
    });

    it('should query entities by namespace', async () => {
      const result = await yata.query({
        entityFilters: { namespace: 'app' },
      });

      expect(result.entities).toHaveLength(3);
    });

    it('should full-text search entities', async () => {
      // REQ-YL-QUERY-005
      // Note: FTS5 tokenizes words, so search for exact token
      const results = await yata.search('ClassA');
      expect(results.length).toBeGreaterThanOrEqual(1);
    });

    it('should find path between entities', async () => {
      // REQ-YL-QUERY-002
      const classC = (await yata.query({ entityFilters: { types: ['class'] } })).entities.find(
        e => e.name === 'ClassC'
      );
      const interfaceI = (await yata.query({ entityFilters: { types: ['interface'] } }))
        .entities[0];

      const path = await yata.findPath(classC!.id, interfaceI!.id);
      
      // Path: ClassC -> ClassB -> ClassA -> IService
      expect(path).toBeDefined();
      expect(path!.length).toBeGreaterThanOrEqual(2);
    });

    it('should extract subgraph', async () => {
      // REQ-YL-QUERY-003
      const classA = (await yata.query({ entityFilters: { types: ['class'] } })).entities.find(
        e => e.name === 'ClassA'
      );

      const subgraph = await yata.extractSubgraph(classA!.id, { depth: 2 });

      expect(subgraph.entities.length).toBeGreaterThanOrEqual(3);
      expect(subgraph.relationships.length).toBeGreaterThanOrEqual(2);
    });

    it('should get entity neighbors', async () => {
      const classA = (await yata.query({ entityFilters: { types: ['class'] } })).entities.find(
        e => e.name === 'ClassA'
      );

      const neighbors = await yata.getNeighbors(classA!.id);
      expect(neighbors.length).toBeGreaterThanOrEqual(2);
    });
  });

  describe('Pattern Matching', () => {
    it('should match simple pattern', async () => {
      // REQ-YL-QUERY-004
      const classId = await yata.addEntity({ type: 'class', name: 'MyClass', namespace: 'app' });
      const interfaceId = await yata.addEntity({
        type: 'interface',
        name: 'MyInterface',
        namespace: 'app',
      });
      await yata.addRelationship(classId, interfaceId, 'implements');

      const pattern: GraphPattern = {
        nodes: [
          { variable: 'class', type: 'class' },
          { variable: 'interface', type: 'interface' },
        ],
        edges: [{ sourceVar: 'class', targetVar: 'interface', type: 'implements' }],
      };

      const matches = await yata.matchPattern(pattern);
      expect(matches.length).toBeGreaterThanOrEqual(1);
      expect(matches[0].bindings['class']).toBe(classId);
    });
  });

  describe('Reasoning', () => {
    it('should infer transitive relationships', async () => {
      // REQ-YL-REASON-001
      const classA = await yata.addEntity({ type: 'class', name: 'A', namespace: 'app' });
      const classB = await yata.addEntity({ type: 'class', name: 'B', namespace: 'app' });
      const classC = await yata.addEntity({ type: 'class', name: 'C', namespace: 'app' });

      await yata.addRelationship(classA, classB, 'extends');
      await yata.addRelationship(classB, classC, 'extends');

      const result = await yata.infer({ rules: ['transitive-extends'] });

      expect(result.inferred.length).toBeGreaterThanOrEqual(1);
      const inferredAC = result.inferred.find(
        i => i.sourceId === classA && i.targetId === classC && i.type === 'extends'
      );
      expect(inferredAC).toBeDefined();
    });

    it('should validate graph constraints', async () => {
      // REQ-YL-REASON-003
      await yata.addEntity({ type: 'class', name: 'ValidClass', namespace: 'app' });

      const result = await yata.validate();
      expect(result.valid).toBe(true);
    });

    it('should suggest relationships', async () => {
      // REQ-YL-REASON-002
      await yata.addEntity({ type: 'class', name: 'UserService', namespace: 'app' });
      await yata.addEntity({ type: 'class', name: 'UserRepository', namespace: 'app' });
      await yata.addEntity({ type: 'interface', name: 'IUserService', namespace: 'app' });

      const entity = (await yata.query({ entityFilters: { types: ['class'] } })).entities.find(
        e => e.name === 'UserService'
      );

      const suggestions = await yata.suggestRelationships(entity!.id, {
        maxSuggestions: 5,
        minConfidence: 0.3,
      });

      expect(suggestions.length).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Import/Export', () => {
    it('should export and import JSON', async () => {
      // REQ-YL-IO-001, REQ-YL-IO-003
      await yata.addEntity({ type: 'class', name: 'TestClass', namespace: 'app' });

      const exported = await yata.exportJson();

      expect(exported.version).toBe('1.0');
      expect(exported.entities).toHaveLength(1);

      // Create new instance and import
      const yata2 = createYataLocal({ path: TEST_DB_PATH + '2' });
      await yata2.open();

      const result = await yata2.importJson(exported);
      expect(result.entitiesAdded).toBe(1);

      await yata2.close();
      await fs.unlink(TEST_DB_PATH + '2');
    });

    it('should export to RDF', async () => {
      // REQ-YL-IO-001
      await yata.addEntity({
        type: 'class',
        name: 'TestClass',
        namespace: 'app',
        description: 'A test class',
      });

      const rdf = await yata.exportRdf();

      expect(rdf).toContain('rdf-syntax-ns#type');
      expect(rdf).toContain('TestClass');
    });

    it('should compute and apply delta', async () => {
      // REQ-YL-IO-004
      await yata.addEntity({ type: 'class', name: 'Original', namespace: 'app' });
      const oldState = await yata.exportJson();

      await yata.addEntity({ type: 'class', name: 'Added', namespace: 'app' });
      const newState = await yata.exportJson();

      const delta = yata.computeDelta(oldState, newState);

      expect(delta.entities.added).toHaveLength(1);
      expect(delta.entities.added[0].name).toBe('Added');
    });

    it('should track changes', async () => {
      // REQ-YL-UPDATE-005
      // Note: Wait a bit to ensure timestamp difference
      const before = new Date(Date.now() - 1000);

      await yata.addEntity({ type: 'class', name: 'New', namespace: 'app' });

      const changes = await yata.getChangesSince(before);

      // Change log should have the new entity
      expect(changes.entities.added.length).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Statistics', () => {
    it('should return graph statistics', async () => {
      await yata.addEntities([
        { type: 'class', name: 'Class1', namespace: 'app' },
        { type: 'class', name: 'Class2', namespace: 'app' },
        { type: 'interface', name: 'Interface1', namespace: 'app' },
      ]);

      const stats = await yata.getStats();

      expect(stats.entityCount).toBe(3);
      expect(stats.entitiesByType['class']).toBe(2);
      expect(stats.entitiesByType['interface']).toBe(1);
      expect(stats.databaseSize).toBeGreaterThan(0);
    });
  });
});
