/**
 * Enhanced Export/Import Tests (v1.7.0)
 *
 * @see REQ-YI-EXP-001 - JSON/RDF/GraphML Export
 * @see REQ-YI-EXP-002 - Import with merge strategies
 * @see REQ-YI-EXP-003 - Incremental export
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'fs/promises';
import * as path from 'path';
import * as os from 'os';
import { YataLocal } from './index.js';
import type { ExportResult, ImportResult } from './io.js';

describe('Enhanced Export/Import (REQ-YI-EXP)', () => {
  let yata: YataLocal;
  let tempDir: string;

  beforeEach(async () => {
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'yata-io-test-'));
    yata = new YataLocal({ path: ':memory:' });
    await yata.open();

    // Add test data
    await yata.addEntity({
      type: 'class',
      name: 'UserService',
      namespace: 'app.services',
      description: 'User management service',
    });
    await yata.addEntity({
      type: 'interface',
      name: 'IUserRepository',
      namespace: 'app.repositories',
      description: 'User repository interface',
    });
    await yata.addEntity({
      type: 'method',
      name: 'findById',
      namespace: 'app.services',
    });
  });

  afterEach(async () => {
    await yata.close();
    await fs.rm(tempDir, { recursive: true, force: true });
  });

  describe('JSON Export (REQ-YI-EXP-001)', () => {
    it('should export to enhanced JSON format', async () => {
      const result = await yata.export({ format: 'json' });

      expect(result.success).toBe(true);
      expect(result.format).toBe('json');
      expect(result.entityCount).toBe(3);
      expect(result.exportTimeMs).toBeGreaterThanOrEqual(0);
      expect(result.content).toBeDefined();

      // Verify JSON structure
      const data = JSON.parse(result.content!);
      expect(data.version).toBe('2.0');
      expect(data.entities).toHaveLength(3);
      expect(data.stats.entityCount).toBe(3);
    });

    it('should filter by namespace', async () => {
      const result = await yata.export({
        format: 'json',
        namespace: 'app.services',
      });

      expect(result.success).toBe(true);
      expect(result.entityCount).toBe(2); // UserService and findById
    });

    it('should export to file', async () => {
      const outputPath = path.join(tempDir, 'export.json');
      const result = await yata.export({
        format: 'json',
        outputPath,
      });

      expect(result.success).toBe(true);
      expect(result.outputPath).toBe(outputPath);

      const fileContent = await fs.readFile(outputPath, 'utf-8');
      const data = JSON.parse(fileContent);
      expect(data.entities).toHaveLength(3);
    });
  });

  describe('GraphML Export (REQ-YI-EXP-001)', () => {
    it('should export to GraphML format', async () => {
      const result = await yata.export({ format: 'graphml' });

      expect(result.success).toBe(true);
      expect(result.format).toBe('graphml');
      expect(result.entityCount).toBe(3);
      expect(result.content).toBeDefined();

      // Verify GraphML structure
      expect(result.content).toContain('<?xml version="1.0"');
      expect(result.content).toContain('<graphml');
      expect(result.content).toContain('<node id=');
      expect(result.content).toContain('<data key="type">class</data>');
      expect(result.content).toContain('<data key="name">UserService</data>');
    });

    it('should include metadata when requested', async () => {
      // Add entity with metadata
      await yata.addEntity({
        type: 'class',
        name: 'MetadataEntity',
        namespace: 'test',
        metadata: { tags: ['important'], version: 1 },
      });

      const result = await yata.export({
        format: 'graphml',
        includeMetadata: true,
      });

      expect(result.content).toContain('<data key="metadata">');
    });
  });

  describe('RDF Export (REQ-YI-EXP-001)', () => {
    it('should export to RDF N-Triples format', async () => {
      const result = await yata.export({ format: 'rdf' });

      expect(result.success).toBe(true);
      expect(result.format).toBe('rdf');
      expect(result.entityCount).toBe(3);
      expect(result.content).toBeDefined();

      // Verify RDF structure
      expect(result.content).toContain('<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>');
      expect(result.content).toContain('<http://www.w3.org/2000/01/rdf-schema#label>');
      expect(result.content).toContain('"UserService"');
    });
  });

  describe('Incremental Export (REQ-YI-EXP-003)', () => {
    it('should export only changes since specified date', async () => {
      // Get current timestamp
      const beforeUpdate = new Date();

      // Wait a bit and add a new entity
      await new Promise(resolve => setTimeout(resolve, 50));

      await yata.addEntity({
        type: 'class',
        name: 'NewService',
        namespace: 'app.services',
      });

      const result = await yata.exportIncremental(beforeUpdate, { format: 'json' });

      expect(result.success).toBe(true);
      // At minimum the new entity should be included
      expect(result.entityCount).toBeGreaterThanOrEqual(1);

      const data = JSON.parse(result.content!);
      expect(data.incremental).toBe(true);
      expect(data.since).toBeDefined();
      // Verify new entity is in the results
      const newService = data.entities.find((e: { name: string }) => e.name === 'NewService');
      expect(newService).toBeDefined();
    });
  });

  describe('JSON Import (REQ-YI-EXP-002)', () => {
    let exportedContent: string;

    beforeEach(async () => {
      const result = await yata.export({ format: 'json' });
      exportedContent = result.content!;
    });

    it('should import with skip strategy', async () => {
      // Create new instance
      const yata2 = new YataLocal({ path: ':memory:' });
      await yata2.open();

      // Add conflicting entity
      await yata2.addEntity({
        type: 'class',
        name: 'ExistingUser',
        namespace: 'app.services',
      });

      // Get the ID from exported content to create conflict
      const data = JSON.parse(exportedContent);
      const firstEntityId = data.entities[0].id;

      // Add entity with same ID
      try {
        await yata2.addEntity({
          type: 'class',
          name: 'Conflict',
          namespace: 'test',
          metadata: { id: firstEntityId },
        });
      } catch {
        // May fail if ID is generated, that's OK
      }

      const result = await yata2.import(exportedContent, {
        format: 'json',
        mergeStrategy: 'skip',
      });

      expect(result.success).toBe(true);
      expect(result.format).toBe('json');
      expect(result.entitiesCreated + result.entitiesSkipped).toBe(3);

      await yata2.close();
    });

    it('should import with overwrite strategy', async () => {
      const yata2 = new YataLocal({ path: ':memory:' });
      await yata2.open();

      // First import
      await yata2.import(exportedContent, {
        format: 'json',
        mergeStrategy: 'skip',
      });

      // Modify exported content
      const data = JSON.parse(exportedContent);
      data.entities[0].name = 'UpdatedUserService';
      const modifiedContent = JSON.stringify(data);

      // Second import with overwrite
      const result = await yata2.import(modifiedContent, {
        format: 'json',
        mergeStrategy: 'overwrite',
      });

      expect(result.success).toBe(true);
      expect(result.entitiesUpdated).toBeGreaterThan(0);

      await yata2.close();
    });

    it('should support dry run', async () => {
      const yata2 = new YataLocal({ path: ':memory:' });
      await yata2.open();

      const result = await yata2.import(exportedContent, {
        format: 'json',
        mergeStrategy: 'skip',
        dryRun: true,
      });

      expect(result.success).toBe(true);
      expect(result.entitiesCreated).toBe(3);

      // Verify nothing was actually imported
      const stats = await yata2.getStats();
      expect(stats.entityCount).toBe(0);

      await yata2.close();
    });
  });

  describe('GraphML Import (REQ-YI-EXP-002)', () => {
    it('should import from GraphML format', async () => {
      // Export to GraphML
      const exportResult = await yata.export({ format: 'graphml' });

      // Create new instance and import
      const yata2 = new YataLocal({ path: ':memory:' });
      await yata2.open();

      const importResult = await yata2.import(exportResult.content!, {
        format: 'graphml',
        mergeStrategy: 'skip',
      });

      expect(importResult.success).toBe(true);
      expect(importResult.format).toBe('graphml');
      expect(importResult.entitiesCreated).toBe(3);

      await yata2.close();
    });
  });

  describe('Export Performance (REQ-YI-EXP-001)', () => {
    it('should export 1000 entities within acceptable time', async () => {
      // Add more entities
      for (let i = 0; i < 1000; i++) {
        await yata.addEntity({
          type: 'class',
          name: `Entity${i}`,
          namespace: 'performance.test',
        });
      }

      const startTime = Date.now();
      const result = await yata.export({ format: 'json' });
      const duration = Date.now() - startTime;

      expect(result.success).toBe(true);
      expect(result.entityCount).toBeGreaterThanOrEqual(1000);
      // Should complete well under 30 second target
      expect(duration).toBeLessThan(5000);
    });
  });
});
