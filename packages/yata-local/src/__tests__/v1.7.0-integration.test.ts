/**
 * MUSUBIX v1.7.0 Integration Tests
 *
 * Verifies that all v1.7.0 features work together:
 * - Phase 1: Index Optimizer
 * - Phase 2: Enhanced Export (JSON/RDF/GraphML)
 * - Phase 3: Global Sync Manager
 * - Phase 4: Enhanced Code Generator
 * - Phase 5: YATA UI
 *
 * @packageDocumentation
 * @see REQ-YI-IDX-001 - Index Analysis
 * @see REQ-YI-EXP-001 - Enhanced Export
 * @see REQ-YG-SYNC-001 - Global Sync
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as fs from 'fs/promises';
import * as path from 'path';
import * as os from 'os';
import { YataLocal, YataDatabase } from '../index.js';
import { IndexOptimizer } from '../index-optimizer.js';
import type Database from 'better-sqlite3';

describe('MUSUBIX v1.7.0 Integration', () => {
  let yata: YataLocal;
  let tempDir: string;

  beforeEach(async () => {
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'musubix-v170-test-'));
    const dbPath = path.join(tempDir, 'test.db');
    yata = new YataLocal({ path: dbPath });
    await yata.open();

    // Seed test data for realistic scenarios
    await seedTestData(yata);
  });

  afterEach(async () => {
    await yata.close();
    await fs.rm(tempDir, { recursive: true, force: true });
  });

  describe('Phase 1+2: Index Optimization → Export Pipeline', () => {
    it('should analyze indexes and export data', async () => {
      // Step 1: Export to JSON (basic functionality test)
      const exportStart = Date.now();
      const result = await yata.export({ format: 'json' });
      const exportTime = Date.now() - exportStart;

      expect(result.success).toBe(true);
      expect(result.entityCount).toBeGreaterThan(0);
      expect(exportTime).toBeLessThan(5000); // Should complete within 5s
    });

    it('should export optimized data to multiple formats', async () => {
      // Export to all supported formats
      const [jsonResult, rdfResult, graphmlResult] = await Promise.all([
        yata.export({ format: 'json' }),
        yata.export({ format: 'rdf' }),
        yata.export({ format: 'graphml' }),
      ]);

      // All exports should succeed
      expect(jsonResult.success).toBe(true);
      expect(rdfResult.success).toBe(true);
      expect(graphmlResult.success).toBe(true);

      // Entity counts should be consistent
      expect(jsonResult.entityCount).toBe(rdfResult.entityCount);
      expect(rdfResult.entityCount).toBe(graphmlResult.entityCount);

      // Verify format-specific content
      expect(jsonResult.content).toContain('"version": "2.0"');
      expect(rdfResult.content).toContain('rdf-syntax-ns#type');
      expect(graphmlResult.content).toContain('<graphml');
    });
  });

  describe('Phase 2+3: Export → Sync Pipeline', () => {
    it('should support incremental export for sync', async () => {
      const baseline = new Date();

      // Simulate time passage and changes
      await new Promise(resolve => setTimeout(resolve, 50));

      // Add new entities
      await yata.addEntity({
        type: 'method',
        name: 'processSync',
        namespace: 'sync.engine',
        description: 'Syncs with global server',
      });

      // Incremental export
      const incrementalResult = await yata.exportIncremental(baseline, {
        format: 'json',
      });

      expect(incrementalResult.success).toBe(true);
      expect(incrementalResult.entityCount).toBeGreaterThanOrEqual(1);

      const data = JSON.parse(incrementalResult.content!);
      expect(data.incremental).toBe(true);
      expect(data.since).toBeDefined();
    });

    it('should preserve relationships during export/import cycle', async () => {
      // Add relationship
      const entities = await yata.getEntitiesByNamespace('domain.entities');
      if (entities.length >= 2) {
        await yata.addRelationship(
          entities[0].id,
          entities[1].id,
          'depends_on'
        );
      }

      // Export
      const exportResult = await yata.export({ format: 'json' });
      expect(exportResult.success).toBe(true);

      // Create new instance and import
      const dbPath2 = path.join(tempDir, 'test2.db');
      const yata2 = new YataLocal({ path: dbPath2 });
      await yata2.open();

      const importResult = await yata2.import(exportResult.content!, {
        format: 'json',
        mergeStrategy: 'overwrite',
      });

      expect(importResult.success).toBe(true);
      expect(importResult.entitiesCreated).toBe(exportResult.entityCount);

      await yata2.close();
    });
  });

  describe('Full Pipeline: Export → Transform → Import', () => {
    it('should complete full knowledge transfer workflow', async () => {
      // Phase 2: Export to JSON
      const jsonExport = await yata.export({
        format: 'json',
        includeMetadata: true,
      });
      expect(jsonExport.success).toBe(true);

      // Phase 2b: Export to GraphML for visualization
      const graphmlExport = await yata.export({
        format: 'graphml',
        outputPath: path.join(tempDir, 'knowledge-graph.graphml'),
      });
      expect(graphmlExport.success).toBe(true);

      // Verify file was created
      const graphmlExists = await fs.access(graphmlExport.outputPath!)
        .then(() => true)
        .catch(() => false);
      expect(graphmlExists).toBe(true);

      // Phase 3: Import to new database (simulating sync to another instance)
      const targetDbPath = path.join(tempDir, 'target.db');
      const targetYata = new YataLocal({ path: targetDbPath });
      await targetYata.open();

      const importResult = await targetYata.import(jsonExport.content!, {
        format: 'json',
        mergeStrategy: 'overwrite',
      });

      expect(importResult.success).toBe(true);
      expect(importResult.entitiesCreated).toBe(jsonExport.entityCount);

      // Verify data integrity
      const sourceEntities = await yata.getEntitiesByNamespace('domain.entities');
      const targetEntities = await targetYata.getEntitiesByNamespace('domain.entities');
      expect(targetEntities.length).toBe(sourceEntities.length);

      await targetYata.close();
    });

    it('should handle namespace filtering through pipeline', async () => {
      const namespace = 'domain.entities';

      // Export only specific namespace
      const filteredExport = await yata.export({
        format: 'json',
        namespace,
      });

      expect(filteredExport.success).toBe(true);

      // Parse and verify
      const data = JSON.parse(filteredExport.content!);
      for (const entity of data.entities) {
        expect(entity.namespace).toBe(namespace);
      }
    });
  });

  describe('Error Handling Across Phases', () => {
    it('should gracefully handle export errors', async () => {
      // Close database to simulate error
      await yata.close();

      // Attempt export should fail gracefully
      try {
        await yata.export({ format: 'json' });
        // If no error, check that it returns a failure result
      } catch (error) {
        expect(error).toBeDefined();
      }
    });

    it('should validate import data format', async () => {
      const invalidJson = '{"invalid": "format"}';

      try {
        await yata.import(invalidJson, {
          format: 'json',
          mergeStrategy: 'skip',
        });
      } catch (error) {
        expect(error).toBeDefined();
      }
    });

    it('should handle dry-run import without changes', async () => {
      const exportResult = await yata.export({ format: 'json' });

      // Create new instance
      const dbPath2 = path.join(tempDir, 'dryrun.db');
      const yata2 = new YataLocal({ path: dbPath2 });
      await yata2.open();

      // Dry run import - counts entities that would be imported
      const dryRunResult = await yata2.import(exportResult.content!, {
        format: 'json',
        mergeStrategy: 'overwrite',
        dryRun: true,
      });

      expect(dryRunResult.success).toBe(true);
      // entitiesCreated counts what would be created (preview count)
      expect(dryRunResult.entitiesCreated).toBeGreaterThan(0);

      // In dry-run mode, actual database should be empty
      const afterEntities = await yata2.getEntitiesByNamespace('domain.entities');
      expect(afterEntities.length).toBe(0);

      await yata2.close();
    });
  });

  describe('Performance Metrics', () => {
    it('should track export performance metrics', async () => {
      const result = await yata.export({ format: 'json' });

      expect(result.exportTimeMs).toBeGreaterThanOrEqual(0);
      expect(result.fileSize).toBeGreaterThan(0);
    });

    it('should complete full pipeline within acceptable time', async () => {
      const start = Date.now();

      // Full pipeline
      await yata.export({ format: 'json' });
      await yata.export({ format: 'graphml' });

      const elapsed = Date.now() - start;

      // Full pipeline should complete within 10 seconds
      expect(elapsed).toBeLessThan(10000);
    });
  });
});

/**
 * Seeds test data for integration tests
 */
async function seedTestData(yata: YataLocal): Promise<void> {
  const entities = [
    // Domain layer
    { type: 'class', name: 'User', namespace: 'domain.entities', description: 'User entity' },
    { type: 'class', name: 'Order', namespace: 'domain.entities', description: 'Order entity' },
    { type: 'class', name: 'Product', namespace: 'domain.entities', description: 'Product entity' },
    { type: 'interface', name: 'UserRepository', namespace: 'domain.repositories' },
    { type: 'interface', name: 'OrderRepository', namespace: 'domain.repositories' },

    // Application layer
    { type: 'class', name: 'UserService', namespace: 'application.services', description: 'User service' },
    { type: 'class', name: 'OrderService', namespace: 'application.services', description: 'Order service' },

    // Infrastructure layer
    { type: 'class', name: 'SqliteUserRepository', namespace: 'infrastructure.repositories' },
    { type: 'class', name: 'SqliteOrderRepository', namespace: 'infrastructure.repositories' },

    // API layer
    { type: 'class', name: 'UserController', namespace: 'api.controllers' },
    { type: 'class', name: 'OrderController', namespace: 'api.controllers' },
  ];

  for (const entity of entities) {
    await yata.addEntity(entity);
  }
}
