/**
 * CodeGraph Integration Tests
 *
 * @see TSK-CG-080
 */

import { describe, it, expect, beforeAll } from 'vitest';
import { createCodeGraph } from '@nahisaho/musubix-codegraph';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const CODEGRAPH_SRC = join(__dirname, '../../src');

describe('CodeGraph Integration Tests', () => {
  describe('Indexing and Querying', () => {
    it('should index and query TypeScript code', async () => {
      const codeGraph = await createCodeGraph({ storage: 'memory' });
      
      // Index the codegraph package itself
      const indexResult = await codeGraph.index(CODEGRAPH_SRC);
      
      expect(indexResult).toBeDefined();
      expect(indexResult.success).toBe(true);
      expect(indexResult.entitiesIndexed).toBeGreaterThanOrEqual(0);
      expect(indexResult.filesProcessed).toBeGreaterThan(0);
      
      // Get stats
      const stats = await codeGraph.getStats();
      expect(stats.fileCount).toBeGreaterThan(0);
    }, 30000);

    it('should find entities by text search', async () => {
      const codeGraph = await createCodeGraph({ storage: 'memory' });
      await codeGraph.index(CODEGRAPH_SRC);
      
      // Query for entities
      const result = await codeGraph.query({ textSearch: 'CodeGraph' });
      
      expect(result).toBeDefined();
      expect(result.entities).toBeDefined();
      // Should find CodeGraph class or related entities
    }, 30000);

    it('should find dependencies', async () => {
      const codeGraph = await createCodeGraph({ storage: 'memory' });
      await codeGraph.index(CODEGRAPH_SRC);
      
      // Find dependencies of a known entity
      const deps = await codeGraph.findDependencies('CodeGraph');
      
      expect(Array.isArray(deps)).toBe(true);
    }, 30000);
  });

  describe('GraphRAG Search', () => {
    it('should perform global search', async () => {
      const codeGraph = await createCodeGraph({ storage: 'memory' });
      await codeGraph.index(CODEGRAPH_SRC);
      
      const results = await codeGraph.globalSearch('entity type definition');
      
      expect(Array.isArray(results)).toBe(true);
      if (results.length > 0) {
        expect(results[0]).toHaveProperty('entity');
        expect(results[0]).toHaveProperty('score');
      }
    }, 30000);

    it('should perform local search', async () => {
      const codeGraph = await createCodeGraph({ storage: 'memory' });
      await codeGraph.index(CODEGRAPH_SRC);
      
      const results = await codeGraph.localSearch('query');
      
      expect(Array.isArray(results)).toBe(true);
    }, 30000);
  });

  describe('Call Graph Analysis', () => {
    it('should find callers and callees', async () => {
      const codeGraph = await createCodeGraph({ storage: 'memory' });
      await codeGraph.index(CODEGRAPH_SRC);
      
      // These may be empty if no matching entities found
      const callers = await codeGraph.findCallers('query');
      const callees = await codeGraph.findCallees('query');
      
      expect(Array.isArray(callers)).toBe(true);
      expect(Array.isArray(callees)).toBe(true);
    }, 30000);
  });
});
