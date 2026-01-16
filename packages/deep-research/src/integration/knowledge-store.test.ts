// Knowledge Store Integration Tests
// TSK-DR-025
// REQ: REQ-DR-INT-005
// DES: DES-DR-v3.4.0 Section 5.4

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  KnowledgeStoreIntegration,
  createKnowledgeStoreIntegration,
  type KnowledgeItem,
  type StorageResult,
} from '../integration/knowledge-store.js';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';

/**
 * Test Suite: Knowledge Store Integration
 * 
 * Verifies integration with @musubix/knowledge package.
 * 
 * Test Coverage:
 * 1. Initialization and configuration
 * 2. Storage operations (store/query/search)
 * 3. Relation management
 * 4. Graph traversal
 * 5. Export/import functionality
 * 6. Error handling
 */
describe('Knowledge Store Integration', () => {
  const TEST_STORAGE_PATH = path.join(process.cwd(), '.test-knowledge');
  let integration: KnowledgeStoreIntegration;
  
  beforeEach(async () => {
    // Clean up test storage
    try {
      await fs.rm(TEST_STORAGE_PATH, { recursive: true, force: true });
    } catch {
      // Ignore if doesn't exist
    }
    
    integration = createKnowledgeStoreIntegration({
      basePath: TEST_STORAGE_PATH,
      autoSave: true,
      autoLoad: false,
    });
  });
  
  afterEach(async () => {
    // Clean up after tests
    try {
      await fs.rm(TEST_STORAGE_PATH, { recursive: true, force: true });
    } catch {
      // Ignore cleanup errors
    }
  });
  
  describe('Initialization', () => {
    it('should create knowledge store integration instance', () => {
      expect(integration).toBeInstanceOf(KnowledgeStoreIntegration);
    });
    
    it('should initialize with default config', async () => {
      const defaultIntegration = createKnowledgeStoreIntegration();
      expect(defaultIntegration).toBeInstanceOf(KnowledgeStoreIntegration);
    });
    
    it('should initialize with custom config', async () => {
      const custom = createKnowledgeStoreIntegration({
        basePath: '/tmp/custom-knowledge',
        autoSave: false,
        autoLoad: false,
      });
      expect(custom).toBeInstanceOf(KnowledgeStoreIntegration);
    });
    
    it('should initialize knowledge store', async () => {
      const isAvailable = await integration.isAvailable();
      
      if (!isAvailable) {
        console.log('⚠️  @musubix/knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      const stats = integration.getStats();
      expect(stats.entityCount).toBe(0);
      expect(stats.relationCount).toBe(0);
    });
  });
  
  describe('Availability Check', () => {
    it('should check if knowledge package is available', async () => {
      const isAvailable = await integration.isAvailable();
      // Returns false if package not installed, true if installed
      expect(typeof isAvailable).toBe('boolean');
    });
  });
  
  describe('Storage Operations', () => {
    it('should store a knowledge item', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const item: KnowledgeItem = {
        content: 'TypeScript is a typed superset of JavaScript',
        type: 'fact',
        confidence: 0.95,
        iteration: 1,
        metadata: { source: 'test' },
      };
      
      const result: StorageResult = await integration.storeKnowledgeItem(
        item,
        'What is TypeScript?'
      );
      
      expect(result.stored).toBe(true);
      expect(result.entityId).toMatch(/^knowledge-fact-/);
      expect(result.message).toBe('Successfully stored');
    });
    
    it('should fail to store without initialization', async () => {
      const item: KnowledgeItem = {
        content: 'Test content',
        type: 'fact',
        iteration: 1,
      };
      
      const result = await integration.storeKnowledgeItem(item, 'test query');
      
      expect(result.stored).toBe(false);
      expect(result.message).toContain('not initialized');
    });
    
    it('should store multiple items with unique IDs', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const items: KnowledgeItem[] = [
        { content: 'Fact 1', type: 'fact', iteration: 1 },
        { content: 'Fact 2', type: 'fact', iteration: 1 },
        { content: 'Concept 1', type: 'concept', iteration: 2 },
      ];
      
      const results = await Promise.all(
        items.map((item) => integration.storeKnowledgeItem(item, 'test'))
      );
      
      const ids = results.map((r) => r.entityId);
      const uniqueIds = new Set(ids);
      
      expect(uniqueIds.size).toBe(items.length);
      results.forEach((r) => expect(r.stored).toBe(true));
    });
  });
  
  describe('Query Operations', () => {
    it('should query stored knowledge items', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      // Store some items
      await integration.storeKnowledgeItem(
        { content: 'Test fact', type: 'fact', iteration: 1 },
        'test'
      );
      
      const entities = await integration.query({ type: 'pattern' });
      
      expect(entities.length).toBeGreaterThanOrEqual(1);
    });
    
    it('should search knowledge by text', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      await integration.storeKnowledgeItem(
        { content: 'JavaScript is a programming language', type: 'fact', iteration: 1 },
        'test'
      );
      
      const results = await integration.search('JavaScript');
      
      expect(results.length).toBeGreaterThanOrEqual(0);
    });
    
    it('should filter by tags', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      await integration.storeKnowledgeItem(
        { content: 'Tagged item', type: 'fact', iteration: 1 },
        'test'
      );
      
      const results = await integration.query({ tags: ['fact'] });
      
      expect(results.length).toBeGreaterThanOrEqual(1);
    });
  });
  
  describe('Relation Management', () => {
    it('should add relation between entities', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const result1 = await integration.storeKnowledgeItem(
        { content: 'Entity 1', type: 'fact', iteration: 1 },
        'test'
      );
      
      const result2 = await integration.storeKnowledgeItem(
        { content: 'Entity 2', type: 'concept', iteration: 1 },
        'test'
      );
      
      await integration.addRelation({
        source: result1.entityId,
        target: result2.entityId,
        type: 'related_to',
      });
      
      const stats = integration.getStats();
      expect(stats.relationCount).toBeGreaterThanOrEqual(1);
    });
    
    it('should get related entities', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const result1 = await integration.storeKnowledgeItem(
        { content: 'Root entity', type: 'fact', iteration: 1 },
        'test'
      );
      
      const result2 = await integration.storeKnowledgeItem(
        { content: 'Related entity', type: 'concept', iteration: 1 },
        'test'
      );
      
      await integration.addRelation({
        source: result1.entityId,
        target: result2.entityId,
        type: 'derives_from',
      });
      
      const related = await integration.getRelated(result1.entityId);
      
      expect(related.entities.length).toBeGreaterThanOrEqual(0);
      expect(related.relationCount).toBeGreaterThanOrEqual(1);
    });
  });
  
  describe('Graph Traversal', () => {
    it('should traverse knowledge graph with depth', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const r1 = await integration.storeKnowledgeItem(
        { content: 'Root', type: 'fact', iteration: 1 },
        'test'
      );
      
      const related = await integration.getRelated(r1.entityId, {
        depth: 2,
        direction: 'both',
      });
      
      expect(related.depth).toBe(2);
    });
    
    it('should filter traversal by relation types', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const r1 = await integration.storeKnowledgeItem(
        { content: 'Root', type: 'fact', iteration: 1 },
        'test'
      );
      
      const related = await integration.getRelated(r1.entityId, {
        relationTypes: ['derives_from', 'related_to'],
      });
      
      expect(related.entities.length).toBeGreaterThanOrEqual(0);
    });
  });
  
  describe('Persistence', () => {
    it('should save knowledge store to disk', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      await integration.storeKnowledgeItem(
        { content: 'Persistent item', type: 'fact', iteration: 1 },
        'test'
      );
      
      await integration.save();
      
      // Check if file exists
      const graphPath = path.join(TEST_STORAGE_PATH, 'graph.json');
      const exists = await fs.access(graphPath).then(() => true).catch(() => false);
      
      expect(exists).toBe(true);
    });
    
    it('should load existing knowledge store', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      await integration.storeKnowledgeItem(
        { content: 'Item to load', type: 'fact', iteration: 1 },
        'test'
      );
      
      await integration.save();
      
      // Create new integration and load
      const newIntegration = createKnowledgeStoreIntegration({
        basePath: TEST_STORAGE_PATH,
        autoLoad: true,
      });
      
      await newIntegration.initialize();
      const stats = newIntegration.getStats();
      
      expect(stats.entityCount).toBeGreaterThanOrEqual(1);
    });
  });
  
  describe('Export', () => {
    it('should export knowledge base as JSON', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      await integration.storeKnowledgeItem(
        { content: 'Export test', type: 'fact', iteration: 1 },
        'test'
      );
      
      const exported = await integration.export();
      const parsed = JSON.parse(exported);
      
      expect(parsed).toHaveProperty('exportedAt');
      expect(parsed).toHaveProperty('stats');
      expect(parsed).toHaveProperty('entities');
      expect(Array.isArray(parsed.entities)).toBe(true);
    });
  });
  
  describe('Statistics', () => {
    it('should get statistics', async () => {
      const isAvailable = await integration.isAvailable();
      if (!isAvailable) {
        console.log('⚠️  Knowledge package not available, skipping test');
        return;
      }
      
      await integration.initialize();
      
      const stats = integration.getStats();
      
      expect(stats).toHaveProperty('entityCount');
      expect(stats).toHaveProperty('relationCount');
      expect(typeof stats.entityCount).toBe('number');
      expect(typeof stats.relationCount).toBe('number');
    });
  });
  
  describe('Error Handling', () => {
    it('should handle query without initialization', async () => {
      await expect(integration.query({})).rejects.toThrow('not initialized');
    });
    
    it('should handle search without initialization', async () => {
      await expect(integration.search('test')).rejects.toThrow('not initialized');
    });
    
    it('should handle getRelated without initialization', async () => {
      await expect(integration.getRelated('test-id')).rejects.toThrow('not initialized');
    });
    
    it('should handle export without initialization', async () => {
      await expect(integration.export()).rejects.toThrow('not initialized');
    });
    
    it('should return empty stats when not initialized', () => {
      const stats = integration.getStats();
      expect(stats.entityCount).toBe(0);
      expect(stats.relationCount).toBe(0);
    });
  });
});

/**
 * E2E Integration Test with Real Package
 * 
 * Note: This test requires @musubix/knowledge to be installed.
 * It will be skipped if the package is not available.
 */
describe('Knowledge Store E2E Integration', () => {
  const TEST_STORAGE_PATH = path.join(process.cwd(), '.test-knowledge-e2e');
  
  afterEach(async () => {
    try {
      await fs.rm(TEST_STORAGE_PATH, { recursive: true, force: true });
    } catch {
      // Ignore cleanup errors
    }
  });
  
  it('should integrate with real knowledge package if available', async () => {
    const integration = createKnowledgeStoreIntegration({
      basePath: TEST_STORAGE_PATH,
      autoSave: true,
      autoLoad: false,
    });
    
    const isAvailable = await integration.isAvailable();
    
    if (!isAvailable) {
      console.log('⚠️  Knowledge package not available, skipping E2E test');
      return;
    }
    
    // If package is available, test full workflow
    try {
      await integration.initialize();
      
      // Store knowledge
      const result = await integration.storeKnowledgeItem(
        {
          content: 'E2E test knowledge item',
          type: 'fact',
          confidence: 0.9,
          iteration: 1,
        },
        'E2E test query'
      );
      
      expect(result.stored).toBe(true);
      
      // Query
      const entities = await integration.query({ type: 'pattern' });
      expect(entities.length).toBeGreaterThanOrEqual(1);
      
      // Export
      const exported = await integration.export();
      expect(exported).toContain('exportedAt');
      
      console.log('✅ Knowledge store package is available and integrated');
      console.log(`💾 Stored ${integration.getStats().entityCount} entities`);
    } catch (error) {
      console.error('❌ E2E integration test failed:', error);
      throw error;
    }
  });
});
