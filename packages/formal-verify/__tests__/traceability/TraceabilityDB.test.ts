/**
 * TraceabilityDB Unit Tests
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { TraceabilityDB } from '../../src/traceability/TraceabilityDB';
import * as fs from 'fs';
import * as path from 'path';

describe('TraceabilityDB', () => {
  let db: TraceabilityDB;
  const testDbPath = path.join(__dirname, 'test-traceability.db');

  beforeEach(() => {
    // Ensure clean state
    if (fs.existsSync(testDbPath)) {
      fs.unlinkSync(testDbPath);
    }
    db = new TraceabilityDB(testDbPath);
  });

  afterEach(async () => {
    await db.close();
    if (fs.existsSync(testDbPath)) {
      fs.unlinkSync(testDbPath);
    }
  });

  describe('constructor', () => {
    it('should create database file', () => {
      expect(fs.existsSync(testDbPath)).toBe(true);
    });

    it('should create in-memory database when no path provided', () => {
      const memDb = new TraceabilityDB(':memory:');
      expect(memDb).toBeInstanceOf(TraceabilityDB);
      memDb.close();
    });
  });

  describe('addNode', () => {
    it('should add requirement node', async () => {
      const node = await db.addNode({
        id: 'REQ-001',
        type: 'requirement',
        title: 'User Authentication',
        description: 'THE system SHALL authenticate users',
        metadata: { priority: 'P0' },
      });

      expect(node.id).toBe('REQ-001');
      expect(node.type).toBe('requirement');
      expect(node.title).toBe('User Authentication');
    });

    it('should add design node', async () => {
      const node = await db.addNode({
        id: 'DES-001',
        type: 'design',
        title: 'Authentication Service',
        description: 'Service for handling authentication',
      });

      expect(node.type).toBe('design');
    });

    it('should add code node', async () => {
      const node = await db.addNode({
        id: 'CODE-001',
        type: 'code',
        title: 'AuthService.ts',
        description: 'Authentication service implementation',
        metadata: { file: 'src/auth/AuthService.ts', lines: '1-100' },
      });

      expect(node.type).toBe('code');
    });

    it('should add test node', async () => {
      const node = await db.addNode({
        id: 'TEST-001',
        type: 'test',
        title: 'AuthService.test.ts',
        description: 'Tests for AuthService',
      });

      expect(node.type).toBe('test');
    });

    it('should reject duplicate node ID', async () => {
      await db.addNode({ id: 'DUP-001', type: 'requirement', title: 'First' });
      
      await expect(
        db.addNode({ id: 'DUP-001', type: 'design', title: 'Second' })
      ).rejects.toThrow();
    });
  });

  describe('addLink', () => {
    beforeEach(async () => {
      await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'Requirement' });
      await db.addNode({ id: 'DES-001', type: 'design', title: 'Design' });
      await db.addNode({ id: 'CODE-001', type: 'code', title: 'Code' });
      await db.addNode({ id: 'TEST-001', type: 'test', title: 'Test' });
    });

    it('should create satisfies link', async () => {
      const link = await db.addLink({
        source: 'DES-001',
        target: 'REQ-001',
        type: 'satisfies',
      });

      expect(link.source).toBe('DES-001');
      expect(link.target).toBe('REQ-001');
      expect(link.type).toBe('satisfies');
    });

    it('should create implements link', async () => {
      const link = await db.addLink({
        source: 'CODE-001',
        target: 'DES-001',
        type: 'implements',
      });

      expect(link.type).toBe('implements');
    });

    it('should create verifies link', async () => {
      const link = await db.addLink({
        source: 'TEST-001',
        target: 'REQ-001',
        type: 'verifies',
      });

      expect(link.type).toBe('verifies');
    });

    it('should reject link with non-existent source', async () => {
      await expect(
        db.addLink({ source: 'NONEXIST', target: 'REQ-001', type: 'satisfies' })
      ).rejects.toThrow();
    });

    it('should reject link with non-existent target', async () => {
      await expect(
        db.addLink({ source: 'DES-001', target: 'NONEXIST', type: 'satisfies' })
      ).rejects.toThrow();
    });
  });

  describe('getNode', () => {
    it('should retrieve existing node', async () => {
      await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'Test' });
      
      const node = await db.getNode('REQ-001');
      
      expect(node).not.toBeNull();
      expect(node?.id).toBe('REQ-001');
    });

    it('should return null for non-existent node', async () => {
      const node = await db.getNode('NONEXIST');
      expect(node).toBeNull();
    });
  });

  describe('query', () => {
    beforeEach(async () => {
      await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'Auth Req' });
      await db.addNode({ id: 'REQ-002', type: 'requirement', title: 'Data Req' });
      await db.addNode({ id: 'DES-001', type: 'design', title: 'Auth Design' });
      await db.addNode({ id: 'DES-002', type: 'design', title: 'Data Design' });
      await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });
      await db.addLink({ source: 'DES-002', target: 'REQ-002', type: 'satisfies' });
    });

    it('should query linked nodes from source', async () => {
      const results = await db.query('REQ-001', { direction: 'both' });
      // Should find DES-001 linked via satisfies
      expect(results.relatedNodes.length).toBeGreaterThan(0);
      expect(results.source?.id).toBe('REQ-001');
    });

    it('should query forward links', async () => {
      const results = await db.query('DES-001', { direction: 'forward' });
      // DES-001 has satisfies -> REQ-001 (forward direction is target)
      expect(results).toBeDefined();
      expect(results.links.length).toBeGreaterThan(0);
    });

    it('should query backward links', async () => {
      const results = await db.query('REQ-001', { direction: 'backward' });
      // REQ-001 is target of DES-001's satisfies link
      expect(results).toBeDefined();
    });

    it('should handle non-existent source node', async () => {
      const results = await db.query('NONEXIST', { direction: 'both' });
      expect(results.source).toBeNull();
      expect(results.relatedNodes.length).toBe(0);
    });
  });

  describe('getStats', () => {
    it('should return correct statistics', async () => {
      await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'R1' });
      await db.addNode({ id: 'REQ-002', type: 'requirement', title: 'R2' });
      await db.addNode({ id: 'DES-001', type: 'design', title: 'D1' });
      await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });

      const stats = await db.getStats();

      expect(stats.nodeCount).toBe(3);
      expect(stats.linkCount).toBe(1);
      expect(stats.nodesByType['requirement']).toBe(2);
      expect(stats.nodesByType['design']).toBe(1);
      expect(stats.linksByType['satisfies']).toBe(1);
    });
  });

  describe('removeNode', () => {
    it('should remove node and associated links', async () => {
      await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'R1' });
      await db.addNode({ id: 'DES-001', type: 'design', title: 'D1' });
      await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });

      await db.removeNode('REQ-001');

      const node = await db.getNode('REQ-001');
      expect(node).toBeNull();

      const stats = await db.getStats();
      expect(stats.nodeCount).toBe(1);
      expect(stats.linkCount).toBe(0);
    });
  });

  describe('updateNode', () => {
    it('should update node properties', async () => {
      await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'Original' });

      await db.updateNode('REQ-001', { title: 'Updated', description: 'New desc' });

      const node = await db.getNode('REQ-001');
      expect(node?.title).toBe('Updated');
      expect(node?.description).toBe('New desc');
    });
  });
});
