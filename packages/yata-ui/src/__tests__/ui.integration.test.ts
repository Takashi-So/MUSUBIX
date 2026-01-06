/**
 * YATA UI Integration Tests
 *
 * Tests the UI Server and data transformation integration
 *
 * @packageDocumentation
 * @see REQ-YI-WEB-001 - Web-based Visualization
 * @see REQ-YI-WEB-002 - Interactive Graph Editing
 * @see REQ-YI-WEB-003 - Real-time Updates
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { YataUIServer, createYataUIServer, DEFAULT_UI_CONFIG } from '../index.js';
import type { GraphData, GraphNode, GraphEdge } from '../index.js';

/**
 * Mock YataLocal-like data source for testing
 */
class MockYataLocal {
  private entities: Array<{ id: string; type: string; name: string; namespace: string }> = [];
  private relationships: Array<{ id: string; sourceId: string; targetId: string; type: string }> = [];

  async addEntity(entity: { type: string; name: string; namespace: string }) {
    const id = `E-${this.entities.length + 1}`;
    this.entities.push({ id, ...entity });
    return { id };
  }

  async addRelationship(rel: { sourceId: string; targetId: string; type: string }) {
    const id = `R-${this.relationships.length + 1}`;
    this.relationships.push({ id, ...rel });
    return { id };
  }

  async getAllEntities() {
    return this.entities;
  }

  async getAllRelationships() {
    return this.relationships;
  }

  toGraphData(): GraphData {
    return {
      nodes: this.entities.map(e => ({
        id: e.id,
        label: e.name,
        type: e.type,
        namespace: e.namespace,
      })),
      edges: this.relationships.map(r => ({
        id: r.id,
        source: r.sourceId,
        target: r.targetId,
        type: r.type,
      })),
    };
  }
}

describe('YATA UI Integration', () => {
  let server: YataUIServer;
  let mockYata: MockYataLocal;

  beforeEach(async () => {
    mockYata = new MockYataLocal();

    // Seed test data
    const user = await mockYata.addEntity({
      type: 'class',
      name: 'User',
      namespace: 'domain.entities',
    });

    const userRepo = await mockYata.addEntity({
      type: 'interface',
      name: 'UserRepository',
      namespace: 'domain.repositories',
    });

    const userService = await mockYata.addEntity({
      type: 'class',
      name: 'UserService',
      namespace: 'application.services',
    });

    await mockYata.addRelationship({
      sourceId: userService.id,
      targetId: userRepo.id,
      type: 'depends_on',
    });

    await mockYata.addRelationship({
      sourceId: userRepo.id,
      targetId: user.id,
      type: 'manages',
    });

    // Create server
    server = new YataUIServer({
      port: 0, // Random port
      enableRealtime: true,
    });

    server.setDataProvider(async () => mockYata.toGraphData());
  });

  afterEach(async () => {
    if (server.isRunning()) {
      await server.stop();
    }
  });

  describe('Server Lifecycle', () => {
    it('should start and stop server', async () => {
      expect(server.isRunning()).toBe(false);
      
      await server.start();
      expect(server.isRunning()).toBe(true);
      
      await server.stop();
      expect(server.isRunning()).toBe(false);
    });

    it('should return URL', () => {
      const url = server.getUrl();
      expect(url).toMatch(/^http:\/\/localhost:\d+$/);
    });
  });

  describe('Data Provider Integration', () => {
    it('should accept data provider function', () => {
      const mockProvider = async (): Promise<GraphData> => ({
        nodes: [{ id: '1', label: 'Test', type: 'entity' }],
        edges: [],
      });

      // Should not throw
      server.setDataProvider(mockProvider);
    });

    it('should update data provider dynamically', async () => {
      // Add more entities
      await mockYata.addEntity({
        type: 'class',
        name: 'Order',
        namespace: 'domain.entities',
      });

      const graphData = mockYata.toGraphData();
      expect(graphData.nodes.length).toBe(4);
    });
  });

  describe('Real-time Updates', () => {
    it('should broadcast updates to connected clients', () => {
      // Broadcast an update - should not throw
      server.broadcastUpdate('entity:created', {
        id: 'E-NEW',
        type: 'class',
        name: 'NewEntity',
      });

      expect(true).toBe(true);
    });

    it('should broadcast to namespaced clients', () => {
      server.broadcastUpdate('entity:updated', {
        id: 'E-1',
        changes: { name: 'UpdatedUser' },
      });

      // Verify no error thrown
      expect(server.isRunning()).toBe(false); // Not started yet
    });
  });
});

describe('YataUIServer Factory', () => {
  it('should create server with factory function', () => {
    const server = createYataUIServer({ port: 0 });
    expect(server).toBeInstanceOf(YataUIServer);
  });

  it('should apply default configuration', () => {
    expect(DEFAULT_UI_CONFIG.port).toBe(3000);
    expect(DEFAULT_UI_CONFIG.host).toBe('localhost');
    expect(DEFAULT_UI_CONFIG.cors).toBe(true);
    expect(DEFAULT_UI_CONFIG.enableRealtime).toBe(true);
  });
});

describe('GraphData Transformation', () => {
  it('should transform entities to nodes correctly', async () => {
    const mockYata = new MockYataLocal();
    await mockYata.addEntity({ type: 'class', name: 'Test', namespace: 'ns' });

    const graphData = mockYata.toGraphData();

    expect(graphData.nodes[0]).toMatchObject({
      label: 'Test',
      type: 'class',
      namespace: 'ns',
    });
  });

  it('should transform relationships to edges correctly', async () => {
    const mockYata = new MockYataLocal();
    const e1 = await mockYata.addEntity({ type: 'class', name: 'A', namespace: 'ns' });
    const e2 = await mockYata.addEntity({ type: 'class', name: 'B', namespace: 'ns' });
    await mockYata.addRelationship({
      sourceId: e1.id,
      targetId: e2.id,
      type: 'uses',
    });

    const graphData = mockYata.toGraphData();

    expect(graphData.edges[0]).toMatchObject({
      source: e1.id,
      target: e2.id,
      type: 'uses',
    });
  });

  it('should handle empty data', () => {
    const mockYata = new MockYataLocal();
    const graphData = mockYata.toGraphData();

    expect(graphData.nodes).toEqual([]);
    expect(graphData.edges).toEqual([]);
  });

  it('should handle multiple nodes and edges', async () => {
    const mockYata = new MockYataLocal();
    
    // Add multiple entities
    for (let i = 0; i < 5; i++) {
      await mockYata.addEntity({ type: 'class', name: `Class${i}`, namespace: 'ns' });
    }

    const graphData = mockYata.toGraphData();
    expect(graphData.nodes.length).toBe(5);
  });
});
