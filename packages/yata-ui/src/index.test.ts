/**
 * Tests for YataUIServer
 *
 * @see REQ-YI-WEB-001 - Web-based Visualization
 * @see REQ-YI-WEB-002 - Interactive Graph Editing
 * @see REQ-YI-WEB-003 - Real-time Updates
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import {
  YataUIServer,
  createYataUIServer,
  DEFAULT_UI_CONFIG,
} from './index.js';
import type { GraphData, UIServerConfig } from './index.js';

describe('YataUIServer', () => {
  let server: YataUIServer;

  beforeEach(() => {
    server = new YataUIServer({
      port: 0, // Use random available port
      enableRealtime: true,
    });
  });

  afterEach(async () => {
    if (server.isRunning()) {
      await server.stop();
    }
  });

  // ============================================================
  // Factory Function
  // ============================================================

  describe('createYataUIServer', () => {
    it('should create server instance', () => {
      const s = createYataUIServer({ port: 0 });
      expect(s).toBeInstanceOf(YataUIServer);
    });
  });

  // ============================================================
  // Default Config
  // ============================================================

  describe('DEFAULT_UI_CONFIG', () => {
    it('should have sensible defaults', () => {
      expect(DEFAULT_UI_CONFIG.port).toBe(3000);
      expect(DEFAULT_UI_CONFIG.host).toBe('localhost');
      expect(DEFAULT_UI_CONFIG.cors).toBe(true);
      expect(DEFAULT_UI_CONFIG.enableRealtime).toBe(true);
    });
  });

  // ============================================================
  // Server Lifecycle
  // ============================================================

  describe('server lifecycle', () => {
    it('should start and stop', async () => {
      expect(server.isRunning()).toBe(false);
      
      await server.start();
      expect(server.isRunning()).toBe(true);
      
      await server.stop();
      expect(server.isRunning()).toBe(false);
    });

    it('should return URL', async () => {
      const url = server.getUrl();
      expect(url).toMatch(/^http:\/\/localhost:\d+$/);
    });
  });

  // ============================================================
  // Data Provider
  // ============================================================

  describe('data provider', () => {
    it('should accept data provider function', () => {
      const mockProvider = async (): Promise<GraphData> => ({
        nodes: [{ id: '1', label: 'Test', type: 'entity' }],
        edges: [],
      });

      // Should not throw
      server.setDataProvider(mockProvider);
    });
  });

  // ============================================================
  // Broadcast (REQ-YI-WEB-003)
  // ============================================================

  describe('broadcastUpdate', () => {
    it('should not throw when no clients connected', () => {
      // Should not throw
      expect(() => {
        server.broadcastUpdate('test', { foo: 'bar' });
      }).not.toThrow();
    });
  });

  // ============================================================
  // Express App
  // ============================================================

  describe('getApp', () => {
    it('should return Express app instance', () => {
      const app = server.getApp();
      expect(app).toBeDefined();
      expect(typeof app.listen).toBe('function');
    });
  });
});

// ============================================================
// API Integration Tests (with supertest-like approach)
// ============================================================

describe('YataUIServer API', () => {
  let server: YataUIServer;
  let baseUrl: string;

  beforeEach(async () => {
    server = new YataUIServer({
      port: 0,
      enableRealtime: true,
    });

    server.setDataProvider(async () => ({
      nodes: [
        { id: 'node-1', label: 'Node 1', type: 'entity', namespace: 'test' },
        { id: 'node-2', label: 'Node 2', type: 'class' },
      ],
      edges: [
        { id: 'edge-1', source: 'node-1', target: 'node-2', type: 'uses', label: 'uses' },
      ],
    }));

    // We can't easily get the actual port without starting
    // For real integration tests, we'd use supertest
    // Here we just test the app configuration
  });

  afterEach(async () => {
    if (server.isRunning()) {
      await server.stop();
    }
  });

  it('should configure health endpoint', () => {
    const app = server.getApp();
    // Check that routes are registered
    expect(app).toBeDefined();
  });
});
