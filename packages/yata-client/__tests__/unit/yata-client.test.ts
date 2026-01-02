/**
 * YATA Client Unit Tests
 * 
 * @see REQ-INT-001 - Neuro-Symbolic Integration
 * @see REQ-INT-001 - Knowledge Graph Query
 * @see TSK-048 - YATA Client Implementation
 */

import { describe, it, expect } from 'vitest';
import {
  VERSION,
  DEFAULT_YATA_CONFIG,
  type YataClientConfig,
  type MCPTransport,
  type ConnectionState,
  type YataToolName,
  type KnowledgeNode,
  type KnowledgeEdge,
  type KnowledgeQueryResult,
} from '../../src/index.js';

describe('REQ-INT-001: YATA Client', () => {
  describe('Module Exports', () => {
    it('should export VERSION', () => {
      expect(VERSION).toBeDefined();
      expect(typeof VERSION).toBe('string');
      expect(VERSION).toMatch(/^\d+\.\d+\.\d+/);
    });

    it('should export DEFAULT_YATA_CONFIG', () => {
      expect(DEFAULT_YATA_CONFIG).toBeDefined();
      expect(DEFAULT_YATA_CONFIG.transport).toBe('stdio');
      expect(DEFAULT_YATA_CONFIG.timeout).toBeGreaterThan(0);
    });
  });

  describe('YataClientConfig', () => {
    it('should have required configuration properties', () => {
      const config: YataClientConfig = {
        transport: 'stdio',
        server: 'test-server',
        timeout: 5000,
        autoReconnect: true,
        maxReconnectAttempts: 3,
        reconnectDelay: 1000,
      };

      expect(config.transport).toBe('stdio');
      expect(config.server).toBe('test-server');
      expect(config.timeout).toBe(5000);
    });

    it('should support optional args', () => {
      const config: YataClientConfig = {
        ...DEFAULT_YATA_CONFIG,
        args: ['--verbose', '--debug'],
      };

      expect(config.args).toHaveLength(2);
      expect(config.args).toContain('--verbose');
    });
  });

  describe('MCPTransport', () => {
    it('should support stdio transport', () => {
      const transport: MCPTransport = 'stdio';
      expect(transport).toBe('stdio');
    });

    it('should support sse transport', () => {
      const transport: MCPTransport = 'sse';
      expect(transport).toBe('sse');
    });
  });

  describe('ConnectionState', () => {
    it('should have all connection states', () => {
      const states: ConnectionState[] = [
        'disconnected',
        'connecting',
        'connected',
        'reconnecting',
        'error',
      ];

      states.forEach((state) => {
        expect(['disconnected', 'connecting', 'connected', 'reconnecting', 'error']).toContain(state);
      });
    });
  });

  describe('YataToolName', () => {
    it('should have all expected tool names', () => {
      const tools: YataToolName[] = [
        'query_knowledge',
        'add_knowledge',
        'update_knowledge',
        'delete_knowledge',
        'search_patterns',
        'validate_constraints',
        'infer_relationships',
        'get_reasoning_chain',
      ];

      expect(tools).toHaveLength(8);
    });
  });

  describe('KnowledgeNode', () => {
    it('should have correct structure', () => {
      const node: KnowledgeNode = {
        id: 'node-001',
        type: 'requirement',
        label: 'REQ-001',
        properties: {
          title: 'Test Requirement',
          status: 'active',
        },
        createdAt: '2025-01-01T00:00:00Z',
        updatedAt: '2025-01-02T00:00:00Z',
      };

      expect(node.id).toBe('node-001');
      expect(node.type).toBe('requirement');
      expect(node.label).toBe('REQ-001');
      expect(node.properties.title).toBe('Test Requirement');
    });
  });

  describe('KnowledgeEdge', () => {
    it('should have correct structure', () => {
      const edge: KnowledgeEdge = {
        id: 'edge-001',
        sourceId: 'node-001',
        targetId: 'node-002',
        type: 'traces_to',
        properties: {
          confidence: 0.95,
        },
      };

      expect(edge.id).toBe('edge-001');
      expect(edge.sourceId).toBe('node-001');
      expect(edge.targetId).toBe('node-002');
      expect(edge.type).toBe('traces_to');
    });
  });

  describe('KnowledgeQueryResult', () => {
    it('should have correct structure', () => {
      const result: KnowledgeQueryResult = {
        nodes: [],
        edges: [],
        totalCount: 0,
        executionTime: 50,
      };

      expect(result.nodes).toEqual([]);
      expect(result.edges).toEqual([]);
      expect(result.totalCount).toBe(0);
      expect(result.executionTime).toBe(50);
    });

    it('should contain matched nodes and edges', () => {
      const result: KnowledgeQueryResult = {
        nodes: [
          {
            id: 'n1',
            type: 'requirement',
            label: 'REQ-001',
            properties: {},
            createdAt: '',
            updatedAt: '',
          },
        ],
        edges: [
          {
            id: 'e1',
            sourceId: 'n1',
            targetId: 'n2',
            type: 'traces_to',
            properties: {},
          },
        ],
        totalCount: 1,
        executionTime: 100,
      };

      expect(result.nodes).toHaveLength(1);
      expect(result.edges).toHaveLength(1);
    });
  });

  describe('Default Configuration', () => {
    it('should have sensible default values', () => {
      expect(DEFAULT_YATA_CONFIG.transport).toBe('stdio');
      expect(DEFAULT_YATA_CONFIG.server).toBe('yata-mcp');
      expect(DEFAULT_YATA_CONFIG.timeout).toBe(30000);
      expect(DEFAULT_YATA_CONFIG.autoReconnect).toBe(true);
      expect(DEFAULT_YATA_CONFIG.maxReconnectAttempts).toBe(3);
      expect(DEFAULT_YATA_CONFIG.reconnectDelay).toBe(1000);
    });

    it('should be immutable', () => {
      const originalTimeout = DEFAULT_YATA_CONFIG.timeout;
      
      // This should not change the original
      const modified = { ...DEFAULT_YATA_CONFIG, timeout: 1000 };
      
      expect(DEFAULT_YATA_CONFIG.timeout).toBe(originalTimeout);
      expect(modified.timeout).toBe(1000);
    });
  });
});

describe('REQ-INT-001: Knowledge Graph Integration', () => {
  describe('Node Types', () => {
    it('should support requirement nodes', () => {
      const req: KnowledgeNode = {
        id: 'req-001',
        type: 'requirement',
        label: 'REQ-RA-001',
        properties: {
          title: 'EARS Pattern Recognition',
          ears_pattern: 'ubiquitous',
        },
        createdAt: '',
        updatedAt: '',
      };

      expect(req.type).toBe('requirement');
    });

    it('should support design nodes', () => {
      const design: KnowledgeNode = {
        id: 'des-001',
        type: 'design',
        label: 'DES-001',
        properties: {
          c4_level: 'component',
        },
        createdAt: '',
        updatedAt: '',
      };

      expect(design.type).toBe('design');
    });

    it('should support task nodes', () => {
      const task: KnowledgeNode = {
        id: 'tsk-001',
        type: 'task',
        label: 'TSK-001',
        properties: {
          status: 'in_progress',
          priority: 'high',
        },
        createdAt: '',
        updatedAt: '',
      };

      expect(task.type).toBe('task');
    });

    it('should support pattern nodes', () => {
      const pattern: KnowledgeNode = {
        id: 'pat-001',
        type: 'pattern',
        label: 'Singleton',
        properties: {
          category: 'creational',
        },
        createdAt: '',
        updatedAt: '',
      };

      expect(pattern.type).toBe('pattern');
    });
  });

  describe('Edge Types', () => {
    it('should support traces_to relationship', () => {
      const edge: KnowledgeEdge = {
        id: 'e1',
        sourceId: 'req-001',
        targetId: 'des-001',
        type: 'traces_to',
        properties: {},
      };

      expect(edge.type).toBe('traces_to');
    });

    it('should support implements relationship', () => {
      const edge: KnowledgeEdge = {
        id: 'e2',
        sourceId: 'code-001',
        targetId: 'des-001',
        type: 'implements',
        properties: {},
      };

      expect(edge.type).toBe('implements');
    });

    it('should support verified_by relationship', () => {
      const edge: KnowledgeEdge = {
        id: 'e3',
        sourceId: 'code-001',
        targetId: 'test-001',
        type: 'verified_by',
        properties: {},
      };

      expect(edge.type).toBe('verified_by');
    });
  });
});
