/**
 * Wake-Sleep YATA Integrator Tests
 *
 * @see REQ-YATA-AUTO-004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  WakeSleepYataIntegrator,
  createWakeSleepYataIntegrator,
  type IYataBridge,
} from '../yata/yata-integrator.js';
import type { WakeTask } from '../types.js';

describe('WakeSleepYataIntegrator', () => {
  let integrator: WakeSleepYataIntegrator;

  beforeEach(() => {
    integrator = createWakeSleepYataIntegrator();
  });

  describe('connection', () => {
    it('should start disconnected', () => {
      expect(integrator.isConnected()).toBe(false);
    });

    it('should connect to YATA bridge', () => {
      const mockBridge: IYataBridge = {
        updateFromCode: async () => ({
          success: true,
          entitiesAdded: 0,
          relationshipsAdded: 0,
          errors: [],
        }),
        analyzeOnly: () => ({ entities: [], relationships: [] }),
      };

      integrator.connect(mockBridge);
      expect(integrator.isConnected()).toBe(true);
    });

    it('should disconnect from YATA bridge', () => {
      const mockBridge: IYataBridge = {
        updateFromCode: async () => ({
          success: true,
          entitiesAdded: 0,
          relationshipsAdded: 0,
          errors: [],
        }),
        analyzeOnly: () => ({ entities: [], relationships: [] }),
      };

      integrator.connect(mockBridge);
      integrator.disconnect();
      expect(integrator.isConnected()).toBe(false);
    });
  });

  describe('processWakeTask', () => {
    it('should extract entities from code task', () => {
      const task: WakeTask = {
        id: 'task-1',
        type: 'code',
        content: `
export class UserService {
  async getUser(id: string): Promise<User | null> {
    return null;
  }
}
`,
        context: {
          filePath: 'src/services/user.ts',
        },
      };

      const result = integrator.processWakeTask(task);

      expect(result.entities.length).toBeGreaterThan(0);
      expect(result.entities).toContainEqual(
        expect.objectContaining({
          type: 'class',
          name: 'UserService',
        })
      );
    });

    it('should skip non-code tasks', () => {
      const task: WakeTask = {
        id: 'task-1',
        type: 'requirements',
        content: 'WHEN user clicks login, THE system SHALL authenticate',
      };

      const result = integrator.processWakeTask(task);

      expect(result.entities).toHaveLength(0);
      expect(result.relationships).toHaveLength(0);
    });

    it('should queue entities for sleep phase', () => {
      const task: WakeTask = {
        id: 'task-1',
        type: 'code',
        content: 'export class Test {}',
        context: { filePath: 'test.ts' },
      };

      integrator.processWakeTask(task);
      const pending = integrator.getPendingCounts();

      expect(pending.entities).toBeGreaterThan(0);
    });

    it('should use YATA bridge when connected', () => {
      const mockAnalysis = {
        entities: [
          {
            type: 'class' as const,
            name: 'MockClass',
            namespace: 'mock',
            filePath: 'mock.ts',
          },
        ],
        relationships: [],
      };

      const mockBridge: IYataBridge = {
        updateFromCode: async () => ({
          success: true,
          entitiesAdded: 1,
          relationshipsAdded: 0,
          errors: [],
        }),
        analyzeOnly: () => mockAnalysis,
      };

      integrator.connect(mockBridge);

      const task: WakeTask = {
        id: 'task-1',
        type: 'code',
        content: 'export class MockClass {}',
        context: { filePath: 'mock.ts' },
      };

      const result = integrator.processWakeTask(task);

      expect(result.entities).toEqual(mockAnalysis.entities);
    });
  });

  describe('persistDuringSleep', () => {
    it('should return error when not connected', async () => {
      const result = await integrator.persistDuringSleep();

      expect(result.errors).toContain('YATA bridge not connected');
    });

    it('should clear pending after persist', async () => {
      const mockBridge: IYataBridge = {
        updateFromCode: async () => ({
          success: true,
          entitiesAdded: 1,
          relationshipsAdded: 0,
          errors: [],
        }),
        analyzeOnly: () => ({
          entities: [
            { type: 'class', name: 'Test', namespace: 'test', filePath: 'test.ts' },
          ],
          relationships: [],
        }),
      };

      integrator.connect(mockBridge);

      // Add some pending entities
      integrator.processWakeTask({
        id: 'task-1',
        type: 'code',
        content: 'export class Test {}',
        context: { filePath: 'test.ts' },
      });

      expect(integrator.getPendingCounts().entities).toBeGreaterThan(0);

      await integrator.persistDuringSleep();

      expect(integrator.getPendingCounts().entities).toBe(0);
    });
  });

  describe('clearPending', () => {
    it('should clear all pending entities and relationships', () => {
      const task: WakeTask = {
        id: 'task-1',
        type: 'code',
        content: 'export class Test {}',
        context: { filePath: 'test.ts' },
      };

      integrator.processWakeTask(task);
      expect(integrator.getPendingCounts().entities).toBeGreaterThan(0);

      integrator.clearPending();
      expect(integrator.getPendingCounts().entities).toBe(0);
      expect(integrator.getPendingCounts().relationships).toBe(0);
    });
  });

  describe('factory function', () => {
    it('should create integrator with default options', () => {
      const integrator = createWakeSleepYataIntegrator();
      expect(integrator).toBeInstanceOf(WakeSleepYataIntegrator);
    });

    it('should create integrator with custom options', () => {
      const integrator = createWakeSleepYataIntegrator({ autoSync: true });
      expect(integrator).toBeInstanceOf(WakeSleepYataIntegrator);
    });
  });
});
