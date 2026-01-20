/**
 * WorkflowIntegration Tests
 *
 * @see REQ-AA-INT-002
 * @see REQ-AA-INT-003
 */

import { describe, it, expect } from 'vitest';
import {
  createWorkflowIntegration,
  createAssistantAxisHook,
  shouldMonitorMessage,
} from '../../src/infrastructure/WorkflowIntegration.js';

describe('WorkflowIntegration', () => {
  describe('createWorkflowIntegration', () => {
    it('should create integration with default config', () => {
      const integration = createWorkflowIntegration();

      expect(integration.getCurrentPhase()).toBeUndefined();
    });

    it('should report monitoring enabled for requirements phase', () => {
      const integration = createWorkflowIntegration();

      expect(integration.isMonitoringEnabled('requirements')).toBe(true);
    });

    it('should report monitoring disabled for done phase', () => {
      const integration = createWorkflowIntegration();

      expect(integration.isMonitoringEnabled('done')).toBe(false);
    });
  });

  describe('getMonitoringFrequency', () => {
    it('should return 100% for requirements phase (HIGH)', () => {
      const integration = createWorkflowIntegration();

      expect(integration.getMonitoringFrequency('requirements')).toBe(1.0);
    });

    it('should return 100% for design phase (HIGH)', () => {
      const integration = createWorkflowIntegration();

      expect(integration.getMonitoringFrequency('design')).toBe(1.0);
    });

    it('should return 75% for tasks phase (MEDIUM)', () => {
      const integration = createWorkflowIntegration();

      expect(integration.getMonitoringFrequency('tasks')).toBe(0.75);
    });

    it('should return 50% for implementation phase (LOW)', () => {
      const integration = createWorkflowIntegration();

      // Implementation is LOW (50%) because coding is safe per research paper
      expect(integration.getMonitoringFrequency('implementation')).toBe(0.5);
    });

    it('should return 0% for done phase (OFF)', () => {
      const integration = createWorkflowIntegration();

      expect(integration.getMonitoringFrequency('done')).toBe(0);
    });

    it('should handle unknown phases with MEDIUM frequency', () => {
      const integration = createWorkflowIntegration();

      expect(integration.getMonitoringFrequency('unknown')).toBe(0.75);
    });
  });

  describe('shouldMonitorMessage', () => {
    it('should always monitor in HIGH frequency phases', () => {
      const integration = createWorkflowIntegration();

      // All messages should be monitored
      for (let i = 0; i < 10; i++) {
        expect(shouldMonitorMessage(integration, 'requirements', i)).toBe(true);
      }
    });

    it('should never monitor in OFF phases', () => {
      const integration = createWorkflowIntegration();

      // No messages should be monitored
      for (let i = 0; i < 10; i++) {
        expect(shouldMonitorMessage(integration, 'done', i)).toBe(false);
      }
    });

    it('should sample messages in LOW frequency phases', () => {
      const integration = createWorkflowIntegration();

      // 50% frequency means every other message
      const monitored = [];
      for (let i = 0; i < 10; i++) {
        monitored.push(shouldMonitorMessage(integration, 'implementation', i));
      }

      // Should have some true and some false
      const trueCount = monitored.filter(Boolean).length;
      expect(trueCount).toBeLessThan(10);
      expect(trueCount).toBeGreaterThan(0);
    });
  });

  describe('AssistantAxisHook', () => {
    it('should create hook with correct name', () => {
      const integration = createWorkflowIntegration();
      const hook = createAssistantAxisHook(integration);

      expect(hook.name).toBe('assistant-axis');
    });

    it('should call onPhaseChange callback', () => {
      const integration = createWorkflowIntegration();
      const phases: string[] = [];
      const hook = createAssistantAxisHook(integration, (phase) => {
        phases.push(phase);
      });

      hook.onPhaseChange('design', 'requirements');

      expect(phases).toContain('design');
    });

    it('should have workflow lifecycle methods', () => {
      const integration = createWorkflowIntegration();
      const hook = createAssistantAxisHook(integration);

      expect(typeof hook.onWorkflowStart).toBe('function');
      expect(typeof hook.onWorkflowEnd).toBe('function');
    });
  });
});
