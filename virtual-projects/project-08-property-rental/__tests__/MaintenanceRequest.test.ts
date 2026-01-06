/**
 * MaintenanceRequest Entity Tests
 * 
 * @requirement REQ-RENTAL-001-F040 (Maintenance Request Submission)
 * @requirement REQ-RENTAL-001-F041 (Maintenance Request Status Workflow)
 * @requirement REQ-RENTAL-001-F042 (Emergency Maintenance Escalation)
 * @design DES-RENTAL-001-C005
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  MaintenanceRequest,
  createMaintenanceRequest,
  CreateMaintenanceRequestInput,
  canTransitionMaintenanceStatus,
  transitionMaintenanceStatus,
  isEmergencyEscalationNeeded,
  EMERGENCY_ESCALATION_MINUTES,
} from '../src/entities/MaintenanceRequest.js';
import {
  resetMaintenanceCounter,
  MaintenanceStatus,
} from '../src/types/common.js';

describe('MaintenanceRequest Entity', () => {
  beforeEach(() => {
    resetMaintenanceCounter();
  });

  describe('createMaintenanceRequest', () => {
    it('should create a maintenance request with valid input', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '給湯器が故障しました。お湯が出ません。',
        priority: 'high',
        photos: ['photo1.jpg', 'photo2.jpg'],
      };

      const result = createMaintenanceRequest(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        const request = result.value;
        expect(request.id.value).toMatch(/^MAINT-\d{8}-001$/);
        expect(request.propertyId.value).toBe('PROP-20260106-001');
        expect(request.tenantId.value).toBe('TEN-20260106-001');
        expect(request.description).toBe('給湯器が故障しました。お湯が出ません。');
        expect(request.priority).toBe('high');
        expect(request.status).toBe('submitted');
        expect(request.photos).toEqual(['photo1.jpg', 'photo2.jpg']);
        expect(request.assignedTo).toBeUndefined();
      }
    });

    it('should create emergency priority request', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '水漏れが発生しています！緊急対応お願いします。',
        priority: 'emergency',
      };

      const result = createMaintenanceRequest(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.priority).toBe('emergency');
      }
    });

    it('should create medium priority request', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: 'インターホンの音が小さくなっています。',
        priority: 'medium',
      };

      const result = createMaintenanceRequest(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.priority).toBe('medium');
      }
    });

    it('should create low priority request', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '壁のクロスに小さな傷があります。',
        priority: 'low',
      };

      const result = createMaintenanceRequest(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.priority).toBe('low');
      }
    });

    it('should reject empty description', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '   ', // Empty after trim
        priority: 'medium',
      };

      const result = createMaintenanceRequest(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('description');
      }
    });
  });

  describe('Maintenance Status Transitions (REQ-RENTAL-001-F041)', () => {
    // Valid transitions
    it('should allow submitted → assigned transition', () => {
      expect(canTransitionMaintenanceStatus('submitted', 'assigned')).toBe(true);
    });

    it('should allow submitted → cancelled transition', () => {
      expect(canTransitionMaintenanceStatus('submitted', 'cancelled')).toBe(true);
    });

    it('should allow assigned → in-progress transition', () => {
      expect(canTransitionMaintenanceStatus('assigned', 'in-progress')).toBe(true);
    });

    it('should allow assigned → cancelled transition', () => {
      expect(canTransitionMaintenanceStatus('assigned', 'cancelled')).toBe(true);
    });

    it('should allow in-progress → completed transition', () => {
      expect(canTransitionMaintenanceStatus('in-progress', 'completed')).toBe(true);
    });

    it('should allow in-progress → cancelled transition', () => {
      expect(canTransitionMaintenanceStatus('in-progress', 'cancelled')).toBe(true);
    });

    // Invalid transitions
    it('should NOT allow submitted → in-progress transition', () => {
      expect(canTransitionMaintenanceStatus('submitted', 'in-progress')).toBe(false);
    });

    it('should NOT allow submitted → completed transition', () => {
      expect(canTransitionMaintenanceStatus('submitted', 'completed')).toBe(false);
    });

    it('should NOT allow completed → any transition', () => {
      const statuses: MaintenanceStatus[] = ['submitted', 'assigned', 'in-progress', 'cancelled'];
      statuses.forEach(status => {
        expect(canTransitionMaintenanceStatus('completed', status)).toBe(false);
      });
    });

    it('should NOT allow cancelled → any transition', () => {
      const statuses: MaintenanceStatus[] = ['submitted', 'assigned', 'in-progress', 'completed'];
      statuses.forEach(status => {
        expect(canTransitionMaintenanceStatus('cancelled', status)).toBe(false);
      });
    });
  });

  describe('transitionMaintenanceStatus', () => {
    it('should transition from submitted to assigned', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '給湯器が故障しました。',
        priority: 'high',
      };

      const createResult = createMaintenanceRequest(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const request = createResult.value;
      const transitionResult = transitionMaintenanceStatus(request, 'assigned', '田中');

      expect(transitionResult.isOk()).toBe(true);
      if (transitionResult.isOk()) {
        expect(transitionResult.value.status).toBe('assigned');
        expect(transitionResult.value.assignedTo).toBe('田中');
        expect(transitionResult.value.assignedAt).toBeInstanceOf(Date);
      }
    });

    it('should transition from in-progress to completed', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '給湯器が故障しました。',
        priority: 'high',
      };

      const createResult = createMaintenanceRequest(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      // Set to in-progress state
      const request: MaintenanceRequest = {
        ...createResult.value,
        status: 'in-progress',
        assignedTo: '田中',
        assignedAt: new Date(),
      };

      const transitionResult = transitionMaintenanceStatus(request, 'completed');

      expect(transitionResult.isOk()).toBe(true);
      if (transitionResult.isOk()) {
        expect(transitionResult.value.status).toBe('completed');
        expect(transitionResult.value.completedAt).toBeInstanceOf(Date);
      }
    });

    it('should reject invalid transition', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '給湯器が故障しました。',
        priority: 'high',
      };

      const createResult = createMaintenanceRequest(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const request = createResult.value;
      // submitted → completed is invalid
      const transitionResult = transitionMaintenanceStatus(request, 'completed');

      expect(transitionResult.isErr()).toBe(true);
      if (transitionResult.isErr()) {
        expect(transitionResult.error._tag).toBe('InvalidStatusTransitionError');
      }
    });
  });

  describe('Emergency Escalation (REQ-RENTAL-001-F042)', () => {
    it('should have escalation threshold of 60 minutes', () => {
      expect(EMERGENCY_ESCALATION_MINUTES).toBe(60);
    });

    it('should need escalation for unassigned emergency request after 1 hour', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '水漏れが発生！',
        priority: 'emergency',
      };

      const createResult = createMaintenanceRequest(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const request = createResult.value;
      
      // Simulate 61 minutes have passed
      const sixtyOneMinutesAgo = new Date(Date.now() - 61 * 60 * 1000);
      const requestWithOldTimestamp = {
        ...request,
        createdAt: sixtyOneMinutesAgo,
      };

      expect(isEmergencyEscalationNeeded(requestWithOldTimestamp)).toBe(true);
    });

    it('should not need escalation for emergency request within 1 hour', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '水漏れが発生！',
        priority: 'emergency',
      };

      const createResult = createMaintenanceRequest(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const request = createResult.value;
      
      // Request just created (within 1 hour)
      expect(isEmergencyEscalationNeeded(request)).toBe(false);
    });

    it('should not need escalation for assigned emergency request', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: '水漏れが発生！',
        priority: 'emergency',
      };

      const createResult = createMaintenanceRequest(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const request = createResult.value;
      
      // Simulate old timestamp but already assigned
      const sixtyOneMinutesAgo = new Date(Date.now() - 61 * 60 * 1000);
      const assignedRequest: MaintenanceRequest = {
        ...request,
        createdAt: sixtyOneMinutesAgo,
        status: 'assigned',
        assignedTo: '田中',
        assignedAt: new Date(),
      };

      expect(isEmergencyEscalationNeeded(assignedRequest)).toBe(false);
    });

    it('should not need escalation for non-emergency requests', () => {
      const input: CreateMaintenanceRequestInput = {
        propertyId: { value: 'PROP-20260106-001' },
        tenantId: { value: 'TEN-20260106-001' },
        description: 'インターホンの音が小さい。',
        priority: 'medium', // Not emergency
      };

      const createResult = createMaintenanceRequest(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const request = createResult.value;
      
      // Simulate old timestamp
      const sixtyOneMinutesAgo = new Date(Date.now() - 61 * 60 * 1000);
      const oldRequest = {
        ...request,
        createdAt: sixtyOneMinutesAgo,
      };

      expect(isEmergencyEscalationNeeded(oldRequest)).toBe(false);
    });
  });
});
