/**
 * MaintenanceRequest Entity Tests
 * TSK-030: MaintenanceRequest Entity Unit Tests
 * 
 * @see REQ-RENTAL-001 F060-F062
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createMaintenanceRequest,
  assignStaff,
  startWork,
  completeMaintenanceRequest,
  escalateUrgency,
  resetMaintenanceCounter,
} from '../src/entities/MaintenanceRequest.js';
import type { SubmitMaintenanceInput } from '../src/types/index.js';

describe('MaintenanceRequest Entity', () => {
  let validInput: SubmitMaintenanceInput;

  beforeEach(() => {
    resetMaintenanceCounter();
    validInput = {
      propertyId: 'PROP-20250101-001',
      tenantId: 'TEN-20250101-001',
      title: '水漏れ修理',
      description: 'キッチンの蛇口から水漏れがあります',
      urgency: 'medium',
      photos: [],
    };
  });

  describe('createMaintenanceRequest', () => {
    it('should create a maintenance request with valid inputs', () => {
      const request = createMaintenanceRequest(validInput);

      expect(request.id).toMatch(/^MNT-\d{8}-\d{3}$/);
      expect(request.title).toBe('水漏れ修理');
      expect(request.status).toBe('submitted');
      expect(request.urgency).toBe('medium');
    });

    it('should throw error for empty title', () => {
      const invalidInput = { ...validInput, title: '' };
      expect(() => createMaintenanceRequest(invalidInput)).toThrow('Title is required');
    });

    it('should throw error for empty description', () => {
      const invalidInput = { ...validInput, description: '' };
      expect(() => createMaintenanceRequest(invalidInput)).toThrow('Description is required');
    });

    it('should handle different urgency levels', () => {
      const lowRequest = createMaintenanceRequest({ ...validInput, urgency: 'low' });
      expect(lowRequest.urgency).toBe('low');

      const highRequest = createMaintenanceRequest({ ...validInput, urgency: 'high' });
      expect(highRequest.urgency).toBe('high');
    });

    it('should store photos when provided', () => {
      const inputWithPhotos = { ...validInput, photos: ['photo1.jpg', 'photo2.jpg'] };
      const request = createMaintenanceRequest(inputWithPhotos);
      expect(request.photos).toHaveLength(2);
    });
  });

  describe('assignStaff', () => {
    it('should assign staff to maintenance request', () => {
      const request = createMaintenanceRequest(validInput);
      const assigned = assignStaff(request, 'STAFF-001');

      expect(assigned.assignedTo).toBe('STAFF-001');
      expect(assigned.status).toBe('assigned');
    });
  });

  describe('startWork', () => {
    it('should start work on assigned request', () => {
      const request = createMaintenanceRequest(validInput);
      const assigned = assignStaff(request, 'STAFF-001');
      const inProgress = startWork(assigned);
      expect(inProgress.status).toBe('in_progress');
    });
  });

  describe('completeMaintenanceRequest', () => {
    it('should complete maintenance with cost', () => {
      const request = createMaintenanceRequest(validInput);
      const assigned = assignStaff(request, 'STAFF-001');
      const inProgress = startWork(assigned);
      const completed = completeMaintenanceRequest(inProgress, 15000);

      expect(completed.status).toBe('completed');
      expect(completed.cost?.amount).toBe(15000);
      expect(completed.completedDate).toBeDefined();
    });
  });

  describe('escalateUrgency', () => {
    it('should escalate urgency from low to high', () => {
      const lowRequest = createMaintenanceRequest({ ...validInput, urgency: 'low' });
      const escalated = escalateUrgency(lowRequest, 'high');
      expect(escalated.urgency).toBe('high');
    });

    it('should escalate urgency from medium to emergency', () => {
      const request = createMaintenanceRequest(validInput);
      const escalated = escalateUrgency(request, 'emergency');
      expect(escalated.urgency).toBe('emergency');
    });
  });
});
