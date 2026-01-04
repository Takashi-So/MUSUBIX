/**
 * Unit tests for Appointment entity
 * @task TSK-CLINIC-001-005
 */

import { describe, it, expect } from 'vitest';
import type {
  Appointment,
  AppointmentStatus,
  AppointmentType,
  TimeSlot,
  CreateAppointmentDTO,
  UpdateAppointmentDTO,
} from '../../../src/domain/entities/appointment.js';

describe('Appointment Entity', () => {
  describe('Appointment type structure', () => {
    it('should have required fields', () => {
      const appointment: Appointment = {
        id: 'APT-001',
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        duration: 30,
        status: 'scheduled',
        type: 'initial',
        createdAt: new Date(),
        updatedAt: new Date(),
      };

      expect(appointment.id).toBe('APT-001');
      expect(appointment.patientId).toBe('PAT-001');
      expect(appointment.doctorId).toBe('DOC-001');
      expect(appointment.duration).toBe(30);
      expect(appointment.status).toBe('scheduled');
      expect(appointment.type).toBe('initial');
    });

    it('should allow optional notes', () => {
      const appointment: Appointment = {
        id: 'APT-002',
        patientId: 'PAT-002',
        doctorId: 'DOC-002',
        dateTime: new Date('2024-06-16T14:00:00'),
        duration: 45,
        status: 'completed',
        type: 'follow_up',
        notes: 'Patient recovering well',
        createdAt: new Date(),
        updatedAt: new Date(),
      };

      expect(appointment.notes).toBe('Patient recovering well');
    });
  });

  describe('AppointmentStatus', () => {
    it('should support all valid statuses', () => {
      const statuses: AppointmentStatus[] = [
        'scheduled',
        'confirmed',
        'checked_in',
        'in_progress',
        'completed',
        'cancelled',
        'no_show',
      ];

      statuses.forEach((status) => {
        expect([
          'scheduled',
          'confirmed',
          'checked_in',
          'in_progress',
          'completed',
          'cancelled',
          'no_show',
        ]).toContain(status);
      });
    });
  });

  describe('AppointmentType', () => {
    it('should support all valid types', () => {
      const types: AppointmentType[] = ['initial', 'follow_up', 'emergency', 'routine'];

      types.forEach((type) => {
        expect(['initial', 'follow_up', 'emergency', 'routine']).toContain(type);
      });
    });
  });

  describe('TimeSlot', () => {
    it('should have required fields', () => {
      const slot: TimeSlot = {
        startTime: new Date('2024-06-15T09:00:00'),
        endTime: new Date('2024-06-15T09:30:00'),
        doctorId: 'DOC-001',
        isAvailable: true,
      };

      expect(slot.startTime).toBeInstanceOf(Date);
      expect(slot.endTime).toBeInstanceOf(Date);
      expect(slot.doctorId).toBe('DOC-001');
      expect(slot.isAvailable).toBe(true);
    });
  });

  describe('CreateAppointmentDTO', () => {
    it('should have required fields for creation', () => {
      const dto: CreateAppointmentDTO = {
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      };

      expect(dto.patientId).toBe('PAT-001');
      expect(dto.doctorId).toBe('DOC-001');
      expect(dto.type).toBe('initial');
    });

    it('should allow optional duration and notes', () => {
      const dto: CreateAppointmentDTO = {
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        duration: 60,
        type: 'routine',
        notes: 'Annual checkup',
      };

      expect(dto.duration).toBe(60);
      expect(dto.notes).toBe('Annual checkup');
    });
  });

  describe('UpdateAppointmentDTO', () => {
    it('should allow partial updates', () => {
      const dto: UpdateAppointmentDTO = {
        status: 'completed',
      };

      expect(dto.status).toBe('completed');
      expect(dto.dateTime).toBeUndefined();
      expect(dto.notes).toBeUndefined();
    });

    it('should allow updating multiple fields', () => {
      const dto: UpdateAppointmentDTO = {
        dateTime: new Date('2024-06-20T15:00:00'),
        duration: 45,
        notes: 'Rescheduled',
      };

      expect(dto.dateTime).toBeInstanceOf(Date);
      expect(dto.duration).toBe(45);
      expect(dto.notes).toBe('Rescheduled');
    });
  });

  describe('Appointment status transitions', () => {
    it('should start as scheduled', () => {
      const appointment: Appointment = {
        id: 'APT-003',
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date(),
        duration: 30,
        status: 'scheduled',
        type: 'initial',
        createdAt: new Date(),
        updatedAt: new Date(),
      };

      expect(appointment.status).toBe('scheduled');
    });

    it('should track no_show status', () => {
      const appointment: Appointment = {
        id: 'APT-004',
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date(),
        duration: 30,
        status: 'no_show',
        type: 'initial',
        notes: 'Patient did not attend',
        createdAt: new Date(),
        updatedAt: new Date(),
      };

      expect(appointment.status).toBe('no_show');
      expect(appointment.notes).toBe('Patient did not attend');
    });
  });
});
