/**
 * Unit tests for InMemoryAppointmentRepository
 * @task TSK-CLINIC-001-006
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { InMemoryAppointmentRepository } from '../../../src/infrastructure/repositories/in-memory-appointment-repository.js';

describe('InMemoryAppointmentRepository', () => {
  let repository: InMemoryAppointmentRepository;

  beforeEach(() => {
    repository = new InMemoryAppointmentRepository();
  });

  describe('create', () => {
    it('should create a new appointment with generated id', async () => {
      const appointment = await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });

      expect(appointment.id).toMatch(/^APT-/);
      expect(appointment.patientId).toBe('PAT-001');
      expect(appointment.doctorId).toBe('DOC-001');
      expect(appointment.status).toBe('scheduled');
      expect(appointment.duration).toBe(30); // default
    });

    it('should include optional fields when provided', async () => {
      const appointment = await repository.create({
        patientId: 'PAT-002',
        doctorId: 'DOC-002',
        dateTime: new Date('2024-06-16T14:00:00'),
        duration: 60,
        type: 'follow_up',
        notes: 'Post-surgery follow-up',
      });

      expect(appointment.duration).toBe(60);
      expect(appointment.notes).toBe('Post-surgery follow-up');
    });
  });

  describe('findById', () => {
    it('should find appointment by id', async () => {
      const created = await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });

      const found = await repository.findById(created.id);

      expect(found).not.toBeNull();
      expect(found?.id).toBe(created.id);
    });

    it('should return null for non-existent id', async () => {
      const found = await repository.findById('non-existent');
      expect(found).toBeNull();
    });
  });

  describe('findByPatientId', () => {
    it('should find all appointments for a patient', async () => {
      await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });
      await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-002',
        dateTime: new Date('2024-06-16T11:00:00'),
        type: 'routine',
      });
      await repository.create({
        patientId: 'PAT-002',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T14:00:00'),
        type: 'initial',
      });

      const appointments = await repository.findByPatientId('PAT-001');

      expect(appointments).toHaveLength(2);
      expect(appointments.every((a) => a.patientId === 'PAT-001')).toBe(true);
    });
  });

  describe('findByDoctorId', () => {
    it('should find all appointments for a doctor', async () => {
      await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });
      await repository.create({
        patientId: 'PAT-002',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T11:00:00'),
        type: 'routine',
      });

      const appointments = await repository.findByDoctorId('DOC-001');

      expect(appointments).toHaveLength(2);
      expect(appointments.every((a) => a.doctorId === 'DOC-001')).toBe(true);
    });
  });

  describe('findByDoctorAndDateRange', () => {
    it('should find appointments within date range', async () => {
      await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });
      await repository.create({
        patientId: 'PAT-002',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-16T11:00:00'),
        type: 'routine',
      });
      await repository.create({
        patientId: 'PAT-003',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-20T10:00:00'),
        type: 'initial',
      });

      const appointments = await repository.findByDoctorAndDateRange(
        'DOC-001',
        new Date('2024-06-15T00:00:00'),
        new Date('2024-06-16T23:59:59')
      );

      expect(appointments).toHaveLength(2);
    });
  });

  describe('update', () => {
    it('should update appointment fields', async () => {
      const created = await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });

      const updated = await repository.update(created.id, {
        status: 'completed',
        notes: 'Appointment completed successfully',
      });

      expect(updated.status).toBe('completed');
      expect(updated.notes).toBe('Appointment completed successfully');
    });

    it('should throw error for non-existent appointment', async () => {
      await expect(
        repository.update('non-existent', { status: 'cancelled' })
      ).rejects.toThrow('Appointment not found');
    });
  });

  describe('delete', () => {
    it('should delete existing appointment', async () => {
      const created = await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });

      await repository.delete(created.id);

      const found = await repository.findById(created.id);
      expect(found).toBeNull();
    });

    it('should throw error for non-existent appointment', async () => {
      await expect(repository.delete('non-existent')).rejects.toThrow(
        'Appointment not found'
      );
    });
  });

  describe('getAvailableSlots', () => {
    it('should return all slots when no appointments exist', async () => {
      const date = new Date('2024-06-15');
      const slots = await repository.getAvailableSlots('DOC-001', date);

      // 9:00 to 17:00 with 30-min slots = 16 slots
      expect(slots.length).toBe(16);
      expect(slots.every((s) => s.isAvailable)).toBe(true);
    });

    it('should mark booked slots as unavailable', async () => {
      const date = new Date('2024-06-15');
      
      // Book a slot at 10:00
      await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });

      const slots = await repository.getAvailableSlots('DOC-001', date);

      // Find the 10:00 slot
      const bookedSlot = slots.find(
        (s) => s.startTime.getHours() === 10 && s.startTime.getMinutes() === 0
      );
      expect(bookedSlot?.isAvailable).toBe(false);
    });

    it('should not mark cancelled appointments as unavailable', async () => {
      const date = new Date('2024-06-15');
      
      const appt = await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });

      await repository.update(appt.id, { status: 'cancelled' });

      const slots = await repository.getAvailableSlots('DOC-001', date);

      const slot = slots.find(
        (s) => s.startTime.getHours() === 10 && s.startTime.getMinutes() === 0
      );
      expect(slot?.isAvailable).toBe(true);
    });
  });

  describe('findByStatus', () => {
    it('should find appointments by status', async () => {
      const appt1 = await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T10:00:00'),
        type: 'initial',
      });
      
      const appt2 = await repository.create({
        patientId: 'PAT-002',
        doctorId: 'DOC-001',
        dateTime: new Date('2024-06-15T11:00:00'),
        type: 'initial',
      });

      await repository.update(appt2.id, { status: 'completed' });

      const scheduled = await repository.findByStatus('scheduled');
      const completed = await repository.findByStatus('completed');

      expect(scheduled).toHaveLength(1);
      expect(completed).toHaveLength(1);
      expect(scheduled[0].status).toBe('scheduled');
      expect(completed[0].status).toBe('completed');
    });
  });

  describe('findUpcoming', () => {
    it('should find upcoming appointments within time window', async () => {
      const now = new Date();
      
      // Create appointment 30 minutes from now
      const soon = new Date(now.getTime() + 30 * 60 * 1000);
      await repository.create({
        patientId: 'PAT-001',
        doctorId: 'DOC-001',
        dateTime: soon,
        type: 'initial',
      });

      // Create appointment 2 hours from now
      const later = new Date(now.getTime() + 2 * 60 * 60 * 1000);
      await repository.create({
        patientId: 'PAT-002',
        doctorId: 'DOC-001',
        dateTime: later,
        type: 'initial',
      });

      const upcoming = await repository.findUpcoming(60); // within 60 minutes

      expect(upcoming).toHaveLength(1);
    });
  });
});
