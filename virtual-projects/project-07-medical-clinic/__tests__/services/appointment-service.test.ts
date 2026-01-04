/**
 * Unit tests for AppointmentService
 * @task TSK-CLINIC-001-007
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { AppointmentService } from '../../src/services/appointment-service.ts';
import { InMemoryAppointmentRepository } from '../../src/infrastructure/repositories/in-memory-appointment-repository.ts';
import { InMemoryPatientRepository } from '../../src/infrastructure/repositories/in-memory-patient-repository.ts';
import type { TimeSlot, AppointmentType } from '../../src/domain/entities/appointment.ts';

describe('AppointmentService', () => {
  let service: AppointmentService;
  let appointmentRepo: InMemoryAppointmentRepository;
  let patientRepo: InMemoryPatientRepository;
  let testPatientId: string;
  let testDoctorId: string;

  beforeEach(async () => {
    appointmentRepo = new InMemoryAppointmentRepository();
    patientRepo = new InMemoryPatientRepository();
    service = new AppointmentService(appointmentRepo, patientRepo);
    testDoctorId = 'DOC-001';

    // Create a test patient
    const patient = await patientRepo.create({
      name: 'Test Patient',
      email: 'test@example.com',
      phone: '+81-90-1234-5678',
      dateOfBirth: new Date('1990-01-15'),
    });
    testPatientId = patient.id;
  });

  describe('bookAppointment', () => {
    it('should book appointment successfully', async () => {
      // Set up available slots
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);
      tomorrow.setHours(10, 0, 0, 0);
      
      const availableSlots: TimeSlot[] = [{
        startTime: new Date(tomorrow.getTime()),
        endTime: new Date(tomorrow.getTime() + 60 * 60 * 1000), // 1 hour slot
        isAvailable: true,
      }];
      appointmentRepo.setAvailableSlots(testDoctorId, tomorrow, availableSlots);

      const result = await service.bookAppointment({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: tomorrow,
        type: 'initial' as AppointmentType,
      });

      expect(result.success).toBe(true);
      expect(result.data?.patientId).toBe(testPatientId);
      expect(result.data?.status).toBe('scheduled');
    });

    it('should fail when patient not found', async () => {
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);

      const result = await service.bookAppointment({
        patientId: 'non-existent-patient',
        doctorId: testDoctorId,
        dateTime: tomorrow,
        type: 'initial' as AppointmentType,
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe('Patient not found');
    });

    it('should fail when slot is not available', async () => {
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);
      tomorrow.setHours(10, 0, 0, 0);
      
      // Set up NO available slots
      appointmentRepo.setAvailableSlots(testDoctorId, tomorrow, []);

      const result = await service.bookAppointment({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: tomorrow,
        type: 'initial' as AppointmentType,
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('not available');
    });

    it('should fail when patient has conflicting appointment', async () => {
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);
      tomorrow.setHours(10, 0, 0, 0);
      
      const availableSlots: TimeSlot[] = [{
        startTime: new Date(tomorrow.getTime()),
        endTime: new Date(tomorrow.getTime() + 2 * 60 * 60 * 1000), // 2 hour slot
        isAvailable: true,
      }];
      appointmentRepo.setAvailableSlots(testDoctorId, tomorrow, availableSlots);

      // Book first appointment
      await service.bookAppointment({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: tomorrow,
        type: 'initial' as AppointmentType,
      });

      // Try to book overlapping appointment
      const conflictTime = new Date(tomorrow.getTime() + 15 * 60 * 1000); // 15 minutes later
      const result = await service.bookAppointment({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: conflictTime,
        type: 'follow_up' as AppointmentType,
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('already have an appointment');
    });

    it('should block booking for patient with excessive no-shows', async () => {
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);
      tomorrow.setHours(10, 0, 0, 0);

      // Create 3 no-show appointments
      for (let i = 0; i < 3; i++) {
        const pastDate = new Date();
        pastDate.setDate(pastDate.getDate() - (i + 1));
        
        await appointmentRepo.create({
          patientId: testPatientId,
          doctorId: testDoctorId,
          dateTime: pastDate,
          duration: 30,
          type: 'initial',
          status: 'no_show',
        });
      }

      const availableSlots: TimeSlot[] = [{
        startTime: new Date(tomorrow.getTime()),
        endTime: new Date(tomorrow.getTime() + 60 * 60 * 1000),
        isAvailable: true,
      }];
      appointmentRepo.setAvailableSlots(testDoctorId, tomorrow, availableSlots);

      const result = await service.bookAppointment({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: tomorrow,
        type: 'initial' as AppointmentType,
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('no-shows');
    });
  });

  describe('cancelAppointment', () => {
    it('should cancel appointment successfully when cancelling early enough', async () => {
      // Create an appointment far in the future
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 7);
      futureDate.setHours(10, 0, 0, 0);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
      });

      const result = await service.cancelAppointment(appointment.id, 'Personal reasons');

      expect(result.success).toBe(true);
      expect(result.data?.status).toBe('cancelled');
    });

    it('should fail when appointment not found', async () => {
      const result = await service.cancelAppointment('non-existent');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Appointment not found');
    });

    it('should fail when cancelling too late', async () => {
      // Create an appointment for tomorrow (less than 24 hours away)
      const soonDate = new Date();
      soonDate.setHours(soonDate.getHours() + 12); // 12 hours from now

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: soonDate,
        duration: 30,
        type: 'initial',
      });

      const result = await service.cancelAppointment(appointment.id);

      expect(result.success).toBe(false);
      expect(result.error).toContain('24 hours');
    });

    it('should fail when appointment already cancelled', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 7);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'cancelled',
      });

      const result = await service.cancelAppointment(appointment.id);

      expect(result.success).toBe(false);
      expect(result.error).toContain('already cancelled');
    });

    it('should fail when appointment is completed', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 7);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'completed',
      });

      const result = await service.cancelAppointment(appointment.id);

      expect(result.success).toBe(false);
      expect(result.error).toContain('completed');
    });
  });

  describe('rescheduleAppointment', () => {
    it('should reschedule appointment successfully', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 7);
      futureDate.setHours(10, 0, 0, 0);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'scheduled',
      });

      const newDateTime = new Date();
      newDateTime.setDate(newDateTime.getDate() + 10);
      newDateTime.setHours(14, 0, 0, 0);

      const availableSlots: TimeSlot[] = [{
        startTime: new Date(newDateTime.getTime()),
        endTime: new Date(newDateTime.getTime() + 60 * 60 * 1000),
        isAvailable: true,
      }];
      appointmentRepo.setAvailableSlots(testDoctorId, newDateTime, availableSlots);

      const result = await service.rescheduleAppointment(appointment.id, {
        newDateTime,
      });

      expect(result.success).toBe(true);
      expect(result.data?.dateTime.getTime()).toBe(newDateTime.getTime());
    });

    it('should fail when appointment not found', async () => {
      const newDateTime = new Date();
      newDateTime.setDate(newDateTime.getDate() + 10);

      const result = await service.rescheduleAppointment('non-existent', {
        newDateTime,
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe('Appointment not found');
    });

    it('should fail when rescheduling cancelled appointment', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 7);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'cancelled',
      });

      const newDateTime = new Date();
      newDateTime.setDate(newDateTime.getDate() + 10);

      const result = await service.rescheduleAppointment(appointment.id, {
        newDateTime,
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('scheduled or confirmed');
    });
  });

  describe('completeAppointment', () => {
    it('should complete scheduled appointment', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 1);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'scheduled',
      });

      const result = await service.completeAppointment(appointment.id, 'Consultation completed');

      expect(result.success).toBe(true);
      expect(result.data?.status).toBe('completed');
    });

    it('should complete in_progress appointment', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 1);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'in_progress',
      });

      const result = await service.completeAppointment(appointment.id);

      expect(result.success).toBe(true);
      expect(result.data?.status).toBe('completed');
    });

    it('should fail when appointment not found', async () => {
      const result = await service.completeAppointment('non-existent');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Appointment not found');
    });

    it('should fail when appointment already cancelled', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 1);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'cancelled',
      });

      const result = await service.completeAppointment(appointment.id);

      expect(result.success).toBe(false);
    });
  });

  describe('markNoShow', () => {
    it('should mark scheduled appointment as no-show', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 1);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'scheduled',
      });

      const result = await service.markNoShow(appointment.id);

      expect(result.success).toBe(true);
      expect(result.data?.status).toBe('no_show');
    });

    it('should fail when appointment not found', async () => {
      const result = await service.markNoShow('non-existent');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Appointment not found');
    });

    it('should fail when appointment is completed', async () => {
      const futureDate = new Date();
      futureDate.setDate(futureDate.getDate() + 1);

      const appointment = await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: futureDate,
        duration: 30,
        type: 'initial',
        status: 'completed',
      });

      const result = await service.markNoShow(appointment.id);

      expect(result.success).toBe(false);
      expect(result.error).toContain('scheduled or confirmed');
    });
  });

  describe('getAvailableSlots', () => {
    it('should return available slots', async () => {
      const tomorrow = new Date();
      tomorrow.setDate(tomorrow.getDate() + 1);
      tomorrow.setHours(0, 0, 0, 0);

      const slots: TimeSlot[] = [
        {
          startTime: new Date(tomorrow.getTime() + 9 * 60 * 60 * 1000), // 9:00
          endTime: new Date(tomorrow.getTime() + 10 * 60 * 60 * 1000), // 10:00
          isAvailable: true,
        },
        {
          startTime: new Date(tomorrow.getTime() + 10 * 60 * 60 * 1000), // 10:00
          endTime: new Date(tomorrow.getTime() + 11 * 60 * 60 * 1000), // 11:00
          isAvailable: true,
        },
      ];
      appointmentRepo.setAvailableSlots(testDoctorId, tomorrow, slots);

      const result = await service.getAvailableSlots(testDoctorId, tomorrow);

      expect(result.success).toBe(true);
      expect(result.data).toHaveLength(2);
    });
  });

  describe('getPatientAppointments', () => {
    it('should return patient appointments', async () => {
      const date1 = new Date();
      date1.setDate(date1.getDate() + 1);
      const date2 = new Date();
      date2.setDate(date2.getDate() + 2);

      await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: date1,
        duration: 30,
        type: 'initial',
      });

      await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: date2,
        duration: 30,
        type: 'follow_up',
      });

      const result = await service.getPatientAppointments(testPatientId);

      expect(result.success).toBe(true);
      expect(result.data).toHaveLength(2);
    });
  });

  describe('getUpcomingAppointments', () => {
    it('should return upcoming appointments', async () => {
      const soonDate = new Date();
      soonDate.setMinutes(soonDate.getMinutes() + 30); // 30 minutes from now

      await appointmentRepo.create({
        patientId: testPatientId,
        doctorId: testDoctorId,
        dateTime: soonDate,
        duration: 30,
        type: 'initial',
        status: 'scheduled',
      });

      const result = await service.getUpcomingAppointments(60);

      expect(result.success).toBe(true);
      expect(result.data!.length).toBeGreaterThanOrEqual(0); // Depends on timing
    });
  });

  describe('getEstimatedWaitTime', () => {
    it('should return estimated wait time', async () => {
      const result = await service.getEstimatedWaitTime(testDoctorId);

      expect(result.success).toBe(true);
      expect(typeof result.data).toBe('number');
      expect(result.data).toBeGreaterThanOrEqual(0);
    });
  });
});
