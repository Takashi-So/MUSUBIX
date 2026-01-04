/**
 * AppointmentService
 * 
 * Business logic for appointment management
 * 
 * @requirement REQ-CLINIC-001-F010 Appointment Booking
 * @requirement REQ-CLINIC-001-F011 Appointment Cancellation
 * @requirement REQ-CLINIC-001-F012 Appointment Rescheduling
 * @requirement REQ-CLINIC-001-F015 No-Show Handling
 * @task TSK-CLINIC-001-007
 */

import type { IAppointmentRepository } from '../domain/repositories/appointment-repository.js';
import type { IPatientRepository } from '../domain/repositories/patient-repository.js';
import type {
  Appointment,
  TimeSlot,
  AppointmentType,
} from '../domain/entities/appointment.js';

/**
 * Service result wrapper
 */
export interface ServiceResult<T> {
  success: boolean;
  data?: T;
  error?: string;
}

/**
 * Booking request DTO
 */
export interface BookingRequest {
  patientId: string;
  doctorId: string;
  dateTime: Date;
  duration?: number;
  type: AppointmentType;
  notes?: string;
}

/**
 * Reschedule request DTO
 */
export interface RescheduleRequest {
  newDateTime: Date;
  duration?: number;
  notes?: string;
}

/**
 * Appointment service for managing appointment-related operations
 */
export class AppointmentService {
  // Minimum hours before appointment for cancellation
  private readonly MIN_CANCEL_HOURS = 24;
  // Minimum hours before appointment for rescheduling
  private readonly MIN_RESCHEDULE_HOURS = 24;
  // Maximum no-shows before blocking
  private readonly MAX_NO_SHOWS = 3;
  // Default appointment duration in minutes
  private readonly DEFAULT_DURATION = 30;

  constructor(
    private readonly appointmentRepository: IAppointmentRepository,
    private readonly patientRepository: IPatientRepository
  ) {}

  /**
   * Book a new appointment
   * @requirement REQ-CLINIC-001-F010
   */
  async bookAppointment(request: BookingRequest): Promise<ServiceResult<Appointment>> {
    // Verify patient exists
    const patient = await this.patientRepository.findById(request.patientId);
    if (!patient) {
      return { success: false, error: 'Patient not found' };
    }

    // Check patient's no-show history
    const patientAppointments = await this.appointmentRepository.findByPatientId(request.patientId);
    const noShowCount = patientAppointments.filter(
      (a) => a.status === 'no_show'
    ).length;
    if (noShowCount >= this.MAX_NO_SHOWS) {
      return {
        success: false,
        error: 'Booking blocked due to excessive no-shows. Please contact clinic.',
      };
    }

    // Check for conflicting appointments for the patient
    const duration = request.duration || this.DEFAULT_DURATION;
    const appointmentEnd = new Date(request.dateTime.getTime() + duration * 60 * 1000);
    
    const hasConflict = patientAppointments.some((appt) => {
      if (appt.status === 'cancelled' || appt.status === 'completed' || appt.status === 'no_show') {
        return false;
      }
      const existingEnd = new Date(appt.dateTime.getTime() + appt.duration * 60 * 1000);
      return this.timeRangesOverlap(
        request.dateTime,
        appointmentEnd,
        appt.dateTime,
        existingEnd
      );
    });
    
    if (hasConflict) {
      return {
        success: false,
        error: 'You already have an appointment at this time',
      };
    }

    // Check slot availability for the doctor
    const availableSlots = await this.appointmentRepository.getAvailableSlots(
      request.doctorId,
      request.dateTime
    );
    
    const slotAvailable = availableSlots.some((slot) => {
      return (
        slot.startTime.getTime() <= request.dateTime.getTime() &&
        slot.endTime.getTime() >= appointmentEnd.getTime() &&
        slot.isAvailable
      );
    });
    
    if (!slotAvailable) {
      return {
        success: false,
        error: 'Selected time slot is not available',
      };
    }

    try {
      const appointment = await this.appointmentRepository.create({
        patientId: request.patientId,
        doctorId: request.doctorId,
        dateTime: request.dateTime,
        duration: duration,
        type: request.type,
        notes: request.notes,
      });
      return { success: true, data: appointment };
    } catch (error) {
      return {
        success: false,
        error: `Failed to book appointment: ${error}`,
      };
    }
  }

  /**
   * Cancel an appointment
   * @requirement REQ-CLINIC-001-F011
   */
  async cancelAppointment(
    appointmentId: string,
    reason?: string
  ): Promise<ServiceResult<Appointment>> {
    const appointment = await this.appointmentRepository.findById(appointmentId);
    if (!appointment) {
      return { success: false, error: 'Appointment not found' };
    }

    // Check if already cancelled or completed
    if (appointment.status === 'cancelled') {
      return { success: false, error: 'Appointment is already cancelled' };
    }
    if (appointment.status === 'completed') {
      return { success: false, error: 'Cannot cancel a completed appointment' };
    }

    // Check cancellation time window
    const hoursUntilAppt = this.getHoursUntilAppointment(appointment);
    if (hoursUntilAppt < this.MIN_CANCEL_HOURS) {
      return {
        success: false,
        error: `Appointments must be cancelled at least ${this.MIN_CANCEL_HOURS} hours in advance`,
      };
    }

    try {
      const updated = await this.appointmentRepository.update(appointmentId, {
        status: 'cancelled',
        notes: reason ? `Cancelled: ${reason}` : 'Cancelled by patient',
      });
      return { success: true, data: updated };
    } catch (error) {
      return {
        success: false,
        error: `Failed to cancel appointment: ${error}`,
      };
    }
  }

  /**
   * Reschedule an appointment
   * @requirement REQ-CLINIC-001-F012
   */
  async rescheduleAppointment(
    appointmentId: string,
    request: RescheduleRequest
  ): Promise<ServiceResult<Appointment>> {
    const appointment = await this.appointmentRepository.findById(appointmentId);
    if (!appointment) {
      return { success: false, error: 'Appointment not found' };
    }

    // Check if can be rescheduled
    if (appointment.status !== 'scheduled' && appointment.status !== 'confirmed') {
      return {
        success: false,
        error: 'Only scheduled or confirmed appointments can be rescheduled',
      };
    }

    // Check reschedule time window
    const hoursUntilAppt = this.getHoursUntilAppointment(appointment);
    if (hoursUntilAppt < this.MIN_RESCHEDULE_HOURS) {
      return {
        success: false,
        error: `Appointments must be rescheduled at least ${this.MIN_RESCHEDULE_HOURS} hours in advance`,
      };
    }

    // Check new slot availability
    const duration = request.duration || appointment.duration;
    const appointmentEnd = new Date(request.newDateTime.getTime() + duration * 60 * 1000);
    
    const availableSlots = await this.appointmentRepository.getAvailableSlots(
      appointment.doctorId,
      request.newDateTime
    );
    
    const slotAvailable = availableSlots.some((slot) => {
      return (
        slot.startTime.getTime() <= request.newDateTime.getTime() &&
        slot.endTime.getTime() >= appointmentEnd.getTime() &&
        slot.isAvailable
      );
    });
    
    if (!slotAvailable) {
      return {
        success: false,
        error: 'Selected new time slot is not available',
      };
    }

    try {
      const updated = await this.appointmentRepository.update(appointmentId, {
        dateTime: request.newDateTime,
        duration: duration,
        notes: request.notes
          ? `Rescheduled: ${request.notes}`
          : 'Rescheduled by patient',
      });
      return { success: true, data: updated };
    } catch (error) {
      return {
        success: false,
        error: `Failed to reschedule appointment: ${error}`,
      };
    }
  }

  /**
   * Mark appointment as completed
   */
  async completeAppointment(
    appointmentId: string,
    notes?: string
  ): Promise<ServiceResult<Appointment>> {
    const appointment = await this.appointmentRepository.findById(appointmentId);
    if (!appointment) {
      return { success: false, error: 'Appointment not found' };
    }

    if (
      appointment.status !== 'scheduled' &&
      appointment.status !== 'confirmed' &&
      appointment.status !== 'in_progress' &&
      appointment.status !== 'checked_in'
    ) {
      return {
        success: false,
        error: 'Only scheduled, confirmed, checked-in, or in-progress appointments can be marked complete',
      };
    }

    try {
      const updated = await this.appointmentRepository.update(appointmentId, {
        status: 'completed',
        notes: notes || 'Appointment completed',
      });
      return { success: true, data: updated };
    } catch (error) {
      return {
        success: false,
        error: `Failed to complete appointment: ${error}`,
      };
    }
  }

  /**
   * Mark appointment as no-show
   * @requirement REQ-CLINIC-001-F015
   */
  async markNoShow(appointmentId: string): Promise<ServiceResult<Appointment>> {
    const appointment = await this.appointmentRepository.findById(appointmentId);
    if (!appointment) {
      return { success: false, error: 'Appointment not found' };
    }

    if (appointment.status !== 'scheduled' && appointment.status !== 'confirmed') {
      return {
        success: false,
        error: 'Only scheduled or confirmed appointments can be marked as no-show',
      };
    }

    try {
      const updated = await this.appointmentRepository.update(appointmentId, {
        status: 'no_show',
        notes: 'Patient did not attend',
      });
      return { success: true, data: updated };
    } catch (error) {
      return {
        success: false,
        error: `Failed to mark no-show: ${error}`,
      };
    }
  }

  /**
   * Get available time slots for a doctor on a specific date
   */
  async getAvailableSlots(
    doctorId: string,
    date: Date
  ): Promise<ServiceResult<TimeSlot[]>> {
    const slots = await this.appointmentRepository.getAvailableSlots(doctorId, date);
    return { success: true, data: slots };
  }

  /**
   * Get appointments for a patient
   */
  async getPatientAppointments(
    patientId: string
  ): Promise<ServiceResult<Appointment[]>> {
    const appointments = await this.appointmentRepository.findByPatientId(patientId);
    return { success: true, data: appointments };
  }

  /**
   * Get upcoming appointments (within specified minutes)
   */
  async getUpcomingAppointments(
    withinMinutes: number = 60
  ): Promise<ServiceResult<Appointment[]>> {
    const appointments = await this.appointmentRepository.findUpcoming(withinMinutes);
    return { success: true, data: appointments };
  }

  /**
   * Get estimated wait time for a doctor
   * @requirement REQ-CLINIC-001-F014
   */
  async getEstimatedWaitTime(doctorId: string): Promise<ServiceResult<number>> {
    const today = new Date();
    const todayStart = new Date(today);
    todayStart.setHours(0, 0, 0, 0);
    const todayEnd = new Date(today);
    todayEnd.setHours(23, 59, 59, 999);

    const doctorAppointments = await this.appointmentRepository.findByDoctorAndDateRange(
      doctorId,
      todayStart,
      todayEnd
    );
    
    // Count scheduled/in-progress appointments before now
    const activeAppointments = doctorAppointments.filter(
      (a) =>
        a.dateTime <= today &&
        (a.status === 'scheduled' || a.status === 'confirmed' || a.status === 'in_progress')
    );

    // Assume average 5 minutes delay per patient ahead
    const estimatedMinutes = activeAppointments.length * 5;
    return { success: true, data: estimatedMinutes };
  }

  /**
   * Helper: Check if two time ranges overlap
   */
  private timeRangesOverlap(
    start1: Date,
    end1: Date,
    start2: Date,
    end2: Date
  ): boolean {
    return start1.getTime() < end2.getTime() && start2.getTime() < end1.getTime();
  }

  /**
   * Helper: Calculate hours until appointment
   */
  private getHoursUntilAppointment(appointment: Appointment): number {
    const now = new Date();
    return (appointment.dateTime.getTime() - now.getTime()) / (1000 * 60 * 60);
  }
}
