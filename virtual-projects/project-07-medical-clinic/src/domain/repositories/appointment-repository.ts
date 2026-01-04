/**
 * IAppointmentRepository Interface
 * 
 * @requirement REQ-CLINIC-001-F010 Appointment Booking
 * @requirement REQ-CLINIC-001-F011 Appointment Cancellation
 * @design DES-CLINIC-001 Section 5.1 Repository Pattern
 */

import type { 
  Appointment, 
  CreateAppointmentDTO, 
  UpdateAppointmentDTO,
  TimeSlot,
  AppointmentStatus 
} from '../entities/appointment.js';

/**
 * Repository interface for Appointment entity
 */
export interface IAppointmentRepository {
  /**
   * Find an appointment by ID
   */
  findById(id: string): Promise<Appointment | null>;

  /**
   * Find appointments by patient ID
   */
  findByPatientId(patientId: string): Promise<Appointment[]>;

  /**
   * Find appointments by doctor ID
   */
  findByDoctorId(doctorId: string): Promise<Appointment[]>;

  /**
   * Find appointments by doctor and date range
   */
  findByDoctorAndDateRange(
    doctorId: string,
    startDate: Date,
    endDate: Date
  ): Promise<Appointment[]>;

  /**
   * Create a new appointment
   */
  create(data: CreateAppointmentDTO): Promise<Appointment>;

  /**
   * Update an existing appointment
   */
  update(id: string, data: UpdateAppointmentDTO): Promise<Appointment>;

  /**
   * Delete an appointment
   */
  delete(id: string): Promise<void>;

  /**
   * Get available time slots for a doctor on a specific date
   */
  getAvailableSlots(doctorId: string, date: Date): Promise<TimeSlot[]>;

  /**
   * Find appointments by status
   */
  findByStatus(status: AppointmentStatus): Promise<Appointment[]>;

  /**
   * Find appointments scheduled within a time range
   */
  findUpcoming(withinMinutes: number): Promise<Appointment[]>;
}
