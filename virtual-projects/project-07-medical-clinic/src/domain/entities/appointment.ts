/**
 * Appointment Entity
 * 
 * @requirement REQ-CLINIC-001-F010 Appointment Booking
 * @requirement REQ-CLINIC-001-F011 Appointment Cancellation
 * @requirement REQ-CLINIC-001-F012 Appointment Rescheduling
 * @requirement REQ-CLINIC-001-F015 No-Show Handling
 * @design DES-CLINIC-001 Section 4.2
 */

/**
 * Appointment status enum
 */
export type AppointmentStatus = 
  | 'scheduled'
  | 'confirmed'
  | 'checked_in'
  | 'in_progress'
  | 'completed'
  | 'cancelled'
  | 'no_show';

/**
 * Appointment type enum
 */
export type AppointmentType = 
  | 'initial'
  | 'follow_up'
  | 'emergency'
  | 'routine';

/**
 * Appointment entity representing a scheduled consultation
 */
export interface Appointment {
  /** Unique identifier (UUID) */
  id: string;
  /** Reference to patient */
  patientId: string;
  /** Reference to doctor */
  doctorId: string;
  /** Scheduled date and time */
  dateTime: Date;
  /** Duration in minutes */
  duration: number;
  /** Current status */
  status: AppointmentStatus;
  /** Type of appointment */
  type: AppointmentType;
  /** Additional notes */
  notes?: string;
  /** Creation timestamp */
  createdAt: Date;
  /** Last update timestamp */
  updatedAt: Date;
}

/**
 * DTO for creating a new appointment
 */
export interface CreateAppointmentDTO {
  patientId: string;
  doctorId: string;
  dateTime: Date;
  duration?: number;
  type: AppointmentType;
  notes?: string;
  /** Optional status override (for testing/admin purposes) */
  status?: AppointmentStatus;
}

/**
 * DTO for updating an appointment
 */
export interface UpdateAppointmentDTO {
  dateTime?: Date;
  duration?: number;
  status?: AppointmentStatus;
  notes?: string;
}

/**
 * Time slot representing an available booking window
 */
export interface TimeSlot {
  startTime: Date;
  endTime: Date;
  doctorId: string;
  isAvailable: boolean;
}
