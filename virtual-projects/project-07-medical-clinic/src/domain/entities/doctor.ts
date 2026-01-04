/**
 * Doctor Entity
 * 
 * @requirement REQ-CLINIC-001-F020 Doctor Availability Setup
 * @requirement REQ-CLINIC-001-F021 Doctor Schedule View
 * @design DES-CLINIC-001 Section 4.2
 */

/**
 * Doctor entity representing a clinic physician
 */
export interface Doctor {
  /** Unique identifier (UUID) */
  id: string;
  /** Doctor's full name */
  name: string;
  /** Medical specialty */
  specialty: string;
  /** Medical license number */
  licenseNumber: string;
  /** Department */
  department: string;
  /** Email address */
  email: string;
  /** Phone number */
  phone: string;
  /** Whether the doctor is currently active */
  isActive: boolean;
  /** Account creation timestamp */
  createdAt: Date;
}

/**
 * Doctor schedule for a specific day
 */
export interface DoctorSchedule {
  /** Unique identifier */
  id: string;
  /** Reference to doctor */
  doctorId: string;
  /** Day of week (0=Sunday, 6=Saturday) */
  dayOfWeek: number;
  /** Start time (HH:MM format) */
  startTime: string;
  /** End time (HH:MM format) */
  endTime: string;
  /** Duration of each slot in minutes */
  slotDuration: number;
  /** Whether this schedule is active */
  isActive: boolean;
}

/**
 * DTO for creating a doctor
 */
export interface CreateDoctorDTO {
  name: string;
  specialty: string;
  licenseNumber: string;
  department: string;
  email: string;
  phone: string;
}

/**
 * DTO for setting doctor schedule
 */
export interface SetScheduleDTO {
  doctorId: string;
  dayOfWeek: number;
  startTime: string;
  endTime: string;
  slotDuration?: number;
}
