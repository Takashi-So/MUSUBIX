/**
 * Patient Entity
 * 
 * @requirement REQ-CLINIC-001-F001 Patient Registration
 * @requirement REQ-CLINIC-001-F002 Patient Profile Management
 * @requirement REQ-CLINIC-001-F003 Patient Medical History
 * @design DES-CLINIC-001 Section 4.2
 */

/**
 * Patient entity representing a clinic patient
 */
export interface Patient {
  /** Unique identifier (UUID) */
  id: string;
  /** Patient's full name */
  name: string;
  /** Email address */
  email: string;
  /** Phone number */
  phone: string;
  /** Date of birth */
  dateOfBirth: Date;
  /** Insurance ID (optional) */
  insuranceId?: string;
  /** List of known allergies */
  allergies: string[];
  /** Current medications */
  medications: string[];
  /** Account creation timestamp */
  createdAt: Date;
  /** Last update timestamp */
  updatedAt: Date;
}

/**
 * DTO for creating a new patient
 */
export interface CreatePatientDTO {
  name: string;
  email: string;
  phone: string;
  dateOfBirth: Date;
  insuranceId?: string;
  allergies?: string[];
  medications?: string[];
}

/**
 * DTO for updating patient information
 */
export interface UpdatePatientDTO {
  name?: string;
  email?: string;
  phone?: string;
  insuranceId?: string;
  allergies?: string[];
  medications?: string[];
}

/**
 * Medical history record
 */
export interface MedicalHistory {
  id: string;
  patientId: string;
  doctorId: string;
  doctorName: string;
  diagnosis: string;
  treatment: string;
  notes?: string;
  date: Date;
  createdAt: Date;
}
