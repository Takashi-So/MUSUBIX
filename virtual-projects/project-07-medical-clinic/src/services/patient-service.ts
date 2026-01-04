/**
 * PatientService
 * 
 * Business logic for patient management
 * 
 * @requirement REQ-CLINIC-001-F001 Patient Registration
 * @requirement REQ-CLINIC-001-F002 Patient Profile Management
 * @requirement REQ-CLINIC-001-F003 Patient Medical History
 * @task TSK-CLINIC-001-003
 */

import type { IPatientRepository } from '../domain/repositories/patient-repository.js';
import type {
  Patient,
  CreatePatientDTO,
  UpdatePatientDTO,
  MedicalHistory,
} from '../domain/entities/patient.js';

/**
 * Service result wrapper
 */
export interface ServiceResult<T> {
  success: boolean;
  data?: T;
  error?: string;
}

/**
 * Patient service for managing patient-related operations
 */
export class PatientService {
  constructor(private readonly patientRepository: IPatientRepository) {}

  /**
   * Register a new patient
   * @requirement REQ-CLINIC-001-F001
   */
  async registerPatient(data: CreatePatientDTO): Promise<ServiceResult<Patient>> {
    // Check for duplicate email
    const existing = await this.patientRepository.findByEmail(data.email);
    if (existing) {
      return {
        success: false,
        error: 'A patient with this email already exists',
      };
    }

    // Validate required fields
    if (!data.name || !data.email || !data.phone) {
      return {
        success: false,
        error: 'Name, email, and phone are required',
      };
    }

    // Validate email format
    const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    if (!emailRegex.test(data.email)) {
      return {
        success: false,
        error: 'Invalid email format',
      };
    }

    try {
      const patient = await this.patientRepository.create(data);
      return { success: true, data: patient };
    } catch (error) {
      return {
        success: false,
        error: `Failed to register patient: ${error}`,
      };
    }
  }

  /**
   * Get patient by ID
   * @requirement REQ-CLINIC-001-F002
   */
  async getPatient(id: string): Promise<ServiceResult<Patient>> {
    const patient = await this.patientRepository.findById(id);
    if (!patient) {
      return {
        success: false,
        error: 'Patient not found',
      };
    }
    return { success: true, data: patient };
  }

  /**
   * Update patient information
   * @requirement REQ-CLINIC-001-F002
   */
  async updatePatient(
    id: string,
    data: UpdatePatientDTO
  ): Promise<ServiceResult<Patient>> {
    const existing = await this.patientRepository.findById(id);
    if (!existing) {
      return {
        success: false,
        error: 'Patient not found',
      };
    }

    // If email is being updated, check for duplicates
    if (data.email && data.email !== existing.email) {
      const duplicate = await this.patientRepository.findByEmail(data.email);
      if (duplicate) {
        return {
          success: false,
          error: 'Email already in use by another patient',
        };
      }
    }

    try {
      const updated = await this.patientRepository.update(id, data);
      return { success: true, data: updated };
    } catch (error) {
      return {
        success: false,
        error: `Failed to update patient: ${error}`,
      };
    }
  }

  /**
   * Get patient's medical history
   * @requirement REQ-CLINIC-001-F003
   */
  async getMedicalHistory(patientId: string): Promise<ServiceResult<MedicalHistory[]>> {
    const patient = await this.patientRepository.findById(patientId);
    if (!patient) {
      return {
        success: false,
        error: 'Patient not found',
      };
    }

    const history = await this.patientRepository.getMedicalHistory(patientId);
    return { success: true, data: history };
  }

  /**
   * Add a medical history record
   * @requirement REQ-CLINIC-001-F003
   */
  async addMedicalHistory(
    patientId: string,
    doctorId: string,
    doctorName: string,
    diagnosis: string,
    treatment: string,
    notes?: string
  ): Promise<ServiceResult<MedicalHistory>> {
    const patient = await this.patientRepository.findById(patientId);
    if (!patient) {
      return {
        success: false,
        error: 'Patient not found',
      };
    }

    try {
      const record = await this.patientRepository.addMedicalHistory({
        patientId,
        doctorId,
        doctorName,
        diagnosis,
        treatment,
        notes,
        date: new Date(),
      });
      return { success: true, data: record };
    } catch (error) {
      return {
        success: false,
        error: `Failed to add medical history: ${error}`,
      };
    }
  }

  /**
   * List all patients
   */
  async listPatients(limit?: number, offset?: number): Promise<ServiceResult<Patient[]>> {
    const patients = await this.patientRepository.findAll(limit, offset);
    return { success: true, data: patients };
  }
}
