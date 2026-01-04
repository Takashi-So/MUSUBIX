/**
 * IPatientRepository Interface
 * 
 * @requirement REQ-CLINIC-001-F001 Patient Registration
 * @requirement REQ-CLINIC-001-F002 Patient Profile Management
 * @design DES-CLINIC-001 Section 5.1 Repository Pattern
 */

import type { Patient, CreatePatientDTO, UpdatePatientDTO, MedicalHistory } from '../entities/patient.js';

/**
 * Repository interface for Patient entity
 * Implements Repository Pattern for data access abstraction
 */
export interface IPatientRepository {
  /**
   * Find a patient by ID
   * @param id - Patient UUID
   * @returns Patient or null if not found
   */
  findById(id: string): Promise<Patient | null>;

  /**
   * Find a patient by email address
   * @param email - Email address
   * @returns Patient or null if not found
   */
  findByEmail(email: string): Promise<Patient | null>;

  /**
   * Create a new patient record
   * @param data - Patient creation data
   * @returns Created patient
   */
  create(data: CreatePatientDTO): Promise<Patient>;

  /**
   * Update an existing patient record
   * @param id - Patient UUID
   * @param data - Update data
   * @returns Updated patient
   */
  update(id: string, data: UpdatePatientDTO): Promise<Patient>;

  /**
   * Delete a patient record
   * @param id - Patient UUID
   */
  delete(id: string): Promise<void>;

  /**
   * Get all patients with optional pagination
   * @param limit - Maximum number of results
   * @param offset - Number of records to skip
   */
  findAll(limit?: number, offset?: number): Promise<Patient[]>;

  /**
   * Get medical history for a patient
   * @param patientId - Patient UUID
   */
  getMedicalHistory(patientId: string): Promise<MedicalHistory[]>;

  /**
   * Add a medical history record
   * @param record - Medical history data
   */
  addMedicalHistory(record: Omit<MedicalHistory, 'id' | 'createdAt'>): Promise<MedicalHistory>;
}
