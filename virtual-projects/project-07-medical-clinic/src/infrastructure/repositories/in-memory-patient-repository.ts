/**
 * InMemoryPatientRepository
 * 
 * In-memory implementation of IPatientRepository for testing
 * 
 * @requirement REQ-CLINIC-001-F001 Patient Registration
 * @requirement REQ-CLINIC-001-F002 Patient Profile Management
 * @task TSK-CLINIC-001-002
 */

import type { IPatientRepository } from '../../domain/repositories/patient-repository.js';
import type { 
  Patient, 
  CreatePatientDTO, 
  UpdatePatientDTO, 
  MedicalHistory 
} from '../../domain/entities/patient.js';

/**
 * In-memory implementation of patient repository
 */
export class InMemoryPatientRepository implements IPatientRepository {
  private patients: Map<string, Patient> = new Map();
  private medicalHistories: Map<string, MedicalHistory[]> = new Map();
  private idCounter = 0;

  /**
   * Generate a unique ID
   */
  private generateId(): string {
    return `patient-${++this.idCounter}`;
  }

  async findById(id: string): Promise<Patient | null> {
    return this.patients.get(id) || null;
  }

  async findByEmail(email: string): Promise<Patient | null> {
    for (const patient of this.patients.values()) {
      if (patient.email === email) {
        return patient;
      }
    }
    return null;
  }

  async create(data: CreatePatientDTO): Promise<Patient> {
    const now = new Date();
    const patient: Patient = {
      id: this.generateId(),
      name: data.name,
      email: data.email,
      phone: data.phone,
      dateOfBirth: data.dateOfBirth,
      insuranceId: data.insuranceId,
      allergies: data.allergies || [],
      medications: data.medications || [],
      createdAt: now,
      updatedAt: now,
    };
    this.patients.set(patient.id, patient);
    this.medicalHistories.set(patient.id, []);
    return patient;
  }

  async update(id: string, data: UpdatePatientDTO): Promise<Patient> {
    const patient = this.patients.get(id);
    if (!patient) {
      throw new Error(`Patient not found: ${id}`);
    }

    const updated: Patient = {
      ...patient,
      ...data,
      updatedAt: new Date(),
    };
    this.patients.set(id, updated);
    return updated;
  }

  async delete(id: string): Promise<void> {
    this.patients.delete(id);
    this.medicalHistories.delete(id);
  }

  async findAll(limit = 100, offset = 0): Promise<Patient[]> {
    const all = Array.from(this.patients.values());
    return all.slice(offset, offset + limit);
  }

  async getMedicalHistory(patientId: string): Promise<MedicalHistory[]> {
    return this.medicalHistories.get(patientId) || [];
  }

  async addMedicalHistory(
    record: Omit<MedicalHistory, 'id' | 'createdAt'>
  ): Promise<MedicalHistory> {
    const history: MedicalHistory = {
      ...record,
      id: `history-${Date.now()}`,
      createdAt: new Date(),
    };

    const histories = this.medicalHistories.get(record.patientId) || [];
    histories.push(history);
    this.medicalHistories.set(record.patientId, histories);

    return history;
  }

  /**
   * Clear all data (for testing)
   */
  clear(): void {
    this.patients.clear();
    this.medicalHistories.clear();
    this.idCounter = 0;
  }
}
