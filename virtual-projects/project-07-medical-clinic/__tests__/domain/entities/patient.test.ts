/**
 * Unit tests for Patient entity
 * @task TSK-CLINIC-001-001
 */

import { describe, it, expect } from 'vitest';
import type {
  Patient,
  CreatePatientDTO,
  UpdatePatientDTO,
  MedicalHistory,
} from '../../../src/domain/entities/patient.js';

describe('Patient Entity', () => {
  describe('Patient type structure', () => {
    it('should have required fields', () => {
      const patient: Patient = {
        id: 'patient-1',
        name: 'John Doe',
        email: 'john@example.com',
        phone: '+81-90-1234-5678',
        dateOfBirth: new Date('1990-01-15'),
        allergies: ['Penicillin'],
        medications: ['Aspirin'],
        createdAt: new Date(),
        updatedAt: new Date(),
      };

      expect(patient.id).toBe('patient-1');
      expect(patient.name).toBe('John Doe');
      expect(patient.email).toBe('john@example.com');
      expect(patient.phone).toBe('+81-90-1234-5678');
      expect(patient.allergies).toContain('Penicillin');
      expect(patient.medications).toContain('Aspirin');
    });

    it('should allow optional insuranceId', () => {
      const patient: Patient = {
        id: 'patient-2',
        name: 'Jane Smith',
        email: 'jane@example.com',
        phone: '+81-80-1111-2222',
        dateOfBirth: new Date('1985-05-20'),
        insuranceId: 'INS-12345',
        allergies: [],
        medications: [],
        createdAt: new Date(),
        updatedAt: new Date(),
      };

      expect(patient.insuranceId).toBe('INS-12345');
    });
  });

  describe('CreatePatientDTO', () => {
    it('should have required fields for creation', () => {
      const dto: CreatePatientDTO = {
        name: 'New Patient',
        email: 'new@example.com',
        phone: '+81-70-3333-4444',
        dateOfBirth: new Date('1995-03-10'),
      };

      expect(dto.name).toBe('New Patient');
      expect(dto.email).toBe('new@example.com');
      expect(dto.phone).toBe('+81-70-3333-4444');
      expect(dto.dateOfBirth).toBeInstanceOf(Date);
    });

    it('should allow optional fields', () => {
      const dto: CreatePatientDTO = {
        name: 'Full Patient',
        email: 'full@example.com',
        phone: '+81-70-5555-6666',
        dateOfBirth: new Date('1980-12-25'),
        insuranceId: 'INS-67890',
        allergies: ['Nuts', 'Shellfish'],
        medications: ['Vitamin D'],
      };

      expect(dto.insuranceId).toBe('INS-67890');
      expect(dto.allergies).toHaveLength(2);
      expect(dto.medications).toHaveLength(1);
    });
  });

  describe('UpdatePatientDTO', () => {
    it('should allow partial updates', () => {
      const dto: UpdatePatientDTO = {
        phone: '+81-80-7777-8888',
      };

      expect(dto.phone).toBe('+81-80-7777-8888');
      expect(dto.name).toBeUndefined();
      expect(dto.email).toBeUndefined();
    });
  });

  describe('MedicalHistory', () => {
    it('should have required fields', () => {
      const history: MedicalHistory = {
        id: 'history-1',
        patientId: 'patient-1',
        doctorId: 'DOC-001',
        doctorName: 'Dr. Smith',
        date: new Date('2024-01-15'),
        diagnosis: 'Common cold',
        treatment: 'Rest and fluids',
        createdAt: new Date(),
      };

      expect(history.id).toBe('history-1');
      expect(history.diagnosis).toBe('Common cold');
      expect(history.treatment).toBe('Rest and fluids');
    });

    it('should allow optional notes', () => {
      const history: MedicalHistory = {
        id: 'history-2',
        patientId: 'patient-1',
        doctorId: 'DOC-001',
        doctorName: 'Dr. Smith',
        date: new Date('2024-02-20'),
        diagnosis: 'Headache',
        treatment: 'Pain medication',
        notes: 'Follow up in 1 week if symptoms persist',
        createdAt: new Date(),
      };

      expect(history.notes).toBe('Follow up in 1 week if symptoms persist');
    });
  });
});
