/**
 * Unit tests for InMemoryPatientRepository
 * @task TSK-CLINIC-001-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { InMemoryPatientRepository } from '../../../src/infrastructure/repositories/in-memory-patient-repository.js';

describe('InMemoryPatientRepository', () => {
  let repository: InMemoryPatientRepository;

  beforeEach(() => {
    repository = new InMemoryPatientRepository();
  });

  describe('create', () => {
    it('should create a new patient with generated id', async () => {
      const patient = await repository.create({
        name: 'John Doe',
        email: 'john@example.com',
        phone: '+81-90-1234-5678',
        dateOfBirth: new Date('1990-01-15'),
      });

      expect(patient.id).toMatch(/^patient-/);
      expect(patient.name).toBe('John Doe');
      expect(patient.email).toBe('john@example.com');
      expect(patient.createdAt).toBeDefined();
      expect(patient.updatedAt).toBeDefined();
    });

    it('should initialize empty arrays for allergies and medications', async () => {
      const patient = await repository.create({
        name: 'Jane Smith',
        email: 'jane@example.com',
        phone: '+81-80-1111-2222',
        dateOfBirth: new Date('1990-05-15'),
      });

      expect(patient.allergies).toEqual([]);
      expect(patient.medications).toEqual([]);
    });

    it('should include optional fields when provided', async () => {
      const patient = await repository.create({
        name: 'Full Patient',
        email: 'full@example.com',
        phone: '+81-70-3333-4444',
        dateOfBirth: new Date('1985-12-25'),
        insuranceId: 'INS-12345',
        allergies: ['Penicillin'],
        medications: ['Aspirin'],
      });

      expect(patient.insuranceId).toBe('INS-12345');
      expect(patient.allergies).toContain('Penicillin');
      expect(patient.medications).toContain('Aspirin');
    });
  });

  describe('findById', () => {
    it('should find patient by id', async () => {
      const created = await repository.create({
        name: 'Test Patient',
        email: 'test@example.com',
        phone: '+81-70-5555-5555',
        dateOfBirth: new Date('1990-01-01'),
      });

      const found = await repository.findById(created.id);

      expect(found).not.toBeNull();
      expect(found?.id).toBe(created.id);
      expect(found?.name).toBe('Test Patient');
    });

    it('should return null for non-existent id', async () => {
      const found = await repository.findById('non-existent-id');
      expect(found).toBeNull();
    });
  });

  describe('findByEmail', () => {
    it('should find patient by email', async () => {
      await repository.create({
        name: 'Email Test',
        email: 'email-test@example.com',
        phone: '+81-70-6666-6666',
        dateOfBirth: new Date('1990-01-01'),
      });

      const found = await repository.findByEmail('email-test@example.com');

      expect(found).not.toBeNull();
      expect(found?.email).toBe('email-test@example.com');
    });

    it('should return null for non-existent email', async () => {
      const found = await repository.findByEmail('nonexistent@example.com');
      expect(found).toBeNull();
    });
  });

  describe('update', () => {
    it('should update patient fields', async () => {
      const created = await repository.create({
        name: 'Original Name',
        email: 'original@example.com',
        phone: '+81-70-7777-7777',
        dateOfBirth: new Date('1990-01-01'),
      });

      const updated = await repository.update(created.id, {
        name: 'Updated Name',
        phone: '+81-80-9999-0000',
      });

      expect(updated.name).toBe('Updated Name');
      expect(updated.phone).toBe('+81-80-9999-0000');
      expect(updated.email).toBe('original@example.com');
    });

    it('should throw error for non-existent patient', async () => {
      await expect(
        repository.update('non-existent', { name: 'Test' })
      ).rejects.toThrow('Patient not found');
    });
  });

  describe('delete', () => {
    it('should delete existing patient', async () => {
      const created = await repository.create({
        name: 'To Delete',
        email: 'delete@example.com',
        phone: '+81-70-1111-1111',
        dateOfBirth: new Date('1990-01-01'),
      });

      await repository.delete(created.id);

      const found = await repository.findById(created.id);
      expect(found).toBeNull();
    });

    it('should not throw for non-existent patient', async () => {
      // delete is idempotent - doesn't throw for non-existent
      await expect(repository.delete('non-existent')).resolves.toBeUndefined();
    });
  });

  describe('findAll', () => {
    it('should return all patients', async () => {
      await repository.create({
        name: 'Patient 1',
        email: 'p1@example.com',
        phone: '+81-70-1111-1111',
        dateOfBirth: new Date('1990-01-01'),
      });
      await repository.create({
        name: 'Patient 2',
        email: 'p2@example.com',
        phone: '+81-70-2222-2222',
        dateOfBirth: new Date('1990-02-02'),
      });
      await repository.create({
        name: 'Patient 3',
        email: 'p3@example.com',
        phone: '+81-70-3333-3333',
        dateOfBirth: new Date('1990-03-03'),
      });

      const patients = await repository.findAll();

      expect(patients).toHaveLength(3);
    });

    it('should respect limit parameter', async () => {
      for (let i = 1; i <= 5; i++) {
        await repository.create({
          name: `Patient ${i}`,
          email: `p${i}@example.com`,
          phone: `+81-70-${i}${i}${i}${i}-${i}${i}${i}${i}`,
          dateOfBirth: new Date('1990-01-01'),
        });
      }

      const patients = await repository.findAll(2);

      expect(patients).toHaveLength(2);
    });

    it('should respect offset parameter', async () => {
      for (let i = 1; i <= 5; i++) {
        await repository.create({
          name: `Patient ${i}`,
          email: `p${i}@example.com`,
          phone: `+81-70-${i}${i}${i}${i}-${i}${i}${i}${i}`,
          dateOfBirth: new Date('1990-01-01'),
        });
      }

      const patients = await repository.findAll(10, 2);

      expect(patients).toHaveLength(3);
    });
  });

  describe('Medical History', () => {
    let patientId: string;

    beforeEach(async () => {
      const patient = await repository.create({
        name: 'History Patient',
        email: 'history@example.com',
        phone: '+81-70-4444-4444',
        dateOfBirth: new Date('1990-01-01'),
      });
      patientId = patient.id;
    });

    it('should add medical history record', async () => {
      const record = await repository.addMedicalHistory({
        patientId,
        doctorId: 'DOC-001',
        doctorName: 'Dr. Smith',
        date: new Date('2024-01-15'),
        diagnosis: 'Common cold',
        treatment: 'Rest and fluids',
      });

      expect(record.id).toMatch(/^history-/);
      expect(record.diagnosis).toBe('Common cold');
      expect(record.treatment).toBe('Rest and fluids');
    });

    it('should get medical history for patient', async () => {
      await repository.addMedicalHistory({
        patientId,
        doctorId: 'DOC-001',
        doctorName: 'Dr. Smith',
        date: new Date('2024-01-15'),
        diagnosis: 'Cold',
        treatment: 'Rest',
      });
      await repository.addMedicalHistory({
        patientId,
        doctorId: 'DOC-002',
        doctorName: 'Dr. Jones',
        date: new Date('2024-02-20'),
        diagnosis: 'Headache',
        treatment: 'Medication',
      });

      const history = await repository.getMedicalHistory(patientId);

      expect(history).toHaveLength(2);
    });

    it('should return empty array for patient without history', async () => {
      const history = await repository.getMedicalHistory('non-existent');
      expect(history).toEqual([]);
    });
  });
});
