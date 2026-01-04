/**
 * Unit tests for PatientService
 * @task TSK-CLINIC-001-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { PatientService } from '../../src/services/patient-service.ts';
import { InMemoryPatientRepository } from '../../src/infrastructure/repositories/in-memory-patient-repository.ts';

describe('PatientService', () => {
  let service: PatientService;
  let repository: InMemoryPatientRepository;

  beforeEach(() => {
    repository = new InMemoryPatientRepository();
    service = new PatientService(repository);
  });

  describe('registerPatient', () => {
    it('should register a new patient successfully', async () => {
      const result = await service.registerPatient({
        name: 'John Doe',
        email: 'john@example.com',
        phone: '+81-90-1234-5678',
        dateOfBirth: new Date('1990-01-15'),
      });

      expect(result.success).toBe(true);
      expect(result.data?.name).toBe('John Doe');
      expect(result.data?.email).toBe('john@example.com');
    });

    it('should fail when email already exists', async () => {
      await service.registerPatient({
        name: 'John Doe',
        email: 'duplicate@example.com',
        phone: '+81-90-1111-1111',
        dateOfBirth: new Date('1990-01-01'),
      });

      const result = await service.registerPatient({
        name: 'Jane Doe',
        email: 'duplicate@example.com',
        phone: '+81-90-2222-2222',
        dateOfBirth: new Date('1990-02-02'),
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('already exists');
    });

    it('should fail when required fields are missing', async () => {
      const result = await service.registerPatient({
        name: '',
        email: 'test@example.com',
        phone: '+81-90-3333-3333',
        dateOfBirth: new Date('1990-01-01'),
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('required');
    });

    it('should fail for invalid email format', async () => {
      const result = await service.registerPatient({
        name: 'John Doe',
        email: 'invalid-email',
        phone: '+81-90-4444-4444',
        dateOfBirth: new Date('1990-01-01'),
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('email format');
    });
  });

  describe('getPatient', () => {
    it('should return patient when found', async () => {
      const registered = await service.registerPatient({
        name: 'Test Patient',
        email: 'test@example.com',
        phone: '+81-90-5555-5555',
        dateOfBirth: new Date('1990-01-01'),
      });

      const result = await service.getPatient(registered.data!.id);

      expect(result.success).toBe(true);
      expect(result.data?.name).toBe('Test Patient');
    });

    it('should return error when patient not found', async () => {
      const result = await service.getPatient('non-existent-id');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Patient not found');
    });
  });

  describe('updatePatient', () => {
    it('should update patient successfully', async () => {
      const registered = await service.registerPatient({
        name: 'Original Name',
        email: 'original@example.com',
        phone: '+81-90-6666-6666',
        dateOfBirth: new Date('1990-01-01'),
      });

      const result = await service.updatePatient(registered.data!.id, {
        name: 'Updated Name',
        phone: '+81-80-7777-7777',
      });

      expect(result.success).toBe(true);
      expect(result.data?.name).toBe('Updated Name');
      expect(result.data?.email).toBe('original@example.com');
    });

    it('should fail when patient not found', async () => {
      const result = await service.updatePatient('non-existent', {
        name: 'Test',
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe('Patient not found');
    });

    it('should fail when changing to duplicate email', async () => {
      await service.registerPatient({
        name: 'Existing',
        email: 'existing@example.com',
        phone: '+81-90-8888-8888',
        dateOfBirth: new Date('1990-01-01'),
      });

      const registered = await service.registerPatient({
        name: 'To Update',
        email: 'toupdate@example.com',
        phone: '+81-90-9999-9999',
        dateOfBirth: new Date('1990-02-02'),
      });

      const result = await service.updatePatient(registered.data!.id, {
        email: 'existing@example.com',
      });

      expect(result.success).toBe(false);
      expect(result.error).toContain('already in use');
    });
  });

  describe('getMedicalHistory', () => {
    it('should return medical history for patient', async () => {
      const registered = await service.registerPatient({
        name: 'History Patient',
        email: 'history@example.com',
        phone: '+81-70-1111-1111',
        dateOfBirth: new Date('1990-01-01'),
      });

      await service.addMedicalHistory(
        registered.data!.id,
        'DOC-001',
        'Dr. Smith',
        'Common cold',
        'Rest and fluids'
      );

      const result = await service.getMedicalHistory(registered.data!.id);

      expect(result.success).toBe(true);
      expect(result.data).toHaveLength(1);
      expect(result.data?.[0].diagnosis).toBe('Common cold');
    });

    it('should fail when patient not found', async () => {
      const result = await service.getMedicalHistory('non-existent');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Patient not found');
    });
  });

  describe('addMedicalHistory', () => {
    it('should add medical history record', async () => {
      const registered = await service.registerPatient({
        name: 'New History',
        email: 'newhistory@example.com',
        phone: '+81-70-2222-2222',
        dateOfBirth: new Date('1990-01-01'),
      });

      const result = await service.addMedicalHistory(
        registered.data!.id,
        'DOC-001',
        'Dr. Jones',
        'Headache',
        'Pain medication',
        'Follow up in 1 week'
      );

      expect(result.success).toBe(true);
      expect(result.data?.diagnosis).toBe('Headache');
      expect(result.data?.notes).toBe('Follow up in 1 week');
    });

    it('should fail when patient not found', async () => {
      const result = await service.addMedicalHistory(
        'non-existent',
        'DOC-001',
        'Dr. Smith',
        'Test',
        'Test'
      );

      expect(result.success).toBe(false);
      expect(result.error).toBe('Patient not found');
    });
  });

  describe('listPatients', () => {
    it('should return all patients', async () => {
      await service.registerPatient({
        name: 'Patient 1',
        email: 'p1@example.com',
        phone: '+81-70-1111-1111',
        dateOfBirth: new Date('1990-01-01'),
      });
      await service.registerPatient({
        name: 'Patient 2',
        email: 'p2@example.com',
        phone: '+81-70-2222-2222',
        dateOfBirth: new Date('1990-02-02'),
      });

      const result = await service.listPatients();

      expect(result.success).toBe(true);
      expect(result.data).toHaveLength(2);
    });

    it('should respect pagination', async () => {
      for (let i = 1; i <= 5; i++) {
        await service.registerPatient({
          name: `Patient ${i}`,
          email: `p${i}@example.com`,
          phone: `+81-70-${i}${i}${i}${i}-${i}${i}${i}${i}`,
          dateOfBirth: new Date('1990-01-01'),
        });
      }

      const result = await service.listPatients(2, 0);

      expect(result.success).toBe(true);
      expect(result.data).toHaveLength(2);
    });
  });
});
