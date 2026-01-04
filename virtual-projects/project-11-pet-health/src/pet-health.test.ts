// PetCare - ペット健康管理システム テスト
// 要件トレーサビリティ: REQ-PET-001-01 〜 REQ-PET-001-08

import { describe, it, expect, beforeEach } from 'vitest';

// ==================== Types ====================

type PetType = 'dog' | 'cat' | 'bird' | 'rabbit' | 'hamster' | 'other';
type Gender = 'male' | 'female' | 'unknown';
type AppointmentStatus = 'tentative' | 'confirmed' | 'active' | 'completed' | 'cancelled';

interface Pet {
  id: string;
  ownerId: string;
  name: string;
  type: PetType;
  breed: string;
  birthDate: Date;
  weight: number;
  gender: Gender;
  photoUrl?: string;
  createdAt: Date;
  updatedAt: Date;
}

interface PetInput {
  name: string;
  type: PetType;
  breed?: string;
  birthDate?: Date;
  weight?: number;
  gender?: Gender;
}

interface HealthRecord {
  id: string;
  petId: string;
  recordedAt: Date;
  weight: number;
  temperature?: number;
  symptoms: string[];
  notes?: string;
  recordedBy: string;
  createdAt: Date;
}

interface HealthRecordInput {
  weight: number;
  temperature?: number;
  symptoms?: string[];
  notes?: string;
  recordedAt?: Date;
}

interface WeightAlert {
  petId: string;
  petName: string;
  previousWeight: number;
  currentWeight: number;
  changePercent: number;
  alertType: 'increase' | 'decrease';
  createdAt: Date;
}

interface Appointment {
  id: string;
  petId: string;
  clinicId: string;
  ownerId: string;
  scheduledAt: Date;
  status: AppointmentStatus;
  purpose: string;
  notes?: string;
  cancelReason?: string;
  createdAt: Date;
  updatedAt: Date;
}

interface AppointmentInput {
  scheduledAt: Date;
  purpose: string;
  notes?: string;
}

const TEMPERATURE_MIN = 35.0;
const TEMPERATURE_MAX = 42.0;
const WEIGHT_CHANGE_ALERT_THRESHOLD = 0.10;
const CANCEL_DEADLINE_HOURS = 24;

// ==================== IdGenerator ====================

class IdGenerator {
  private counter = 0;
  constructor(private prefix: string) {}

  generate(): string {
    const timestamp = Date.now();
    this.counter++;
    return `${this.prefix}-${timestamp}-${this.counter}`;
  }

  reset(): void {
    this.counter = 0;
  }
}

// ==================== PetService ====================

interface IPetRepository {
  save(pet: Pet): Promise<Pet>;
  findById(id: string): Promise<Pet | null>;
  findByOwnerId(ownerId: string): Promise<Pet[]>;
  update(id: string, data: Partial<Pet>): Promise<Pet>;
  delete(id: string): Promise<void>;
}

class InMemoryPetRepository implements IPetRepository {
  private pets: Map<string, Pet> = new Map();

  async save(pet: Pet): Promise<Pet> {
    this.pets.set(pet.id, pet);
    return pet;
  }

  async findById(id: string): Promise<Pet | null> {
    return this.pets.get(id) || null;
  }

  async findByOwnerId(ownerId: string): Promise<Pet[]> {
    return Array.from(this.pets.values()).filter((pet) => pet.ownerId === ownerId);
  }

  async update(id: string, data: Partial<Pet>): Promise<Pet> {
    const existing = this.pets.get(id);
    if (!existing) throw new Error(`Pet not found: ${id}`);
    const updated = { ...existing, ...data, updatedAt: new Date() };
    this.pets.set(id, updated);
    return updated;
  }

  async delete(id: string): Promise<void> {
    this.pets.delete(id);
  }

  clear(): void {
    this.pets.clear();
  }
}

class PetService {
  private idGenerator = new IdGenerator('PET');

  constructor(private repository: IPetRepository) {}

  async register(ownerId: string, input: PetInput): Promise<Pet> {
    if (!input.name || input.name.trim() === '') {
      throw new Error('Pet name is required');
    }
    if (!input.type) {
      throw new Error('Pet type is required');
    }

    const now = new Date();
    const pet: Pet = {
      id: this.idGenerator.generate(),
      ownerId,
      name: input.name.trim(),
      type: input.type,
      breed: input.breed || '',
      birthDate: input.birthDate || now,
      weight: input.weight || 0,
      gender: input.gender || 'unknown',
      createdAt: now,
      updatedAt: now,
    };

    return this.repository.save(pet);
  }

  async getByOwner(ownerId: string): Promise<Pet[]> {
    return this.repository.findByOwnerId(ownerId);
  }

  async getById(petId: string): Promise<Pet | null> {
    return this.repository.findById(petId);
  }

  async delete(petId: string): Promise<void> {
    const existing = await this.repository.findById(petId);
    if (!existing) throw new Error(`Pet not found: ${petId}`);
    return this.repository.delete(petId);
  }
}

// ==================== HealthRecordService ====================

interface IHealthRecordRepository {
  save(record: HealthRecord): Promise<HealthRecord>;
  findByPetId(petId: string): Promise<HealthRecord[]>;
  findLatestByPetId(petId: string): Promise<HealthRecord | null>;
}

class InMemoryHealthRecordRepository implements IHealthRecordRepository {
  private records: Map<string, HealthRecord> = new Map();

  async save(record: HealthRecord): Promise<HealthRecord> {
    this.records.set(record.id, record);
    return record;
  }

  async findByPetId(petId: string): Promise<HealthRecord[]> {
    return Array.from(this.records.values())
      .filter((r) => r.petId === petId)
      .sort((a, b) => b.recordedAt.getTime() - a.recordedAt.getTime());
  }

  async findLatestByPetId(petId: string): Promise<HealthRecord | null> {
    const records = await this.findByPetId(petId);
    return records[0] || null;
  }

  clear(): void {
    this.records.clear();
  }
}

class HealthAlertService {
  checkWeightChange(
    petId: string,
    petName: string,
    previousWeight: number,
    currentWeight: number
  ): WeightAlert | null {
    if (previousWeight <= 0) return null;

    const changePercent = Math.abs(currentWeight - previousWeight) / previousWeight;

    if (changePercent >= WEIGHT_CHANGE_ALERT_THRESHOLD) {
      return {
        petId,
        petName,
        previousWeight,
        currentWeight,
        changePercent,
        alertType: currentWeight > previousWeight ? 'increase' : 'decrease',
        createdAt: new Date(),
      };
    }

    return null;
  }
}

class HealthRecordService {
  private idGenerator = new IdGenerator('HR');
  private alertService = new HealthAlertService();

  constructor(private repository: IHealthRecordRepository) {}

  async create(
    petId: string,
    petName: string,
    input: HealthRecordInput,
    recordedBy: string
  ): Promise<{ record: HealthRecord; alert: WeightAlert | null }> {
    if (input.weight <= 0) {
      throw new Error('Weight must be greater than 0');
    }

    if (input.temperature !== undefined) {
      if (input.temperature < TEMPERATURE_MIN || input.temperature > TEMPERATURE_MAX) {
        throw new Error(`Temperature must be between ${TEMPERATURE_MIN} and ${TEMPERATURE_MAX}`);
      }
    }

    // 前回記録を先に取得
    const previousRecord = await this.repository.findLatestByPetId(petId);

    const now = new Date();
    const record: HealthRecord = {
      id: this.idGenerator.generate(),
      petId,
      recordedAt: input.recordedAt || now,
      weight: input.weight,
      temperature: input.temperature,
      symptoms: input.symptoms || [],
      notes: input.notes,
      recordedBy,
      createdAt: now,
    };

    const savedRecord = await this.repository.save(record);

    // 前回記録との比較でアラートチェック
    let alert: WeightAlert | null = null;
    if (previousRecord) {
      alert = this.alertService.checkWeightChange(
        petId,
        petName,
        previousRecord.weight,
        input.weight
      );
    }

    return { record: savedRecord, alert };
  }

  async getHistory(petId: string): Promise<HealthRecord[]> {
    return this.repository.findByPetId(petId);
  }
}

// ==================== AppointmentService ====================

interface StatusTransition {
  from: AppointmentStatus;
  to: AppointmentStatus;
  action: string;
}

class AppointmentWorkflow {
  private transitions: StatusTransition[] = [
    { from: 'tentative', to: 'confirmed', action: 'confirm' },
    { from: 'tentative', to: 'cancelled', action: 'cancel' },
    { from: 'confirmed', to: 'active', action: 'start' },
    { from: 'confirmed', to: 'cancelled', action: 'cancel' },
    { from: 'active', to: 'completed', action: 'complete' },
  ];

  canTransition(from: AppointmentStatus, action: string): boolean {
    return this.transitions.some((t) => t.from === from && t.action === action);
  }

  transition(from: AppointmentStatus, action: string): AppointmentStatus {
    const found = this.transitions.find((t) => t.from === from && t.action === action);
    if (!found) throw new Error(`Invalid transition: ${from} -> ${action}`);
    return found.to;
  }

  getAvailableActions(status: AppointmentStatus): string[] {
    return this.transitions.filter((t) => t.from === status).map((t) => t.action);
  }
}

interface IAppointmentRepository {
  save(appointment: Appointment): Promise<Appointment>;
  findById(id: string): Promise<Appointment | null>;
  findByPetId(petId: string): Promise<Appointment[]>;
  findByClinicAndDate(clinicId: string, date: Date): Promise<Appointment[]>;
  update(id: string, data: Partial<Appointment>): Promise<Appointment>;
}

class InMemoryAppointmentRepository implements IAppointmentRepository {
  private appointments: Map<string, Appointment> = new Map();

  async save(appointment: Appointment): Promise<Appointment> {
    this.appointments.set(appointment.id, appointment);
    return appointment;
  }

  async findById(id: string): Promise<Appointment | null> {
    return this.appointments.get(id) || null;
  }

  async findByPetId(petId: string): Promise<Appointment[]> {
    return Array.from(this.appointments.values())
      .filter((a) => a.petId === petId)
      .sort((a, b) => b.scheduledAt.getTime() - a.scheduledAt.getTime());
  }

  async findByClinicAndDate(clinicId: string, date: Date): Promise<Appointment[]> {
    const startOfDay = new Date(date);
    startOfDay.setHours(0, 0, 0, 0);
    const endOfDay = new Date(date);
    endOfDay.setHours(23, 59, 59, 999);

    return Array.from(this.appointments.values()).filter(
      (a) =>
        a.clinicId === clinicId &&
        a.scheduledAt >= startOfDay &&
        a.scheduledAt <= endOfDay &&
        a.status !== 'cancelled'
    );
  }

  async update(id: string, data: Partial<Appointment>): Promise<Appointment> {
    const existing = this.appointments.get(id);
    if (!existing) throw new Error(`Appointment not found: ${id}`);
    const updated = { ...existing, ...data, updatedAt: new Date() };
    this.appointments.set(id, updated);
    return updated;
  }

  clear(): void {
    this.appointments.clear();
  }
}

class AppointmentService {
  private idGenerator = new IdGenerator('APT');
  private workflow = new AppointmentWorkflow();

  constructor(private repository: IAppointmentRepository) {}

  async create(
    petId: string,
    clinicId: string,
    ownerId: string,
    input: AppointmentInput
  ): Promise<Appointment> {
    const existingAppointments = await this.repository.findByClinicAndDate(
      clinicId,
      input.scheduledAt
    );

    const conflicting = existingAppointments.find((a) => {
      const timeDiff = Math.abs(a.scheduledAt.getTime() - input.scheduledAt.getTime());
      return timeDiff < 30 * 60 * 1000;
    });

    if (conflicting) {
      throw new Error('Time slot is not available');
    }

    const now = new Date();
    const appointment: Appointment = {
      id: this.idGenerator.generate(),
      petId,
      clinicId,
      ownerId,
      scheduledAt: input.scheduledAt,
      status: 'tentative',
      purpose: input.purpose,
      notes: input.notes,
      createdAt: now,
      updatedAt: now,
    };

    return this.repository.save(appointment);
  }

  async confirm(appointmentId: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) throw new Error(`Appointment not found: ${appointmentId}`);

    const newStatus = this.workflow.transition(appointment.status, 'confirm');
    return this.repository.update(appointmentId, { status: newStatus });
  }

  async cancel(appointmentId: string, reason?: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) throw new Error(`Appointment not found: ${appointmentId}`);

    const now = new Date();
    const hoursUntilAppointment =
      (appointment.scheduledAt.getTime() - now.getTime()) / (1000 * 60 * 60);

    if (hoursUntilAppointment < CANCEL_DEADLINE_HOURS) {
      throw new Error(`Cannot cancel within ${CANCEL_DEADLINE_HOURS} hours of appointment`);
    }

    const newStatus = this.workflow.transition(appointment.status, 'cancel');
    return this.repository.update(appointmentId, {
      status: newStatus,
      cancelReason: reason,
    });
  }

  async start(appointmentId: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) throw new Error(`Appointment not found: ${appointmentId}`);

    const newStatus = this.workflow.transition(appointment.status, 'start');
    return this.repository.update(appointmentId, { status: newStatus });
  }

  async complete(appointmentId: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) throw new Error(`Appointment not found: ${appointmentId}`);

    const newStatus = this.workflow.transition(appointment.status, 'complete');
    return this.repository.update(appointmentId, { status: newStatus });
  }

  getAvailableActions(status: AppointmentStatus): string[] {
    return this.workflow.getAvailableActions(status);
  }
}

// ==================== Tests ====================

describe('PetCare - ペット健康管理システム', () => {
  // REQ-PET-001-01, REQ-PET-001-02
  describe('PetService', () => {
    let petRepository: InMemoryPetRepository;
    let petService: PetService;

    beforeEach(() => {
      petRepository = new InMemoryPetRepository();
      petService = new PetService(petRepository);
    });

    it('should register a pet with valid data', async () => {
      const pet = await petService.register('owner-1', {
        name: 'ポチ',
        type: 'dog',
        breed: '柴犬',
        weight: 10.5,
        gender: 'male',
      });

      expect(pet.id).toMatch(/^PET-\d+-\d+$/);
      expect(pet.name).toBe('ポチ');
      expect(pet.type).toBe('dog');
      expect(pet.breed).toBe('柴犬');
      expect(pet.weight).toBe(10.5);
    });

    it('should reject pet without name', async () => {
      await expect(
        petService.register('owner-1', { name: '', type: 'dog' })
      ).rejects.toThrow('Pet name is required');
    });

    it('should reject pet without type', async () => {
      await expect(
        petService.register('owner-1', { name: 'ポチ', type: undefined as any })
      ).rejects.toThrow('Pet type is required');
    });

    it('should get all pets for an owner', async () => {
      await petService.register('owner-1', { name: 'ポチ', type: 'dog' });
      await petService.register('owner-1', { name: 'タマ', type: 'cat' });
      await petService.register('owner-2', { name: 'ミケ', type: 'cat' });

      const pets = await petService.getByOwner('owner-1');
      expect(pets).toHaveLength(2);
      expect(pets.map((p) => p.name)).toContain('ポチ');
      expect(pets.map((p) => p.name)).toContain('タマ');
    });

    it('should generate unique IDs even in rapid succession', async () => {
      const pets = await Promise.all([
        petService.register('owner-1', { name: 'Pet1', type: 'dog' }),
        petService.register('owner-1', { name: 'Pet2', type: 'dog' }),
        petService.register('owner-1', { name: 'Pet3', type: 'dog' }),
      ]);

      const ids = pets.map((p) => p.id);
      const uniqueIds = new Set(ids);
      expect(uniqueIds.size).toBe(3);
    });
  });

  // REQ-PET-001-03, REQ-PET-001-04
  describe('HealthRecordService', () => {
    let healthRepository: InMemoryHealthRecordRepository;
    let healthService: HealthRecordService;

    beforeEach(() => {
      healthRepository = new InMemoryHealthRecordRepository();
      healthService = new HealthRecordService(healthRepository);
    });

    it('should create a health record', async () => {
      const { record } = await healthService.create('pet-1', 'ポチ', {
        weight: 10.5,
        temperature: 38.5,
        symptoms: ['咳'],
        notes: '軽い風邪の可能性',
      }, 'staff-1');

      expect(record.id).toMatch(/^HR-\d+-\d+$/);
      expect(record.weight).toBe(10.5);
      expect(record.temperature).toBe(38.5);
      expect(record.symptoms).toContain('咳');
    });

    it('should reject invalid weight', async () => {
      await expect(
        healthService.create('pet-1', 'ポチ', { weight: 0 }, 'staff-1')
      ).rejects.toThrow('Weight must be greater than 0');
    });

    it('should reject temperature out of range', async () => {
      await expect(
        healthService.create('pet-1', 'ポチ', { weight: 10, temperature: 45 }, 'staff-1')
      ).rejects.toThrow(`Temperature must be between ${TEMPERATURE_MIN} and ${TEMPERATURE_MAX}`);
    });

    it('should generate weight alert when change exceeds 10%', async () => {
      // 最初の記録
      await healthService.create('pet-1', 'ポチ', { weight: 10.0 }, 'staff-1');

      // 15%増加
      const { alert } = await healthService.create('pet-1', 'ポチ', { weight: 11.5 }, 'staff-1');

      expect(alert).not.toBeNull();
      expect(alert!.alertType).toBe('increase');
      expect(alert!.changePercent).toBeGreaterThanOrEqual(0.1);
    });

    it('should not generate alert for small weight change', async () => {
      await healthService.create('pet-1', 'ポチ', { weight: 10.0 }, 'staff-1');

      // 5%増加（閾値以下）
      const { alert } = await healthService.create('pet-1', 'ポチ', { weight: 10.5 }, 'staff-1');

      expect(alert).toBeNull();
    });
  });

  // REQ-PET-001-07, REQ-PET-001-08
  describe('AppointmentService', () => {
    let appointmentRepository: InMemoryAppointmentRepository;
    let appointmentService: AppointmentService;

    beforeEach(() => {
      appointmentRepository = new InMemoryAppointmentRepository();
      appointmentService = new AppointmentService(appointmentRepository);
    });

    it('should create an appointment', async () => {
      const scheduledAt = new Date(Date.now() + 48 * 60 * 60 * 1000); // 48時間後

      const appointment = await appointmentService.create(
        'pet-1',
        'clinic-1',
        'owner-1',
        { scheduledAt, purpose: '定期健診' }
      );

      expect(appointment.id).toMatch(/^APT-\d+-\d+$/);
      expect(appointment.status).toBe('tentative');
      expect(appointment.purpose).toBe('定期健診');
    });

    it('should confirm an appointment', async () => {
      const scheduledAt = new Date(Date.now() + 48 * 60 * 60 * 1000);
      const appointment = await appointmentService.create(
        'pet-1',
        'clinic-1',
        'owner-1',
        { scheduledAt, purpose: '定期健診' }
      );

      const confirmed = await appointmentService.confirm(appointment.id);
      expect(confirmed.status).toBe('confirmed');
    });

    it('should follow correct status workflow', async () => {
      const scheduledAt = new Date(Date.now() + 48 * 60 * 60 * 1000);
      const appointment = await appointmentService.create(
        'pet-1',
        'clinic-1',
        'owner-1',
        { scheduledAt, purpose: '定期健診' }
      );

      // tentative → confirmed
      let updated = await appointmentService.confirm(appointment.id);
      expect(updated.status).toBe('confirmed');

      // confirmed → active
      updated = await appointmentService.start(appointment.id);
      expect(updated.status).toBe('active');

      // active → completed
      updated = await appointmentService.complete(appointment.id);
      expect(updated.status).toBe('completed');
    });

    it('should allow cancellation more than 24 hours before', async () => {
      const scheduledAt = new Date(Date.now() + 48 * 60 * 60 * 1000); // 48時間後
      const appointment = await appointmentService.create(
        'pet-1',
        'clinic-1',
        'owner-1',
        { scheduledAt, purpose: '定期健診' }
      );

      const cancelled = await appointmentService.cancel(appointment.id, 'スケジュール変更');
      expect(cancelled.status).toBe('cancelled');
      expect(cancelled.cancelReason).toBe('スケジュール変更');
    });

    it('should reject cancellation within 24 hours', async () => {
      const scheduledAt = new Date(Date.now() + 12 * 60 * 60 * 1000); // 12時間後
      const appointment = await appointmentService.create(
        'pet-1',
        'clinic-1',
        'owner-1',
        { scheduledAt, purpose: '定期健診' }
      );

      await expect(
        appointmentService.cancel(appointment.id)
      ).rejects.toThrow(`Cannot cancel within ${CANCEL_DEADLINE_HOURS} hours of appointment`);
    });

    it('should reject conflicting appointments', async () => {
      const scheduledAt = new Date(Date.now() + 48 * 60 * 60 * 1000);

      await appointmentService.create(
        'pet-1',
        'clinic-1',
        'owner-1',
        { scheduledAt, purpose: '定期健診' }
      );

      // 同じ時間に別の予約
      await expect(
        appointmentService.create(
          'pet-2',
          'clinic-1',
          'owner-2',
          { scheduledAt, purpose: '予防接種' }
        )
      ).rejects.toThrow('Time slot is not available');
    });

    it('should provide available actions for each status', () => {
      expect(appointmentService.getAvailableActions('tentative')).toContain('confirm');
      expect(appointmentService.getAvailableActions('tentative')).toContain('cancel');
      expect(appointmentService.getAvailableActions('confirmed')).toContain('start');
      expect(appointmentService.getAvailableActions('active')).toContain('complete');
      expect(appointmentService.getAvailableActions('completed')).toHaveLength(0);
    });
  });

  // HealthAlertService
  describe('HealthAlertService', () => {
    const alertService = new HealthAlertService();

    it('should detect weight increase alert', () => {
      const alert = alertService.checkWeightChange('pet-1', 'ポチ', 10.0, 12.0);

      expect(alert).not.toBeNull();
      expect(alert!.alertType).toBe('increase');
      expect(alert!.changePercent).toBe(0.2);
    });

    it('should detect weight decrease alert', () => {
      const alert = alertService.checkWeightChange('pet-1', 'ポチ', 10.0, 8.5);

      expect(alert).not.toBeNull();
      expect(alert!.alertType).toBe('decrease');
      expect(alert!.changePercent).toBe(0.15);
    });

    it('should return null for no previous weight', () => {
      const alert = alertService.checkWeightChange('pet-1', 'ポチ', 0, 10.0);
      expect(alert).toBeNull();
    });
  });

  // AppointmentWorkflow
  describe('AppointmentWorkflow', () => {
    const workflow = new AppointmentWorkflow();

    it('should validate transitions', () => {
      expect(workflow.canTransition('tentative', 'confirm')).toBe(true);
      expect(workflow.canTransition('tentative', 'complete')).toBe(false);
      expect(workflow.canTransition('completed', 'cancel')).toBe(false);
    });

    it('should throw on invalid transition', () => {
      expect(() => workflow.transition('completed', 'cancel')).toThrow(
        'Invalid transition: completed -> cancel'
      );
    });
  });
});
