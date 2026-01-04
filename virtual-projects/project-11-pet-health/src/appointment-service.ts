// PetCare - 予約サービス実装
// REQ-PET-001-07, REQ-PET-001-08 対応

import {
  Appointment,
  AppointmentInput,
  AppointmentStatus,
  TimeSlot,
  CANCEL_DEADLINE_HOURS,
} from './types';

// IdGenerator パターン
class AppointmentIdGenerator {
  private counter = 0;

  generate(): string {
    const timestamp = Date.now();
    this.counter++;
    return `APT-${timestamp}-${this.counter}`;
  }
}

// StatusWorkflow パターン（MUSUBIXから学習）
interface StatusTransition {
  from: AppointmentStatus;
  to: AppointmentStatus;
  action: string;
  guard?: () => boolean;
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
    return this.transitions.some(
      (t) => t.from === from && t.action === action
    );
  }

  transition(from: AppointmentStatus, action: string): AppointmentStatus {
    const found = this.transitions.find(
      (t) => t.from === from && t.action === action
    );
    if (!found) {
      throw new Error(`Invalid transition: ${from} -> ${action}`);
    }
    return found.to;
  }

  getAvailableActions(status: AppointmentStatus): string[] {
    return this.transitions
      .filter((t) => t.from === status)
      .map((t) => t.action);
  }
}

// リポジトリインターフェース
export interface IAppointmentRepository {
  save(appointment: Appointment): Promise<Appointment>;
  findById(id: string): Promise<Appointment | null>;
  findByPetId(petId: string): Promise<Appointment[]>;
  findByClinicAndDate(clinicId: string, date: Date): Promise<Appointment[]>;
  update(id: string, data: Partial<Appointment>): Promise<Appointment>;
}

// インメモリリポジトリ実装
export class InMemoryAppointmentRepository implements IAppointmentRepository {
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
    if (!existing) {
      throw new Error(`Appointment not found: ${id}`);
    }
    const updated = { ...existing, ...data, updatedAt: new Date() };
    this.appointments.set(id, updated);
    return updated;
  }

  clear(): void {
    this.appointments.clear();
  }
}

// 予約サービス
export class AppointmentService {
  private idGenerator = new AppointmentIdGenerator();
  private workflow = new AppointmentWorkflow();

  constructor(private repository: IAppointmentRepository) {}

  /**
   * 予約を作成
   * REQ-PET-001-07: WHEN オーナーが診療予約をリクエストした
   *                 THE システム SHALL 予約を作成すること
   */
  async create(
    petId: string,
    clinicId: string,
    ownerId: string,
    input: AppointmentInput
  ): Promise<Appointment> {
    // 重複チェック
    const existingAppointments = await this.repository.findByClinicAndDate(
      clinicId,
      input.scheduledAt
    );

    const conflicting = existingAppointments.find((a) => {
      const timeDiff = Math.abs(
        a.scheduledAt.getTime() - input.scheduledAt.getTime()
      );
      return timeDiff < 30 * 60 * 1000; // 30分以内は重複
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

  /**
   * 予約を確定
   */
  async confirm(appointmentId: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) {
      throw new Error(`Appointment not found: ${appointmentId}`);
    }

    const newStatus = this.workflow.transition(appointment.status, 'confirm');
    return this.repository.update(appointmentId, { status: newStatus });
  }

  /**
   * 予約をキャンセル
   * REQ-PET-001-08: IF 予約日の24時間前まで
   *                 THEN THE オーナー SHALL 予約をキャンセルできること
   */
  async cancel(appointmentId: string, reason?: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) {
      throw new Error(`Appointment not found: ${appointmentId}`);
    }

    // 24時間前チェック
    const now = new Date();
    const hoursUntilAppointment =
      (appointment.scheduledAt.getTime() - now.getTime()) / (1000 * 60 * 60);

    if (hoursUntilAppointment < CANCEL_DEADLINE_HOURS) {
      throw new Error(
        `Cannot cancel within ${CANCEL_DEADLINE_HOURS} hours of appointment`
      );
    }

    const newStatus = this.workflow.transition(appointment.status, 'cancel');
    return this.repository.update(appointmentId, {
      status: newStatus,
      cancelReason: reason,
    });
  }

  /**
   * 診療を開始
   */
  async start(appointmentId: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) {
      throw new Error(`Appointment not found: ${appointmentId}`);
    }

    const newStatus = this.workflow.transition(appointment.status, 'start');
    return this.repository.update(appointmentId, { status: newStatus });
  }

  /**
   * 診療を完了
   */
  async complete(appointmentId: string): Promise<Appointment> {
    const appointment = await this.repository.findById(appointmentId);
    if (!appointment) {
      throw new Error(`Appointment not found: ${appointmentId}`);
    }

    const newStatus = this.workflow.transition(appointment.status, 'complete');
    return this.repository.update(appointmentId, { status: newStatus });
  }

  /**
   * ペットの予約一覧を取得
   */
  async getByPet(petId: string): Promise<Appointment[]> {
    return this.repository.findByPetId(petId);
  }

  /**
   * 利用可能なアクションを取得
   */
  getAvailableActions(status: AppointmentStatus): string[] {
    return this.workflow.getAvailableActions(status);
  }
}
