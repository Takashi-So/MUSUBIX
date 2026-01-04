// PetCare - ペット健康管理システム
// ドメインモデル・型定義

// ==================== 基本型 ====================

export type PetType = 'dog' | 'cat' | 'bird' | 'rabbit' | 'hamster' | 'other';
export type Gender = 'male' | 'female' | 'unknown';
export type AppointmentStatus = 'tentative' | 'confirmed' | 'active' | 'completed' | 'cancelled';

// ==================== エンティティ ====================

export interface Owner {
  id: string;
  name: string;
  email: string;
  phone: string;
  createdAt: Date;
}

export interface Pet {
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

export interface HealthRecord {
  id: string;
  petId: string;
  recordedAt: Date;
  weight: number;
  temperature?: number; // 35.0〜42.0°C
  symptoms: string[];
  notes?: string;
  recordedBy: string;
  createdAt: Date;
}

export interface Vaccination {
  id: string;
  petId: string;
  vaccineType: string;
  administeredAt: Date;
  nextDueDate: Date;
  lotNumber: string;
  administeredBy: string;
  clinicId: string;
  createdAt: Date;
}

export interface Appointment {
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

export interface VeterinaryClinic {
  id: string;
  name: string;
  address: string;
  phone: string;
  email: string;
}

export interface TimeSlot {
  startTime: Date;
  endTime: Date;
  available: boolean;
}

// ==================== 入力型 ====================

export interface PetInput {
  name: string;
  type: PetType;
  breed?: string;
  birthDate?: Date;
  weight?: number;
  gender?: Gender;
  photoUrl?: string;
}

export interface HealthRecordInput {
  weight: number;
  temperature?: number;
  symptoms?: string[];
  notes?: string;
  recordedAt?: Date;
}

export interface VaccinationInput {
  vaccineType: string;
  administeredAt: Date;
  lotNumber: string;
  clinicId: string;
}

export interface AppointmentInput {
  scheduledAt: Date;
  purpose: string;
  notes?: string;
}

// ==================== アラート・通知型 ====================

export interface WeightAlert {
  petId: string;
  petName: string;
  previousWeight: number;
  currentWeight: number;
  changePercent: number;
  alertType: 'increase' | 'decrease';
  createdAt: Date;
}

export interface VaccinationReminder {
  petId: string;
  petName: string;
  ownerId: string;
  ownerEmail: string;
  vaccination: Vaccination;
  daysUntilDue: number;
}

// ==================== クエリオプション ====================

export interface QueryOptions {
  limit?: number;
  offset?: number;
  orderBy?: string;
  order?: 'asc' | 'desc';
  startDate?: Date;
  endDate?: Date;
}

// ==================== 定数 ====================

export const TEMPERATURE_MIN = 35.0;
export const TEMPERATURE_MAX = 42.0;
export const WEIGHT_CHANGE_ALERT_THRESHOLD = 0.10; // 10%
export const VACCINE_REMINDER_DAYS = [14, 7, 1];
export const CANCEL_DEADLINE_HOURS = 24;
