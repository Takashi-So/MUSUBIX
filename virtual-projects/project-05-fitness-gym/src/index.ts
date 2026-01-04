/**
 * FitGym Pro - Main Application Entry Point
 *
 * @module index
 * @description Exports all services and types for the FitGym Pro management system
 * @traces REQ-GYM-001 through REQ-GYM-020
 */

// ============================================================
// Member Service
// ============================================================
export {
  type Member,
  type MemberStatus,
  type CreateMemberInput,
  type UpdateMemberInput,
  type MemberFilterOptions,
  type CheckInResult,
  type UsageRecord,
  type IMemberService,
  type IMemberRepository,
  MemberService,
  createMemberService,
} from './member-service';

// ============================================================
// Booking Service
// ============================================================
export {
  type Booking,
  type BookingStatus,
  type GymClass,
  type ClassSchedule,
  type CreateBookingInput,
  type BookingFilterOptions,
  type AvailabilitySlot,
  type WaitlistEntry,
  type IBookingService,
  type IBookingRepository,
  type IClassRepository,
  BookingService,
  createBookingService,
} from './booking-service';

// ============================================================
// Trainer Service
// ============================================================
export {
  type Trainer,
  type TrainerStatus,
  type Specialization,
  type Certification,
  type WeeklyAvailability,
  type TimeSlot,
  type TrainerSession,
  type SessionStatus,
  type SessionType,
  type CreateTrainerInput,
  type TrainerFilterOptions,
  type TrainerPerformanceMetrics,
  type ITrainerService,
  type ITrainerRepository,
  type ITrainerSessionRepository,
  TrainerService,
  createTrainerService,
} from './trainer-service';

// ============================================================
// Equipment Service
// ============================================================
export {
  type Equipment,
  type EquipmentCategory,
  type EquipmentStatus,
  type MaintenanceRecord,
  type MaintenanceType,
  type EquipmentUsageLog,
  type CreateEquipmentInput,
  type EquipmentFilterOptions,
  type EquipmentUtilizationReport,
  type IEquipmentService,
  type IEquipmentRepository,
  type IMaintenanceRepository,
  type IUsageLogRepository,
  EquipmentService,
  createEquipmentService,
} from './equipment-service';

// ============================================================
// Payment Service
// ============================================================
export {
  type Payment,
  type PaymentType,
  type PaymentMethod,
  type PaymentStatus,
  type Invoice,
  type InvoiceItem,
  type InvoiceStatus,
  type Subscription,
  type BillingCycle,
  type SubscriptionStatus,
  type CreatePaymentInput,
  type CreateInvoiceInput,
  type RevenueReport,
  type IPaymentService,
  type IPaymentRepository,
  type IInvoiceRepository,
  type ISubscriptionRepository,
  PaymentService,
  createPaymentService,
} from './payment-service';
