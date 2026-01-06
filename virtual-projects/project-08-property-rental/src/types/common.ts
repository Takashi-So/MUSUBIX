/**
 * Common Types for Property Rental System
 * 
 * @module types/common
 * @requirement REQ-RENTAL-001-NF001 (Data Integrity)
 */

import { Result, ok, err } from 'neverthrow';

// ============================================================
// ID Value Objects (BP-CODE-002: Date-based ID Format)
// ============================================================

export interface PropertyId {
  readonly value: string;
}

export interface TenantId {
  readonly value: string;
}

export interface LeaseContractId {
  readonly value: string;
}

export interface PaymentId {
  readonly value: string;
}

export interface MaintenanceRequestId {
  readonly value: string;
}

// ============================================================
// Money Value Object (BP-CODE-003, BP-CODE-004)
// ============================================================

export interface Money {
  readonly amount: number;
  readonly currency: 'JPY';
}

export function createMoney(amount: number): Result<Money, ValidationError> {
  if (amount < 0) {
    return err(new ValidationError('Amount must be non-negative'));
  }
  if (!Number.isInteger(amount)) {
    return err(new ValidationError('Amount must be an integer for JPY'));
  }
  return ok({ amount, currency: 'JPY' });
}

// ============================================================
// Address Value Object
// ============================================================

export interface Address {
  readonly prefecture: string;
  readonly city: string;
  readonly street: string;
  readonly building?: string;
}

export function createAddress(input: {
  prefecture: string;
  city: string;
  street: string;
  building?: string;
}): Result<Address, ValidationError> {
  if (!input.prefecture.trim()) {
    return err(new ValidationError('Prefecture is required'));
  }
  if (!input.city.trim()) {
    return err(new ValidationError('City is required'));
  }
  if (!input.street.trim()) {
    return err(new ValidationError('Street is required'));
  }
  return ok({
    prefecture: input.prefecture.trim(),
    city: input.city.trim(),
    street: input.street.trim(),
    building: input.building?.trim(),
  });
}

// ============================================================
// Email Value Object
// ============================================================

export interface Email {
  readonly value: string;
}

const EMAIL_REGEX = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;

export function createEmail(value: string): Result<Email, ValidationError> {
  if (!EMAIL_REGEX.test(value)) {
    return err(new ValidationError('Invalid email format'));
  }
  return ok({ value: value.toLowerCase() });
}

// ============================================================
// Phone Value Object
// ============================================================

export interface Phone {
  readonly value: string;
}

const PHONE_REGEX = /^[\d-]+$/;

export function createPhone(value: string): Result<Phone, ValidationError> {
  const cleaned = value.replace(/\s/g, '');
  if (!PHONE_REGEX.test(cleaned)) {
    return err(new ValidationError('Invalid phone format'));
  }
  if (cleaned.replace(/-/g, '').length < 10) {
    return err(new ValidationError('Phone number too short'));
  }
  return ok({ value: cleaned });
}

// ============================================================
// Emergency Contact
// ============================================================

export interface EmergencyContact {
  readonly name: string;
  readonly phone: Phone;
}

export function createEmergencyContact(input: {
  name: string;
  phone: string;
}): Result<EmergencyContact, ValidationError> {
  if (!input.name.trim()) {
    return err(new ValidationError('Emergency contact name is required'));
  }
  const phoneResult = createPhone(input.phone);
  if (phoneResult.isErr()) {
    return err(phoneResult.error);
  }
  return ok({
    name: input.name.trim(),
    phone: phoneResult.value,
  });
}

// ============================================================
// Status Types
// ============================================================

export type PropertyStatus = 'available' | 'pending' | 'occupied' | 'maintenance';
export type PropertyType = 'apartment' | 'house' | 'condominium';
export type VerificationStatus = 'pending-verification' | 'verified' | 'rejected';
export type ContractStatus = 'draft' | 'active' | 'terminated' | 'expired';
export type PaymentStatus = 'pending' | 'paid' | 'overdue';
export type PaymentMethod = 'bank-transfer' | 'credit-card' | 'cash' | 'auto-debit';
export type MaintenancePriority = 'emergency' | 'high' | 'medium' | 'low';
export type MaintenanceStatus = 'submitted' | 'assigned' | 'in-progress' | 'completed' | 'cancelled';
export type TerminationReason = 'natural-expiry' | 'early-termination' | 'breach';

// ============================================================
// Status Transition Maps (BP-DESIGN-001)
// ============================================================

export const validPropertyStatusTransitions: Record<PropertyStatus, PropertyStatus[]> = {
  'available': ['pending', 'maintenance'],
  'pending': ['occupied', 'available'],
  'occupied': ['available', 'maintenance'],
  'maintenance': ['available'],
};

export const validVerificationStatusTransitions: Record<VerificationStatus, VerificationStatus[]> = {
  'pending-verification': ['verified', 'rejected'],
  'verified': [],
  'rejected': [],
};

export const validContractStatusTransitions: Record<ContractStatus, ContractStatus[]> = {
  'draft': ['active'],
  'active': ['terminated', 'expired'],
  'terminated': [],
  'expired': [],
};

export const validMaintenanceStatusTransitions: Record<MaintenanceStatus, MaintenanceStatus[]> = {
  'submitted': ['assigned', 'cancelled'],
  'assigned': ['in-progress', 'cancelled'],
  'in-progress': ['completed', 'cancelled'],
  'completed': [],
  'cancelled': [],
};

// ============================================================
// Validation Error (BP-CODE-005)
// ============================================================

export class ValidationError extends Error {
  readonly _tag = 'ValidationError' as const;
  constructor(message: string) {
    super(message);
    this.name = 'ValidationError';
  }
}

// ============================================================
// ID Generation Utilities (BP-CODE-002)
// ============================================================

let propertyCounter = 0;
let tenantCounter = 0;
let contractCounter = 0;
let paymentCounter = 0;
let maintenanceCounter = 0;

function formatDate(date: Date): string {
  const year = date.getFullYear();
  const month = String(date.getMonth() + 1).padStart(2, '0');
  const day = String(date.getDate()).padStart(2, '0');
  return `${year}${month}${day}`;
}

export function generatePropertyId(date: Date = new Date()): PropertyId {
  propertyCounter++;
  return { value: `PROP-${formatDate(date)}-${String(propertyCounter).padStart(3, '0')}` };
}

export function generateTenantId(date: Date = new Date()): TenantId {
  tenantCounter++;
  return { value: `TEN-${formatDate(date)}-${String(tenantCounter).padStart(3, '0')}` };
}

export function generateLeaseContractId(date: Date = new Date()): LeaseContractId {
  contractCounter++;
  return { value: `LEASE-${formatDate(date)}-${String(contractCounter).padStart(3, '0')}` };
}

export function generatePaymentId(date: Date = new Date()): PaymentId {
  paymentCounter++;
  return { value: `PAY-${formatDate(date)}-${String(paymentCounter).padStart(3, '0')}` };
}

export function generateMaintenanceRequestId(date: Date = new Date()): MaintenanceRequestId {
  maintenanceCounter++;
  return { value: `MAINT-${formatDate(date)}-${String(maintenanceCounter).padStart(3, '0')}` };
}

// Counter reset for testing (BP-DESIGN-006)
export function resetPropertyCounter(): void { propertyCounter = 0; }
export function resetTenantCounter(): void { tenantCounter = 0; }
export function resetLeaseContractCounter(): void { contractCounter = 0; }
export function resetPaymentCounter(): void { paymentCounter = 0; }
export function resetMaintenanceCounter(): void { maintenanceCounter = 0; }
export function resetAllCounters(): void {
  resetPropertyCounter();
  resetTenantCounter();
  resetLeaseContractCounter();
  resetPaymentCounter();
  resetMaintenanceCounter();
}
