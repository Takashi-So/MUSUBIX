/**
 * Tenant Entity
 * 
 * @requirement REQ-RENTAL-001-F010 (Tenant Registration)
 * @requirement REQ-RENTAL-001-F011 (Tenant Verification Status)
 * @design DES-RENTAL-001-C002
 */

import { Result, ok, err } from 'neverthrow';
import {
  TenantId,
  VerificationStatus,
  Email,
  Phone,
  EmergencyContact,
  generateTenantId,
  createEmail,
  createPhone,
  createEmergencyContact,
  validVerificationStatusTransitions,
  ValidationError,
} from '../types/common.js';
import { InvalidStatusTransitionError } from '../types/errors.js';

// ============================================================
// Tenant Entity
// ============================================================

export interface Tenant {
  readonly id: TenantId;
  readonly fullName: string;
  readonly email: Email;
  readonly phone: Phone;
  readonly emergencyContact: EmergencyContact;
  readonly verificationStatus: VerificationStatus;
  readonly createdAt: Date;
  readonly updatedAt: Date;
  readonly version: number;
}

// ============================================================
// Input DTO (BP-CODE-001)
// ============================================================

export interface CreateTenantInput {
  fullName: string;
  email: string;
  phone: string;
  emergencyContact: {
    name: string;
    phone: string;
  };
}

// ============================================================
// Factory Function
// ============================================================

export function createTenant(
  input: CreateTenantInput,
  date: Date = new Date()
): Result<Tenant, ValidationError> {
  // Validate full name
  const trimmedName = input.fullName.trim();
  if (!trimmedName) {
    return err(new ValidationError('Full name is required'));
  }

  // Validate email
  const emailResult = createEmail(input.email);
  if (emailResult.isErr()) {
    return err(emailResult.error);
  }

  // Validate phone
  const phoneResult = createPhone(input.phone);
  if (phoneResult.isErr()) {
    return err(phoneResult.error);
  }

  // Validate emergency contact
  const emergencyContactResult = createEmergencyContact(input.emergencyContact);
  if (emergencyContactResult.isErr()) {
    return err(emergencyContactResult.error);
  }

  const now = new Date();
  const tenant: Tenant = {
    id: generateTenantId(date),
    fullName: trimmedName,
    email: emailResult.value,
    phone: phoneResult.value,
    emergencyContact: emergencyContactResult.value,
    verificationStatus: 'pending-verification',
    createdAt: now,
    updatedAt: now,
    version: 1,
  };

  return ok(tenant);
}

// ============================================================
// Status Transition Functions
// ============================================================

export function canTransitionVerificationStatus(
  currentStatus: VerificationStatus,
  targetStatus: VerificationStatus
): boolean {
  const validTransitions = validVerificationStatusTransitions[currentStatus];
  return validTransitions.includes(targetStatus);
}

export function transitionVerificationStatus(
  tenant: Tenant,
  targetStatus: VerificationStatus
): Result<Tenant, InvalidStatusTransitionError> {
  if (!canTransitionVerificationStatus(tenant.verificationStatus, targetStatus)) {
    return err(
      new InvalidStatusTransitionError('Tenant', tenant.verificationStatus, targetStatus)
    );
  }

  const updatedTenant: Tenant = {
    ...tenant,
    verificationStatus: targetStatus,
    updatedAt: new Date(),
    version: tenant.version + 1,
  };

  return ok(updatedTenant);
}

// ============================================================
// Query Helpers
// ============================================================

export function isVerified(tenant: Tenant): boolean {
  return tenant.verificationStatus === 'verified';
}

export function canSignContract(tenant: Tenant): boolean {
  // REQ-RENTAL-001-F011: Tenant must be verified to sign contracts
  return tenant.verificationStatus === 'verified';
}
