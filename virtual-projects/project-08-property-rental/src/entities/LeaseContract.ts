/**
 * LeaseContract Entity
 * 
 * @requirement REQ-RENTAL-001-F020 (Contract Creation)
 * @requirement REQ-RENTAL-001-F021 (Contract Termination)
 * @requirement REQ-RENTAL-001-F022 (Contract Renewal)
 * @design DES-RENTAL-001-C003
 */

import { Result, ok, err } from 'neverthrow';
import {
  LeaseContractId,
  PropertyId,
  TenantId,
  ContractStatus,
  Money,
  TerminationReason,
  generateLeaseContractId,
  createMoney,
  validContractStatusTransitions,
  ValidationError,
} from '../types/common.js';
import { InvalidStatusTransitionError } from '../types/errors.js';

// ============================================================
// LeaseContract Entity
// ============================================================

export interface LeaseContract {
  readonly id: LeaseContractId;
  readonly propertyId: PropertyId;
  readonly tenantId: TenantId;
  readonly startDate: Date;
  readonly endDate: Date;
  readonly monthlyRent: Money;
  readonly deposit: Money;
  readonly status: ContractStatus;
  readonly terminationDate?: Date;
  readonly terminationReason?: TerminationReason;
  readonly createdAt: Date;
  readonly updatedAt: Date;
  readonly version: number;
}

// ============================================================
// Input DTO (BP-CODE-001)
// ============================================================

export interface CreateLeaseContractInput {
  propertyId: PropertyId;
  tenantId: TenantId;
  startDate: Date;
  endDate: Date;
  monthlyRent: number;
  deposit: number;
}

// ============================================================
// Factory Function
// ============================================================

export function createLeaseContract(
  input: CreateLeaseContractInput,
  date: Date = new Date()
): Result<LeaseContract, ValidationError> {
  // Validate dates
  if (input.endDate <= input.startDate) {
    return err(new ValidationError('Contract end date must be after start date'));
  }

  // Validate monthly rent
  const monthlyRentResult = createMoney(input.monthlyRent);
  if (monthlyRentResult.isErr()) {
    return err(monthlyRentResult.error);
  }

  // Validate deposit
  const depositResult = createMoney(input.deposit);
  if (depositResult.isErr()) {
    return err(depositResult.error);
  }

  const now = new Date();
  const contract: LeaseContract = {
    id: generateLeaseContractId(date),
    propertyId: input.propertyId,
    tenantId: input.tenantId,
    startDate: input.startDate,
    endDate: input.endDate,
    monthlyRent: monthlyRentResult.value,
    deposit: depositResult.value,
    status: 'draft',
    createdAt: now,
    updatedAt: now,
    version: 1,
  };

  return ok(contract);
}

// ============================================================
// Status Transition Functions
// ============================================================

export function canTransitionContractStatus(
  currentStatus: ContractStatus,
  targetStatus: ContractStatus
): boolean {
  const validTransitions = validContractStatusTransitions[currentStatus];
  return validTransitions.includes(targetStatus);
}

export function activateContract(
  contract: LeaseContract
): Result<LeaseContract, InvalidStatusTransitionError> {
  if (!canTransitionContractStatus(contract.status, 'active')) {
    return err(
      new InvalidStatusTransitionError('LeaseContract', contract.status, 'active')
    );
  }

  const updatedContract: LeaseContract = {
    ...contract,
    status: 'active',
    updatedAt: new Date(),
    version: contract.version + 1,
  };

  return ok(updatedContract);
}

export function terminateContract(
  contract: LeaseContract,
  reason: TerminationReason
): Result<LeaseContract, InvalidStatusTransitionError> {
  if (!canTransitionContractStatus(contract.status, 'terminated')) {
    return err(
      new InvalidStatusTransitionError('LeaseContract', contract.status, 'terminated')
    );
  }

  const now = new Date();
  const updatedContract: LeaseContract = {
    ...contract,
    status: 'terminated',
    terminationDate: now,
    terminationReason: reason,
    updatedAt: now,
    version: contract.version + 1,
  };

  return ok(updatedContract);
}

export function expireContract(
  contract: LeaseContract
): Result<LeaseContract, InvalidStatusTransitionError> {
  if (!canTransitionContractStatus(contract.status, 'expired')) {
    return err(
      new InvalidStatusTransitionError('LeaseContract', contract.status, 'expired')
    );
  }

  const now = new Date();
  const updatedContract: LeaseContract = {
    ...contract,
    status: 'expired',
    updatedAt: now,
    version: contract.version + 1,
  };

  return ok(updatedContract);
}

// ============================================================
// Query Helpers
// ============================================================

export function isActive(contract: LeaseContract): boolean {
  return contract.status === 'active';
}

export function isExpiringSoon(contract: LeaseContract, withinDays: number = 30): boolean {
  if (contract.status !== 'active') {
    return false;
  }

  const now = new Date();
  const daysUntilExpiry = Math.floor(
    (contract.endDate.getTime() - now.getTime()) / (1000 * 60 * 60 * 24)
  );

  return daysUntilExpiry >= 0 && daysUntilExpiry <= withinDays;
}

export function getContractDurationMonths(contract: LeaseContract): number {
  const startYear = contract.startDate.getFullYear();
  const startMonth = contract.startDate.getMonth();
  const endYear = contract.endDate.getFullYear();
  const endMonth = contract.endDate.getMonth();

  return (endYear - startYear) * 12 + (endMonth - startMonth);
}

// ============================================================
// Renewal Eligibility (REQ-RENTAL-001-F022)
// ============================================================

export interface RenewalEligibility {
  eligible: boolean;
  daysUntilExpiry: number;
  reason?: string;
}

export function checkRenewalEligibility(
  contract: LeaseContract,
  terminationIntentDeclared: boolean = false
): RenewalEligibility {
  if (contract.status !== 'active') {
    return {
      eligible: false,
      daysUntilExpiry: -1,
      reason: 'Contract is not active',
    };
  }

  const now = new Date();
  const daysUntilExpiry = Math.floor(
    (contract.endDate.getTime() - now.getTime()) / (1000 * 60 * 60 * 24)
  );

  if (daysUntilExpiry < 0) {
    return {
      eligible: false,
      daysUntilExpiry,
      reason: 'Contract has already expired',
    };
  }

  if (daysUntilExpiry > 30) {
    return {
      eligible: false,
      daysUntilExpiry,
      reason: 'Contract expiry is more than 30 days away',
    };
  }

  if (terminationIntentDeclared) {
    return {
      eligible: false,
      daysUntilExpiry,
      reason: 'Termination intent has been declared',
    };
  }

  return {
    eligible: true,
    daysUntilExpiry,
  };
}
