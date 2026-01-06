/**
 * Domain Errors for Property Rental System
 * 
 * @module types/errors
 * @requirement REQ-RENTAL-001-NF002 (Audit Trail)
 */

import { ValidationError } from './common.js';

// ============================================================
// Base Domain Error
// ============================================================

export abstract class DomainError extends Error {
  abstract readonly _tag: string;
  readonly timestamp: Date;
  
  constructor(message: string) {
    super(message);
    this.timestamp = new Date();
  }
}

// ============================================================
// Entity Errors
// ============================================================

export class EntityNotFoundError extends DomainError {
  readonly _tag = 'EntityNotFoundError' as const;
  
  constructor(
    public readonly entityType: string,
    public readonly entityId: string
  ) {
    super(`${entityType} not found: ${entityId}`);
    this.name = 'EntityNotFoundError';
  }
}

export class DuplicateEntityError extends DomainError {
  readonly _tag = 'DuplicateEntityError' as const;
  
  constructor(
    public readonly entityType: string,
    public readonly entityId: string
  ) {
    super(`${entityType} already exists: ${entityId}`);
    this.name = 'DuplicateEntityError';
  }
}

// ============================================================
// Status Transition Errors
// ============================================================

export class InvalidStatusTransitionError extends DomainError {
  readonly _tag = 'InvalidStatusTransitionError' as const;
  
  constructor(
    public readonly entityType: string,
    public readonly currentStatus: string,
    public readonly targetStatus: string
  ) {
    super(`Invalid ${entityType} status transition: ${currentStatus} → ${targetStatus}`);
    this.name = 'InvalidStatusTransitionError';
  }
}

// ============================================================
// Business Rule Errors
// ============================================================

export class BusinessRuleViolationError extends DomainError {
  readonly _tag = 'BusinessRuleViolationError' as const;
  
  constructor(
    public readonly rule: string,
    message: string
  ) {
    super(message);
    this.name = 'BusinessRuleViolationError';
  }
}

export class PropertyNotAvailableError extends DomainError {
  readonly _tag = 'PropertyNotAvailableError' as const;
  
  constructor(
    public readonly propertyId: string,
    public readonly currentStatus: string
  ) {
    super(`Property ${propertyId} is not available (current status: ${currentStatus})`);
    this.name = 'PropertyNotAvailableError';
  }
}

export class TenantNotVerifiedError extends DomainError {
  readonly _tag = 'TenantNotVerifiedError' as const;
  
  constructor(
    public readonly tenantId: string,
    public readonly currentStatus: string
  ) {
    super(`Tenant ${tenantId} is not verified (current status: ${currentStatus})`);
    this.name = 'TenantNotVerifiedError';
  }
}

export class ContractConflictError extends DomainError {
  readonly _tag = 'ContractConflictError' as const;
  
  constructor(
    public readonly propertyId: string,
    public readonly existingContractId: string
  ) {
    super(`Property ${propertyId} already has active contract: ${existingContractId}`);
    this.name = 'ContractConflictError';
  }
}

// ============================================================
// Concurrency Errors
// ============================================================

export class OptimisticLockError extends DomainError {
  readonly _tag = 'OptimisticLockError' as const;
  
  constructor(
    public readonly entityType: string,
    public readonly entityId: string,
    public readonly expectedVersion: number,
    public readonly actualVersion: number
  ) {
    super(
      `Optimistic lock failed for ${entityType} ${entityId}: ` +
      `expected version ${expectedVersion}, found ${actualVersion}`
    );
    this.name = 'OptimisticLockError';
  }
}

// ============================================================
// Type Re-exports
// ============================================================

export { ValidationError };

// ============================================================
// Error Type Union
// ============================================================

export type PropertyRentalError =
  | ValidationError
  | EntityNotFoundError
  | DuplicateEntityError
  | InvalidStatusTransitionError
  | BusinessRuleViolationError
  | PropertyNotAvailableError
  | TenantNotVerifiedError
  | ContractConflictError
  | OptimisticLockError;
