/**
 * MaintenanceRequest Entity
 * 
 * @requirement REQ-RENTAL-001-F040 (Maintenance Request Submission)
 * @requirement REQ-RENTAL-001-F041 (Maintenance Request Status Workflow)
 * @requirement REQ-RENTAL-001-F042 (Emergency Maintenance Escalation)
 * @design DES-RENTAL-001-C005
 */

import { Result, ok, err } from 'neverthrow';
import {
  MaintenanceRequestId,
  PropertyId,
  TenantId,
  MaintenancePriority,
  MaintenanceStatus,
  generateMaintenanceRequestId,
  validMaintenanceStatusTransitions,
  ValidationError,
} from '../types/common.js';
import { InvalidStatusTransitionError } from '../types/errors.js';

// ============================================================
// Constants
// ============================================================

export const EMERGENCY_ESCALATION_MINUTES = 60;

// ============================================================
// MaintenanceRequest Entity
// ============================================================

export interface MaintenanceRequest {
  readonly id: MaintenanceRequestId;
  readonly propertyId: PropertyId;
  readonly tenantId: TenantId;
  readonly description: string;
  readonly priority: MaintenancePriority;
  readonly status: MaintenanceStatus;
  readonly photos?: string[];
  readonly assignedTo?: string;
  readonly assignedAt?: Date;
  readonly completedAt?: Date;
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

// ============================================================
// Input DTO (BP-CODE-001)
// ============================================================

export interface CreateMaintenanceRequestInput {
  propertyId: PropertyId;
  tenantId: TenantId;
  description: string;
  priority: MaintenancePriority;
  photos?: string[];
}

// ============================================================
// Factory Function
// ============================================================

export function createMaintenanceRequest(
  input: CreateMaintenanceRequestInput,
  date: Date = new Date()
): Result<MaintenanceRequest, ValidationError> {
  // Validate description
  const trimmedDescription = input.description.trim();
  if (!trimmedDescription) {
    return err(new ValidationError('Maintenance description is required'));
  }

  const now = new Date();
  const request: MaintenanceRequest = {
    id: generateMaintenanceRequestId(date),
    propertyId: input.propertyId,
    tenantId: input.tenantId,
    description: trimmedDescription,
    priority: input.priority,
    status: 'submitted',
    photos: input.photos,
    createdAt: now,
    updatedAt: now,
  };

  return ok(request);
}

// ============================================================
// Status Transition Functions (BP-DESIGN-001)
// ============================================================

export function canTransitionMaintenanceStatus(
  currentStatus: MaintenanceStatus,
  targetStatus: MaintenanceStatus
): boolean {
  const validTransitions = validMaintenanceStatusTransitions[currentStatus];
  return validTransitions.includes(targetStatus);
}

export function transitionMaintenanceStatus(
  request: MaintenanceRequest,
  targetStatus: MaintenanceStatus,
  assignee?: string
): Result<MaintenanceRequest, InvalidStatusTransitionError> {
  if (!canTransitionMaintenanceStatus(request.status, targetStatus)) {
    return err(
      new InvalidStatusTransitionError('MaintenanceRequest', request.status, targetStatus)
    );
  }

  const now = new Date();
  let updatedRequest: MaintenanceRequest = {
    ...request,
    status: targetStatus,
    updatedAt: now,
  };

  // Handle assignment
  if (targetStatus === 'assigned' && assignee) {
    updatedRequest = {
      ...updatedRequest,
      assignedTo: assignee,
      assignedAt: now,
    };
  }

  // Handle completion
  if (targetStatus === 'completed') {
    updatedRequest = {
      ...updatedRequest,
      completedAt: now,
    };
  }

  return ok(updatedRequest);
}

// ============================================================
// Emergency Escalation (REQ-RENTAL-001-F042)
// ============================================================

export function isEmergencyEscalationNeeded(
  request: MaintenanceRequest,
  checkTime: Date = new Date()
): boolean {
  // Only check emergency priority requests
  if (request.priority !== 'emergency') {
    return false;
  }

  // Only check unassigned requests (submitted status)
  if (request.status !== 'submitted') {
    return false;
  }

  // Check if more than EMERGENCY_ESCALATION_MINUTES have passed
  const minutesSinceCreation = 
    (checkTime.getTime() - request.createdAt.getTime()) / (1000 * 60);

  return minutesSinceCreation > EMERGENCY_ESCALATION_MINUTES;
}

// ============================================================
// Query Helpers
// ============================================================

export function isOpenRequest(request: MaintenanceRequest): boolean {
  return !['completed', 'cancelled'].includes(request.status);
}

export function isPendingAssignment(request: MaintenanceRequest): boolean {
  return request.status === 'submitted';
}

export function isInProgress(request: MaintenanceRequest): boolean {
  return request.status === 'in-progress';
}

// ============================================================
// Escalation Report
// ============================================================

export interface EscalationReport {
  escalatedRequests: MaintenanceRequest[];
  generatedAt: Date;
  totalCount: number;
}

export function generateEscalationReport(
  requests: MaintenanceRequest[]
): EscalationReport {
  const escalatedRequests = requests.filter(req => isEmergencyEscalationNeeded(req));

  return {
    escalatedRequests,
    generatedAt: new Date(),
    totalCount: escalatedRequests.length,
  };
}
