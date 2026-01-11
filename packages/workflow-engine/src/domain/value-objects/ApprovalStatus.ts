/**
 * ApprovalStatus Value Object
 * 
 * Represents the approval status for phase transitions
 * 
 * @see REQ-ORCH-003 - Quality Gate Integration
 * @see DES-ORCH-003 - QualityGateRunner
 */

/**
 * Approval status type
 */
export type ApprovalStatus = 'pending' | 'approved' | 'rejected';

/**
 * Approval keywords that indicate user approval
 */
export const APPROVAL_KEYWORDS: readonly string[] = [
  '承認',
  'approve',
  'approved',
  'LGTM',
  '進める',
  'OK',
  'ok',
  'Yes',
  'yes',
  '実装',
  'proceed',
];

/**
 * Rejection keywords
 */
export const REJECTION_KEYWORDS: readonly string[] = [
  '修正',
  'reject',
  'rejected',
  'no',
  'No',
  'やり直し',
  'fix',
];

/**
 * Approval entity
 */
export interface Approval {
  readonly id: string;
  readonly status: ApprovalStatus;
  readonly approver: string;
  readonly comment?: string;
  readonly timestamp: Date;
}

/**
 * Create an approval
 * 
 * @param id - Approval ID
 * @param status - Approval status
 * @param approver - Approver identifier
 * @param comment - Optional comment
 * @returns Approval entity
 */
export function createApproval(
  id: string,
  status: ApprovalStatus,
  approver: string,
  comment?: string
): Approval {
  return Object.freeze({
    id,
    status,
    approver,
    comment,
    timestamp: new Date(),
  });
}

/**
 * Parse user input for approval status
 * 
 * @param input - User input text
 * @returns Detected approval status
 */
export function parseApprovalFromInput(input: string): ApprovalStatus {
  const normalized = input.trim().toLowerCase();

  // Check for rejection first (修正 could be in a longer sentence)
  for (const keyword of REJECTION_KEYWORDS) {
    if (normalized.includes(keyword.toLowerCase())) {
      return 'rejected';
    }
  }

  // Check for approval
  for (const keyword of APPROVAL_KEYWORDS) {
    if (normalized.includes(keyword.toLowerCase())) {
      return 'approved';
    }
  }

  return 'pending';
}

/**
 * Check if approval is granted
 * 
 * @param approval - Approval to check
 * @returns true if approved
 */
export function isApproved(approval: Approval): boolean {
  return approval.status === 'approved';
}

/**
 * Check if approval is rejected
 * 
 * @param approval - Approval to check
 * @returns true if rejected
 */
export function isRejected(approval: Approval): boolean {
  return approval.status === 'rejected';
}

/**
 * Generate approval ID
 * 
 * @param phaseType - Phase type
 * @returns Approval ID
 */
export function generateApprovalId(phaseType: string): string {
  const timestamp = Date.now().toString(36);
  return `APR-${phaseType.toUpperCase()}-${timestamp}`;
}
