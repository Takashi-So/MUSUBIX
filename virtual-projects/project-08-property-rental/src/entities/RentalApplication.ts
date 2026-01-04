/**
 * RentalApplication Entity
 * TSK-011: RentalApplication Entity
 * 
 * @see REQ-RENTAL-001 F021
 * @see DES-RENTAL-001 §4.1.7
 */

import type {
  RentalApplication,
  RentalApplicationId,
  PropertyId,
  TenantId,
  ApplicationStatus,
  SubmitApplicationInput,
} from '../types/index.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let applicationCounter = 0;

/**
 * RentalApplication ID生成
 * Format: APP-YYYYMMDD-NNN
 */
export function generateApplicationId(): RentalApplicationId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  applicationCounter++;
  const seq = String(applicationCounter).padStart(3, '0');
  return `APP-${dateStr}-${seq}` as RentalApplicationId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetApplicationCounter(): void {
  applicationCounter = 0;
}

/**
 * RentalApplicationエンティティを作成
 * @see REQ-RENTAL-001 F021
 */
export function createRentalApplication(
  input: SubmitApplicationInput
): RentalApplication {
  if (!input.desiredMoveInDate) {
    throw new Error('Desired move-in date is required');
  }
  
  const moveInDate = new Date(input.desiredMoveInDate);
  const now = new Date();
  
  // 入居希望日は今日以降
  if (moveInDate < now) {
    throw new Error('Desired move-in date must be in the future');
  }
  
  return {
    id: generateApplicationId(),
    propertyId: input.propertyId,
    tenantId: input.tenantId,
    desiredMoveInDate: moveInDate,
    status: 'submitted',
    screeningNotes: undefined,
    rejectionReason: undefined,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * 有効なステータス遷移マップ
 */
const validApplicationStatusTransitions: Record<ApplicationStatus, ApplicationStatus[]> = {
  submitted: ['screening', 'withdrawn'],
  screening: ['approved', 'rejected'],
  approved: [],      // 承認済みは変更不可
  rejected: [],      // 却下済みは変更不可
  withdrawn: [],     // 取り下げ済みは変更不可
};

/**
 * RentalApplicationステータスを更新
 */
export function updateApplicationStatus(
  application: RentalApplication,
  newStatus: ApplicationStatus
): RentalApplication {
  const allowedTransitions = validApplicationStatusTransitions[application.status];
  
  if (!allowedTransitions.includes(newStatus)) {
    throw new Error(
      `Invalid status transition: ${application.status} -> ${newStatus}. ` +
      `Allowed: ${allowedTransitions.join(', ') || 'none'}`
    );
  }
  
  return {
    ...application,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * 審査を開始
 * @see REQ-RENTAL-001 F021
 */
export function startScreening(
  application: RentalApplication
): RentalApplication {
  if (application.status !== 'submitted') {
    throw new Error('Can only start screening on submitted applications');
  }
  
  return updateApplicationStatus(application, 'screening');
}

/**
 * 審査メモを追加
 */
export function addScreeningNotes(
  application: RentalApplication,
  notes: string
): RentalApplication {
  if (application.status !== 'screening') {
    throw new Error('Can only add notes during screening');
  }
  
  const existingNotes = application.screeningNotes || '';
  const timestamp = new Date().toISOString();
  const newNotes = existingNotes 
    ? `${existingNotes}\n[${timestamp}] ${notes}`
    : `[${timestamp}] ${notes}`;
  
  return {
    ...application,
    screeningNotes: newNotes,
    updatedAt: new Date(),
  };
}

/**
 * 申込を承認
 * @see REQ-RENTAL-001 F021
 */
export function approveApplication(
  application: RentalApplication
): RentalApplication {
  if (application.status !== 'screening') {
    throw new Error('Can only approve applications in screening');
  }
  
  return updateApplicationStatus(application, 'approved');
}

/**
 * 申込を却下
 * @see REQ-RENTAL-001 F021
 */
export function rejectApplication(
  application: RentalApplication,
  reason: string
): RentalApplication {
  if (application.status !== 'screening') {
    throw new Error('Can only reject applications in screening');
  }
  
  if (!reason || reason.trim().length === 0) {
    throw new Error('Rejection reason is required');
  }
  
  return {
    ...application,
    status: 'rejected',
    rejectionReason: reason.trim(),
    updatedAt: new Date(),
  };
}

/**
 * 申込を取り下げ
 */
export function withdrawApplication(
  application: RentalApplication
): RentalApplication {
  if (application.status === 'approved' || 
      application.status === 'rejected' ||
      application.status === 'withdrawn') {
    throw new Error('Cannot withdraw application in current status');
  }
  
  return updateApplicationStatus(application, 'withdrawn');
}

/**
 * 入居希望日を更新
 */
export function updateDesiredMoveInDate(
  application: RentalApplication,
  newDate: Date
): RentalApplication {
  if (application.status !== 'submitted') {
    throw new Error('Can only update move-in date for submitted applications');
  }
  
  const now = new Date();
  if (newDate < now) {
    throw new Error('Desired move-in date must be in the future');
  }
  
  return {
    ...application,
    desiredMoveInDate: new Date(newDate),
    updatedAt: new Date(),
  };
}

/**
 * 申込が処理済みかチェック
 */
export function isApplicationProcessed(application: RentalApplication): boolean {
  return ['approved', 'rejected', 'withdrawn'].includes(application.status);
}

/**
 * 申込が承認済みかチェック
 */
export function isApplicationApproved(application: RentalApplication): boolean {
  return application.status === 'approved';
}

/**
 * 申込から契約開始までの日数を計算
 */
export function getDaysUntilMoveIn(application: RentalApplication): number {
  const now = new Date();
  const moveIn = application.desiredMoveInDate;
  
  const days = Math.floor(
    (moveIn.getTime() - now.getTime()) / (24 * 60 * 60 * 1000)
  );
  
  return days;
}

/**
 * 審査期間を計算（日数）
 */
export function getScreeningDuration(application: RentalApplication): number | null {
  if (application.status === 'submitted') {
    return null; // まだ審査中
  }
  
  const startDate = application.createdAt;
  const endDate = application.updatedAt;
  
  const days = Math.floor(
    (endDate.getTime() - startDate.getTime()) / (24 * 60 * 60 * 1000)
  );
  
  return Math.max(0, days);
}
