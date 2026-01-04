/**
 * MaintenanceRequest Entity
 * TSK-010: MaintenanceRequest Entity
 * 
 * @see REQ-RENTAL-001 F060-F062
 * @see DES-RENTAL-001 §4.1.6
 */

import type {
  MaintenanceRequest,
  MaintenanceRequestId,
  PropertyId,
  TenantId,
  Money,
  UrgencyLevel,
  MaintenanceStatus,
  SubmitMaintenanceInput,
} from '../types/index.js';
import { createMoney } from './Property.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let maintenanceCounter = 0;

/**
 * MaintenanceRequest ID生成
 * Format: MNT-YYYYMMDD-NNN
 */
export function generateMaintenanceId(): MaintenanceRequestId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  maintenanceCounter++;
  const seq = String(maintenanceCounter).padStart(3, '0');
  return `MNT-${dateStr}-${seq}` as MaintenanceRequestId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetMaintenanceCounter(): void {
  maintenanceCounter = 0;
}

/**
 * MaintenanceRequestエンティティを作成
 * @see REQ-RENTAL-001 F060
 */
export function createMaintenanceRequest(
  input: SubmitMaintenanceInput
): MaintenanceRequest {
  if (!input.title || input.title.trim().length === 0) {
    throw new Error('Title is required');
  }
  if (!input.description || input.description.trim().length === 0) {
    throw new Error('Description is required');
  }
  
  const now = new Date();
  
  return {
    id: generateMaintenanceId(),
    propertyId: input.propertyId,
    tenantId: input.tenantId,
    title: input.title.trim(),
    description: input.description.trim(),
    urgency: input.urgency,
    status: 'submitted',
    assignedTo: undefined,
    scheduledDate: undefined,
    completedDate: undefined,
    cost: undefined,
    photos: input.photos ? [...input.photos] : [],
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * 有効なステータス遷移マップ
 */
const validMaintenanceStatusTransitions: Record<MaintenanceStatus, MaintenanceStatus[]> = {
  submitted: ['assigned', 'cancelled'],
  assigned: ['in_progress', 'cancelled'],
  in_progress: ['completed', 'cancelled'],
  completed: [],    // 完了は変更不可
  cancelled: [],    // キャンセル済みは変更不可
};

/**
 * MaintenanceRequestステータスを更新
 */
export function updateMaintenanceStatus(
  request: MaintenanceRequest,
  newStatus: MaintenanceStatus
): MaintenanceRequest {
  const allowedTransitions = validMaintenanceStatusTransitions[request.status];
  
  if (!allowedTransitions.includes(newStatus)) {
    throw new Error(
      `Invalid status transition: ${request.status} -> ${newStatus}. ` +
      `Allowed: ${allowedTransitions.join(', ') || 'none'}`
    );
  }
  
  return {
    ...request,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * 担当者を割り当て
 * @see REQ-RENTAL-001 F061
 */
export function assignStaff(
  request: MaintenanceRequest,
  staffId: string,
  scheduledDate?: Date
): MaintenanceRequest {
  if (request.status !== 'submitted') {
    throw new Error('Can only assign staff to submitted requests');
  }
  
  if (!staffId || staffId.trim().length === 0) {
    throw new Error('Staff ID is required');
  }
  
  return {
    ...request,
    assignedTo: staffId.trim(),
    scheduledDate: scheduledDate ? new Date(scheduledDate) : undefined,
    status: 'assigned',
    updatedAt: new Date(),
  };
}

/**
 * 作業を開始
 */
export function startWork(request: MaintenanceRequest): MaintenanceRequest {
  if (request.status !== 'assigned') {
    throw new Error('Can only start work on assigned requests');
  }
  
  return updateMaintenanceStatus(request, 'in_progress');
}

/**
 * メンテナンスを完了
 * @see REQ-RENTAL-001 F062
 */
export function completeMaintenanceRequest(
  request: MaintenanceRequest,
  cost?: number
): MaintenanceRequest {
  if (request.status !== 'in_progress') {
    throw new Error('Can only complete in-progress requests');
  }
  
  const now = new Date();
  
  return {
    ...request,
    status: 'completed',
    completedDate: now,
    cost: cost !== undefined ? createMoney(cost) : undefined,
    updatedAt: now,
  };
}

/**
 * メンテナンスをキャンセル
 */
export function cancelMaintenanceRequest(
  request: MaintenanceRequest
): MaintenanceRequest {
  if (request.status === 'completed' || request.status === 'cancelled') {
    throw new Error('Cannot cancel completed or already cancelled requests');
  }
  
  return updateMaintenanceStatus(request, 'cancelled');
}

/**
 * リクエスト情報を更新
 */
export function updateMaintenanceRequest(
  request: MaintenanceRequest,
  updates: {
    title?: string;
    description?: string;
    urgency?: UrgencyLevel;
    photos?: string[];
  }
): MaintenanceRequest {
  if (request.status === 'completed' || request.status === 'cancelled') {
    throw new Error('Cannot update completed or cancelled requests');
  }
  
  if (updates.title !== undefined && updates.title.trim().length === 0) {
    throw new Error('Title cannot be empty');
  }
  
  return {
    ...request,
    title: updates.title !== undefined ? updates.title.trim() : request.title,
    description: updates.description !== undefined 
      ? updates.description.trim() 
      : request.description,
    urgency: updates.urgency ?? request.urgency,
    photos: updates.photos ? [...updates.photos] : request.photos,
    updatedAt: new Date(),
  };
}

/**
 * 緊急度を更新（エスカレーション）
 */
export function escalateUrgency(
  request: MaintenanceRequest,
  newUrgency: UrgencyLevel
): MaintenanceRequest {
  const urgencyOrder: UrgencyLevel[] = ['low', 'medium', 'high', 'emergency'];
  const currentIndex = urgencyOrder.indexOf(request.urgency);
  const newIndex = urgencyOrder.indexOf(newUrgency);
  
  if (newIndex <= currentIndex) {
    throw new Error('Can only escalate to higher urgency level');
  }
  
  return {
    ...request,
    urgency: newUrgency,
    updatedAt: new Date(),
  };
}

/**
 * 緊急度に基づく対応期限を計算
 */
export function getResponseDeadline(
  request: MaintenanceRequest
): Date {
  const deadlines: Record<UrgencyLevel, number> = {
    low: 7,        // 7日
    medium: 3,     // 3日
    high: 1,       // 1日
    emergency: 0,  // 即日
  };
  
  const days = deadlines[request.urgency];
  const deadline = new Date(request.createdAt);
  deadline.setDate(deadline.getDate() + days);
  
  return deadline;
}

/**
 * 対応期限を過ぎているかチェック
 */
export function isOverdue(request: MaintenanceRequest): boolean {
  if (request.status === 'completed' || request.status === 'cancelled') {
    return false;
  }
  
  const deadline = getResponseDeadline(request);
  return new Date() > deadline;
}

/**
 * 解決までの日数を計算
 */
export function getResolutionDays(request: MaintenanceRequest): number | null {
  if (request.status !== 'completed' || !request.completedDate) {
    return null;
  }
  
  const days = Math.floor(
    (request.completedDate.getTime() - request.createdAt.getTime()) / 
    (24 * 60 * 60 * 1000)
  );
  
  return Math.max(0, days);
}
