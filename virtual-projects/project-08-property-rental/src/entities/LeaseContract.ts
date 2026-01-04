/**
 * LeaseContract Entity
 * TSK-008: LeaseContract Entity
 * 
 * @see REQ-RENTAL-001 F030-F032
 * @see DES-RENTAL-001 §4.1.4
 */

import type {
  LeaseContract,
  LeaseContractId,
  PropertyId,
  TenantId,
  GuarantorId,
  Money,
  ContractStatus,
  CreateContractInput,
} from '../types/index.js';
import { createMoney } from './Property.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let contractCounter = 0;

/**
 * LeaseContract ID生成
 * Format: LEASE-YYYYMMDD-NNN
 */
export function generateContractId(): LeaseContractId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  contractCounter++;
  const seq = String(contractCounter).padStart(3, '0');
  return `LEASE-${dateStr}-${seq}` as LeaseContractId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetContractCounter(): void {
  contractCounter = 0;
}

/**
 * 契約期間を検証
 */
export function validateContractPeriod(startDate: Date, endDate: Date): void {
  if (endDate <= startDate) {
    throw new Error('End date must be after start date');
  }
  
  // 最低契約期間: 1ヶ月
  const minDuration = 30 * 24 * 60 * 60 * 1000; // 30 days in ms
  if (endDate.getTime() - startDate.getTime() < minDuration) {
    throw new Error('Contract duration must be at least 1 month');
  }
  
  // 最大契約期間: 5年
  const maxDuration = 5 * 365 * 24 * 60 * 60 * 1000; // 5 years in ms
  if (endDate.getTime() - startDate.getTime() > maxDuration) {
    throw new Error('Contract duration cannot exceed 5 years');
  }
}

/**
 * 契約金額を検証
 */
export function validateContractAmounts(input: CreateContractInput): void {
  if (input.monthlyRent <= 0) {
    throw new Error('Monthly rent must be greater than 0');
  }
  if (input.deposit < 0) {
    throw new Error('Deposit cannot be negative');
  }
  if (input.keyMoney < 0) {
    throw new Error('Key money cannot be negative');
  }
  if (input.maintenanceFee < 0) {
    throw new Error('Maintenance fee cannot be negative');
  }
  if (input.renewalFee !== undefined && input.renewalFee < 0) {
    throw new Error('Renewal fee cannot be negative');
  }
}

/**
 * LeaseContractエンティティを作成
 * @see REQ-RENTAL-001 F030
 */
export function createLeaseContract(input: CreateContractInput): LeaseContract {
  validateContractPeriod(input.startDate, input.endDate);
  validateContractAmounts(input);
  
  const now = new Date();
  
  return {
    id: generateContractId(),
    propertyId: input.propertyId,
    tenantId: input.tenantId,
    guarantorId: input.guarantorId,
    startDate: new Date(input.startDate),
    endDate: new Date(input.endDate),
    monthlyRent: createMoney(input.monthlyRent),
    deposit: createMoney(input.deposit),
    keyMoney: createMoney(input.keyMoney),
    maintenanceFee: createMoney(input.maintenanceFee),
    renewalFee: input.renewalFee !== undefined 
      ? createMoney(input.renewalFee) 
      : undefined,
    status: 'draft',
    specialTerms: input.specialTerms,
    renewedFromId: undefined,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * 有効なステータス遷移マップ
 */
const validContractStatusTransitions: Record<ContractStatus, ContractStatus[]> = {
  draft: ['active'],                    // 下書き → 契約開始
  active: ['renewed', 'terminated', 'expired'],  // 契約中 → 更新/解約/期限切れ
  renewed: [],                          // 更新済みは変更不可
  terminated: [],                       // 解約済みは変更不可
  expired: ['renewed'],                 // 期限切れ → 更新
};

/**
 * 契約ステータスを更新
 */
export function updateContractStatus(
  contract: LeaseContract,
  newStatus: ContractStatus
): LeaseContract {
  const allowedTransitions = validContractStatusTransitions[contract.status];
  
  if (!allowedTransitions.includes(newStatus)) {
    throw new Error(
      `Invalid status transition: ${contract.status} -> ${newStatus}. ` +
      `Allowed: ${allowedTransitions.join(', ') || 'none'}`
    );
  }
  
  return {
    ...contract,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * 契約を有効化
 * @see REQ-RENTAL-001 F030
 */
export function activateContract(contract: LeaseContract): LeaseContract {
  if (contract.status !== 'draft') {
    throw new Error('Only draft contracts can be activated');
  }
  
  const now = new Date();
  if (contract.startDate > now) {
    throw new Error('Cannot activate contract before start date');
  }
  
  return updateContractStatus(contract, 'active');
}

/**
 * 契約を更新（新契約を作成）
 * @see REQ-RENTAL-001 F031
 */
export function renewContract(
  contract: LeaseContract,
  newEndDate: Date,
  newMonthlyRent?: number
): LeaseContract {
  if (contract.status !== 'active' && contract.status !== 'expired') {
    throw new Error('Only active or expired contracts can be renewed');
  }
  
  const newStartDate = contract.endDate;
  validateContractPeriod(newStartDate, newEndDate);
  
  const now = new Date();
  
  // 元契約を更新済みにマーク
  const renewedOriginal = updateContractStatus(contract, 'renewed');
  
  // 新契約を作成
  const newContract: LeaseContract = {
    id: generateContractId(),
    propertyId: contract.propertyId,
    tenantId: contract.tenantId,
    guarantorId: contract.guarantorId,
    startDate: newStartDate,
    endDate: newEndDate,
    monthlyRent: newMonthlyRent !== undefined 
      ? createMoney(newMonthlyRent) 
      : contract.monthlyRent,
    deposit: contract.deposit,
    keyMoney: createMoney(0),  // 更新時は礼金なし
    maintenanceFee: contract.maintenanceFee,
    renewalFee: contract.renewalFee,
    status: 'active',
    specialTerms: contract.specialTerms,
    renewedFromId: contract.id,
    createdAt: now,
    updatedAt: now,
  };
  
  return newContract;
}

/**
 * 契約を解約
 * @see REQ-RENTAL-001 F032
 */
export function terminateContract(
  contract: LeaseContract,
  terminationDate?: Date
): LeaseContract {
  if (contract.status !== 'active') {
    throw new Error('Only active contracts can be terminated');
  }
  
  const effectiveDate = terminationDate || new Date();
  
  return {
    ...contract,
    endDate: effectiveDate,
    status: 'terminated',
    updatedAt: new Date(),
  };
}

/**
 * 契約が期限切れかチェック
 */
export function isContractExpired(contract: LeaseContract): boolean {
  if (contract.status !== 'active') {
    return false;
  }
  return new Date() > contract.endDate;
}

/**
 * 契約更新期限が近いかチェック（90日以内）
 * @see REQ-RENTAL-001 F031
 */
export function isContractExpiringWithinDays(
  contract: LeaseContract,
  days: number = 90
): boolean {
  if (contract.status !== 'active') {
    return false;
  }
  
  const now = new Date();
  const daysUntilExpiry = Math.floor(
    (contract.endDate.getTime() - now.getTime()) / (24 * 60 * 60 * 1000)
  );
  
  return daysUntilExpiry >= 0 && daysUntilExpiry <= days;
}

/**
 * 契約期間（月数）を計算
 */
export function getContractDurationMonths(contract: LeaseContract): number {
  const start = contract.startDate;
  const end = contract.endDate;
  
  const months = (end.getFullYear() - start.getFullYear()) * 12 +
    (end.getMonth() - start.getMonth());
  
  return Math.max(1, months);
}

/**
 * 敷金返却額を計算（原状回復費用を差し引く）
 */
export function calculateDepositReturn(
  contract: LeaseContract,
  restorationCost: number
): Money {
  const depositAmount = contract.deposit.amount;
  const returnAmount = Math.max(0, depositAmount - restorationCost);
  
  return createMoney(returnAmount);
}
