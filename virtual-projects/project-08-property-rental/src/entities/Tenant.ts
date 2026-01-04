/**
 * Tenant Entity
 * TSK-006: Tenant Entity
 * 
 * @see REQ-RENTAL-001 F020-F023
 * @see DES-RENTAL-001 §4.1.2
 */

import type {
  Tenant,
  TenantId,
  GuarantorId,
  PersonName,
  ContactInfo,
  Identification,
  EmploymentInfo,
  EmergencyContact,
  TenantStatus,
  CreateTenantInput,
} from '../types/index.js';
import { validatePersonName, validateContactInfo } from './PropertyOwner.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let tenantCounter = 0;

/**
 * Tenant ID生成
 * Format: TEN-YYYYMMDD-NNN
 */
export function generateTenantId(): TenantId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  tenantCounter++;
  const seq = String(tenantCounter).padStart(3, '0');
  return `TEN-${dateStr}-${seq}` as TenantId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetTenantCounter(): void {
  tenantCounter = 0;
}

/**
 * Identificationを検証
 */
export function validateIdentification(id: Identification): void {
  if (!id.type) {
    throw new Error('Identification type is required');
  }
  if (!id.number) {
    throw new Error('Identification number is required');
  }
  if (!id.issuedDate) {
    throw new Error('Issue date is required');
  }
  if (id.expiryDate && id.expiryDate < new Date()) {
    throw new Error('Identification has expired');
  }
}

/**
 * EmploymentInfoを検証
 */
export function validateEmploymentInfo(employment: EmploymentInfo): void {
  if (!employment.companyName) {
    throw new Error('Company name is required');
  }
  if (!employment.position) {
    throw new Error('Position is required');
  }
  if (!employment.annualIncome || employment.annualIncome.amount < 0) {
    throw new Error('Valid annual income is required');
  }
  if (!employment.employmentType) {
    throw new Error('Employment type is required');
  }
  if (employment.yearsEmployed < 0) {
    throw new Error('Years employed cannot be negative');
  }
}

/**
 * EmergencyContactを検証
 */
export function validateEmergencyContact(contact: EmergencyContact): void {
  validatePersonName(contact.name);
  if (!contact.relationship) {
    throw new Error('Relationship is required for emergency contact');
  }
  if (!contact.phone) {
    throw new Error('Phone is required for emergency contact');
  }
}

/**
 * Tenantエンティティを作成
 * @see REQ-RENTAL-001 F020
 */
export function createTenant(input: CreateTenantInput): Tenant {
  validatePersonName(input.name);
  validateContactInfo(input.contact);
  validateIdentification(input.identification);
  validateEmploymentInfo(input.employment);
  validateEmergencyContact(input.emergencyContact);
  
  const now = new Date();
  
  return {
    id: generateTenantId(),
    name: { ...input.name },
    contact: { ...input.contact },
    identification: { ...input.identification },
    employment: { ...input.employment },
    emergencyContact: { ...input.emergencyContact },
    guarantorId: undefined,
    status: 'prospective',
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * Tenant情報を更新
 * @see REQ-RENTAL-001 F022
 */
export function updateTenant(
  tenant: Tenant,
  updates: Partial<CreateTenantInput>
): Tenant {
  if (updates.name) {
    validatePersonName(updates.name);
  }
  if (updates.contact) {
    validateContactInfo(updates.contact);
  }
  if (updates.identification) {
    validateIdentification(updates.identification);
  }
  if (updates.employment) {
    validateEmploymentInfo(updates.employment);
  }
  if (updates.emergencyContact) {
    validateEmergencyContact(updates.emergencyContact);
  }
  
  return {
    ...tenant,
    name: updates.name ? { ...updates.name } : tenant.name,
    contact: updates.contact ? { ...updates.contact } : tenant.contact,
    identification: updates.identification 
      ? { ...updates.identification } 
      : tenant.identification,
    employment: updates.employment 
      ? { ...updates.employment } 
      : tenant.employment,
    emergencyContact: updates.emergencyContact 
      ? { ...updates.emergencyContact } 
      : tenant.emergencyContact,
    updatedAt: new Date(),
  };
}

/**
 * Tenantに保証人を設定
 * @see REQ-RENTAL-001 F023
 */
export function assignGuarantor(
  tenant: Tenant,
  guarantorId: GuarantorId
): Tenant {
  return {
    ...tenant,
    guarantorId,
    updatedAt: new Date(),
  };
}

/**
 * 有効なステータス遷移マップ
 */
const validTenantStatusTransitions: Record<TenantStatus, TenantStatus[]> = {
  prospective: ['active', 'former'],  // 申込中 → 入居 or 却下
  active: ['former'],                  // 入居中 → 退去
  former: [],                          // 退去済みは変更不可
};

/**
 * Tenantステータスを更新
 * @see REQ-RENTAL-001 F021
 */
export function updateTenantStatus(
  tenant: Tenant,
  newStatus: TenantStatus
): Tenant {
  const allowedTransitions = validTenantStatusTransitions[tenant.status];
  
  if (!allowedTransitions.includes(newStatus)) {
    throw new Error(
      `Invalid status transition: ${tenant.status} -> ${newStatus}. ` +
      `Allowed: ${allowedTransitions.join(', ') || 'none'}`
    );
  }
  
  return {
    ...tenant,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * Tenantを非アクティブ化（退去処理）
 */
export function deactivateTenant(tenant: Tenant): Tenant {
  if (tenant.status === 'former') {
    throw new Error('Tenant is already deactivated');
  }
  
  return updateTenantStatus(tenant, 'former');
}

/**
 * 収入審査（年収が家賃の36倍以上か）
 * @see REQ-RENTAL-001 F021
 */
export function checkIncomeEligibility(
  tenant: Tenant,
  monthlyRent: number
): { eligible: boolean; ratio: number; requiredRatio: number } {
  const annualIncome = tenant.employment.annualIncome.amount;
  const requiredAnnualIncome = monthlyRent * 36;  // 家賃の36倍
  const ratio = annualIncome / monthlyRent;
  
  return {
    eligible: annualIncome >= requiredAnnualIncome,
    ratio,
    requiredRatio: 36,
  };
}
