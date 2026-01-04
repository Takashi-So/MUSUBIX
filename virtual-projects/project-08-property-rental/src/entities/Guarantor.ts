/**
 * Guarantor Entity
 * TSK-007: Guarantor Entity
 * 
 * @see REQ-RENTAL-001 F013
 * @see DES-RENTAL-001 §4.1.3
 */

import type {
  Guarantor,
  GuarantorId,
  PersonName,
  ContactInfo,
  Identification,
  EmploymentInfo,
  RelationshipType,
} from '../types/index.js';
import { 
  validatePersonName, 
  validateContactInfo 
} from './PropertyOwner.js';
import { 
  validateIdentification, 
  validateEmploymentInfo 
} from './Tenant.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let guarantorCounter = 0;

/**
 * Guarantor ID生成
 * Format: GUA-YYYYMMDD-NNN
 */
export function generateGuarantorId(): GuarantorId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  guarantorCounter++;
  const seq = String(guarantorCounter).padStart(3, '0');
  return `GUA-${dateStr}-${seq}` as GuarantorId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetGuarantorCounter(): void {
  guarantorCounter = 0;
}

/**
 * Guarantor作成入力
 */
export interface CreateGuarantorInput {
  name: PersonName;
  contact: ContactInfo;
  relationship: RelationshipType;
  employment?: EmploymentInfo;
  identification?: Identification;
}

/**
 * Guarantorエンティティを作成
 * @see REQ-RENTAL-001 F013
 */
export function createGuarantor(input: CreateGuarantorInput): Guarantor {
  validatePersonName(input.name);
  validateContactInfo(input.contact);
  
  if (!input.relationship) {
    throw new Error('Relationship type is required');
  }
  
  if (input.employment) {
    validateEmploymentInfo(input.employment);
  }
  
  if (input.identification) {
    validateIdentification(input.identification);
  }
  
  const now = new Date();
  
  return {
    id: generateGuarantorId(),
    name: { ...input.name },
    contact: { ...input.contact },
    relationship: input.relationship,
    employment: input.employment ? { ...input.employment } : undefined,
    identification: input.identification ? { ...input.identification } : undefined,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * Guarantor情報を更新
 */
export function updateGuarantor(
  guarantor: Guarantor,
  updates: Partial<Omit<CreateGuarantorInput, 'relationship'>>
): Guarantor {
  if (updates.name) {
    validatePersonName(updates.name);
  }
  if (updates.contact) {
    validateContactInfo(updates.contact);
  }
  if (updates.employment) {
    validateEmploymentInfo(updates.employment);
  }
  if (updates.identification) {
    validateIdentification(updates.identification);
  }
  
  return {
    ...guarantor,
    name: updates.name ? { ...updates.name } : guarantor.name,
    contact: updates.contact ? { ...updates.contact } : guarantor.contact,
    employment: updates.employment 
      ? { ...updates.employment } 
      : guarantor.employment,
    identification: updates.identification 
      ? { ...updates.identification } 
      : guarantor.identification,
    updatedAt: new Date(),
  };
}

/**
 * 保証会社かどうかをチェック
 */
export function isGuarantorCompany(guarantor: Guarantor): boolean {
  return guarantor.relationship === 'guarantor_company';
}

/**
 * 保証人の収入審査（契約者と同等以上の収入があるか）
 */
export function checkGuarantorEligibility(
  guarantor: Guarantor,
  tenantAnnualIncome: number
): { eligible: boolean; reason?: string } {
  // 保証会社の場合は常に eligible
  if (isGuarantorCompany(guarantor)) {
    return { eligible: true };
  }
  
  // 個人保証人の場合は収入チェック
  if (!guarantor.employment) {
    return { 
      eligible: false, 
      reason: 'Employment information is required for individual guarantors' 
    };
  }
  
  const guarantorIncome = guarantor.employment.annualIncome.amount;
  
  if (guarantorIncome < tenantAnnualIncome) {
    return {
      eligible: false,
      reason: `Guarantor income (${guarantorIncome}) is less than tenant income (${tenantAnnualIncome})`,
    };
  }
  
  return { eligible: true };
}
