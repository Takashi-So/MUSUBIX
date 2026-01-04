/**
 * PropertyOwner Entity
 * TSK-005: PropertyOwner Entity
 * 
 * @see DES-RENTAL-001 §4.1.8
 */

import type {
  PropertyOwner,
  OwnerId,
  PropertyId,
  PersonName,
  ContactInfo,
  BankAccount,
  OwnerType,
  OwnerStatus,
} from '../types/index.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let ownerCounter = 0;

/**
 * Owner ID生成
 * Format: OWN-YYYYMMDD-NNN
 */
export function generateOwnerId(): OwnerId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  ownerCounter++;
  const seq = String(ownerCounter).padStart(3, '0');
  return `OWN-${dateStr}-${seq}` as OwnerId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetOwnerCounter(): void {
  ownerCounter = 0;
}

/**
 * PersonNameを検証
 */
export function validatePersonName(name: PersonName): void {
  if (!name.firstName || !name.lastName) {
    throw new Error('First name and last name are required');
  }
  if (!name.firstNameKana || !name.lastNameKana) {
    throw new Error('Furigana (kana) is required for name');
  }
  // カタカナチェック
  const kanaRegex = /^[\u30A0-\u30FF]+$/;
  if (!kanaRegex.test(name.firstNameKana) || !kanaRegex.test(name.lastNameKana)) {
    throw new Error('Furigana must be in katakana');
  }
}

/**
 * ContactInfoを検証
 */
export function validateContactInfo(contact: ContactInfo): void {
  if (!contact.phone) {
    throw new Error('Phone number is required');
  }
  // 電話番号形式チェック（日本の電話番号）
  const phoneRegex = /^0\d{1,4}-?\d{1,4}-?\d{4}$/;
  if (!phoneRegex.test(contact.phone.replace(/-/g, ''))) {
    throw new Error('Invalid phone number format');
  }
  
  if (!contact.email) {
    throw new Error('Email is required');
  }
  // メールアドレス形式チェック
  const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
  if (!emailRegex.test(contact.email)) {
    throw new Error('Invalid email format');
  }
}

/**
 * BankAccountを検証
 */
export function validateBankAccount(account: BankAccount): void {
  if (!account.bankName) {
    throw new Error('Bank name is required');
  }
  if (!account.branchName) {
    throw new Error('Branch name is required');
  }
  if (!account.accountNumber) {
    throw new Error('Account number is required');
  }
  if (!account.accountHolder) {
    throw new Error('Account holder name is required');
  }
}

/**
 * PropertyOwner作成入力
 */
export interface CreatePropertyOwnerInput {
  name: PersonName;
  ownerType: OwnerType;
  contact: ContactInfo;
  bankAccount?: BankAccount;
  taxId?: string;
}

/**
 * PropertyOwnerエンティティを作成
 */
export function createPropertyOwner(input: CreatePropertyOwnerInput): PropertyOwner {
  validatePersonName(input.name);
  validateContactInfo(input.contact);
  
  if (input.bankAccount) {
    validateBankAccount(input.bankAccount);
  }
  
  const now = new Date();
  
  return {
    id: generateOwnerId(),
    name: { ...input.name },
    ownerType: input.ownerType,
    contact: { ...input.contact },
    bankAccount: input.bankAccount ? { ...input.bankAccount } : undefined,
    taxId: input.taxId,  // Already encrypted by caller
    properties: [],
    status: 'active',
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * PropertyOwner情報を更新
 */
export function updatePropertyOwner(
  owner: PropertyOwner,
  updates: Partial<Omit<CreatePropertyOwnerInput, 'ownerType'>>
): PropertyOwner {
  if (updates.name) {
    validatePersonName(updates.name);
  }
  if (updates.contact) {
    validateContactInfo(updates.contact);
  }
  if (updates.bankAccount) {
    validateBankAccount(updates.bankAccount);
  }
  
  return {
    ...owner,
    name: updates.name ? { ...updates.name } : owner.name,
    contact: updates.contact ? { ...updates.contact } : owner.contact,
    bankAccount: updates.bankAccount ? { ...updates.bankAccount } : owner.bankAccount,
    taxId: updates.taxId ?? owner.taxId,
    updatedAt: new Date(),
  };
}

/**
 * PropertyOwnerに物件を追加
 */
export function addPropertyToOwner(
  owner: PropertyOwner,
  propertyId: PropertyId
): PropertyOwner {
  if (owner.properties.includes(propertyId)) {
    throw new Error(`Property ${propertyId} already belongs to this owner`);
  }
  
  return {
    ...owner,
    properties: [...owner.properties, propertyId],
    updatedAt: new Date(),
  };
}

/**
 * PropertyOwnerから物件を削除
 */
export function removePropertyFromOwner(
  owner: PropertyOwner,
  propertyId: PropertyId
): PropertyOwner {
  if (!owner.properties.includes(propertyId)) {
    throw new Error(`Property ${propertyId} does not belong to this owner`);
  }
  
  return {
    ...owner,
    properties: owner.properties.filter(id => id !== propertyId),
    updatedAt: new Date(),
  };
}

/**
 * PropertyOwnerステータスを更新
 */
export function updateOwnerStatus(
  owner: PropertyOwner,
  newStatus: OwnerStatus
): PropertyOwner {
  if (newStatus === 'inactive' && owner.properties.length > 0) {
    throw new Error('Cannot deactivate owner with active properties');
  }
  
  return {
    ...owner,
    status: newStatus,
    updatedAt: new Date(),
  };
}
