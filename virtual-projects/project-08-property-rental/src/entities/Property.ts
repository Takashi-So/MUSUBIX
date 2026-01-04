/**
 * Property Entity
 * TSK-004: Property Entity
 * 
 * @see REQ-RENTAL-001 F010-F012
 * @see DES-RENTAL-001 §4.1.1
 */

import type {
  Property,
  PropertyId,
  OwnerId,
  Address,
  PropertyType,
  PropertyStatus,
  Money,
  CreatePropertyInput,
} from '../types/index.js';

/**
 * ID生成カウンター（インメモリ用）
 */
let propertyCounter = 0;

/**
 * Property ID生成
 * Format: PROP-YYYYMMDD-NNN
 */
export function generatePropertyId(): PropertyId {
  const now = new Date();
  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, '');
  propertyCounter++;
  const seq = String(propertyCounter).padStart(3, '0');
  return `PROP-${dateStr}-${seq}` as PropertyId;
}

/**
 * ID生成カウンターをリセット（テスト用）
 */
export function resetPropertyCounter(): void {
  propertyCounter = 0;
}

/**
 * Money value objectを作成
 */
export function createMoney(amount: number, currency: string = 'JPY'): Money {
  if (amount < 0) {
    throw new Error('Amount cannot be negative');
  }
  return { amount, currency };
}

/**
 * Addressを検証
 */
export function validateAddress(address: Address): void {
  if (!address.postalCode || !/^\d{3}-?\d{4}$/.test(address.postalCode)) {
    throw new Error('Invalid postal code format. Expected: xxx-xxxx or xxxxxxx');
  }
  if (!address.prefecture) {
    throw new Error('Prefecture is required');
  }
  if (!address.city) {
    throw new Error('City is required');
  }
  if (!address.street) {
    throw new Error('Street is required');
  }
}

/**
 * Property作成パラメータを検証
 */
export function validatePropertyInput(input: CreatePropertyInput): void {
  validateAddress(input.address);
  
  if (input.sizeSqm <= 0) {
    throw new Error('Size must be greater than 0');
  }
  if (input.monthlyRent < 0) {
    throw new Error('Monthly rent cannot be negative');
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
}

/**
 * Propertyエンティティを作成
 * @see REQ-RENTAL-001 F010
 */
export function createProperty(input: CreatePropertyInput): Property {
  validatePropertyInput(input);
  
  const now = new Date();
  
  return {
    id: generatePropertyId(),
    ownerId: input.ownerId,
    address: { ...input.address },
    propertyType: input.propertyType,
    sizeSqm: input.sizeSqm,
    monthlyRent: createMoney(input.monthlyRent),
    deposit: createMoney(input.deposit),
    keyMoney: createMoney(input.keyMoney),
    maintenanceFee: createMoney(input.maintenanceFee),
    amenities: input.amenities ? [...input.amenities] : [],
    status: 'available',
    photos: input.photos ? [...input.photos] : [],
    description: input.description,
    createdAt: now,
    updatedAt: now,
  };
}

/**
 * Property情報を更新
 * @see REQ-RENTAL-001 F011
 */
export function updateProperty(
  property: Property,
  updates: Partial<Omit<CreatePropertyInput, 'ownerId'>>
): Property {
  if (updates.address) {
    validateAddress(updates.address);
  }
  if (updates.sizeSqm !== undefined && updates.sizeSqm <= 0) {
    throw new Error('Size must be greater than 0');
  }
  if (updates.monthlyRent !== undefined && updates.monthlyRent < 0) {
    throw new Error('Monthly rent cannot be negative');
  }
  
  return {
    ...property,
    address: updates.address ? { ...updates.address } : property.address,
    propertyType: updates.propertyType ?? property.propertyType,
    sizeSqm: updates.sizeSqm ?? property.sizeSqm,
    monthlyRent: updates.monthlyRent !== undefined 
      ? createMoney(updates.monthlyRent) 
      : property.monthlyRent,
    deposit: updates.deposit !== undefined 
      ? createMoney(updates.deposit) 
      : property.deposit,
    keyMoney: updates.keyMoney !== undefined 
      ? createMoney(updates.keyMoney) 
      : property.keyMoney,
    maintenanceFee: updates.maintenanceFee !== undefined 
      ? createMoney(updates.maintenanceFee) 
      : property.maintenanceFee,
    amenities: updates.amenities ? [...updates.amenities] : property.amenities,
    photos: updates.photos ? [...updates.photos] : property.photos,
    description: updates.description ?? property.description,
    updatedAt: new Date(),
  };
}

/**
 * 有効なステータス遷移マップ
 */
const validStatusTransitions: Record<PropertyStatus, PropertyStatus[]> = {
  available: ['occupied', 'reserved', 'under_maintenance'],
  occupied: ['available', 'under_maintenance'],
  reserved: ['occupied', 'available'],
  under_maintenance: ['available'],
};

/**
 * Propertyステータスを更新
 * @see REQ-RENTAL-001 F012
 */
export function updatePropertyStatus(
  property: Property,
  newStatus: PropertyStatus
): Property {
  const allowedTransitions = validStatusTransitions[property.status];
  
  if (!allowedTransitions.includes(newStatus)) {
    throw new Error(
      `Invalid status transition: ${property.status} -> ${newStatus}. ` +
      `Allowed: ${allowedTransitions.join(', ')}`
    );
  }
  
  return {
    ...property,
    status: newStatus,
    updatedAt: new Date(),
  };
}

/**
 * Propertyを削除マーク（論理削除）
 */
export function markPropertyAsDeleted(property: Property): Property {
  if (property.status === 'occupied') {
    throw new Error('Cannot delete occupied property');
  }
  
  return {
    ...property,
    status: 'under_maintenance',  // 削除は under_maintenance で表現
    updatedAt: new Date(),
  };
}

/**
 * 検索条件に一致するかチェック
 */
export function matchesSearchCriteria(
  property: Property,
  criteria: {
    prefecture?: string;
    city?: string;
    propertyType?: PropertyType;
    minRent?: number;
    maxRent?: number;
    minSize?: number;
    maxSize?: number;
    amenities?: string[];
    status?: PropertyStatus;
  }
): boolean {
  if (criteria.prefecture && property.address.prefecture !== criteria.prefecture) {
    return false;
  }
  if (criteria.city && property.address.city !== criteria.city) {
    return false;
  }
  if (criteria.propertyType && property.propertyType !== criteria.propertyType) {
    return false;
  }
  if (criteria.minRent !== undefined && property.monthlyRent.amount < criteria.minRent) {
    return false;
  }
  if (criteria.maxRent !== undefined && property.monthlyRent.amount > criteria.maxRent) {
    return false;
  }
  if (criteria.minSize !== undefined && property.sizeSqm < criteria.minSize) {
    return false;
  }
  if (criteria.maxSize !== undefined && property.sizeSqm > criteria.maxSize) {
    return false;
  }
  if (criteria.status && property.status !== criteria.status) {
    return false;
  }
  if (criteria.amenities && criteria.amenities.length > 0) {
    const hasAllAmenities = criteria.amenities.every(a => 
      property.amenities.includes(a)
    );
    if (!hasAllAmenities) {
      return false;
    }
  }
  
  return true;
}
