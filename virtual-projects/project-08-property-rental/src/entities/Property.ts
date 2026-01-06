/**
 * Property Entity
 * 
 * @requirement REQ-RENTAL-001-F001 (Property Registration)
 * @requirement REQ-RENTAL-001-F002 (Property Status Transition)
 * @design DES-RENTAL-001-C001
 */

import { Result, ok, err } from 'neverthrow';
import {
  PropertyId,
  PropertyStatus,
  PropertyType,
  Money,
  Address,
  generatePropertyId,
  createMoney,
  createAddress,
  validPropertyStatusTransitions,
  ValidationError,
} from '../types/common.js';
import { InvalidStatusTransitionError } from '../types/errors.js';

// ============================================================
// Property Entity
// ============================================================

export interface Property {
  readonly id: PropertyId;
  readonly address: Address;
  readonly propertyType: PropertyType;
  readonly sizeSqm: number;
  readonly monthlyRent: Money;
  readonly deposit: Money;
  readonly status: PropertyStatus;
  readonly amenities: string[];
  readonly description?: string;
  readonly photos?: string[];
  readonly createdAt: Date;
  readonly updatedAt: Date;
  readonly version: number;
}

// ============================================================
// Input DTO (BP-CODE-001)
// ============================================================

export interface CreatePropertyInput {
  address: {
    prefecture: string;
    city: string;
    street: string;
    building?: string;
  };
  propertyType: PropertyType;
  sizeSqm: number;
  monthlyRent: number;
  deposit: number;
  amenities?: string[];
  description?: string;
  photos?: string[];
}

// ============================================================
// Factory Function
// ============================================================

export function createProperty(
  input: CreatePropertyInput,
  date: Date = new Date()
): Result<Property, ValidationError> {
  // Validate address
  const addressResult = createAddress(input.address);
  if (addressResult.isErr()) {
    return err(addressResult.error);
  }

  // Validate size
  if (input.sizeSqm <= 0) {
    return err(new ValidationError('Size must be positive'));
  }

  // Validate monthly rent
  const monthlyRentResult = createMoney(input.monthlyRent);
  if (monthlyRentResult.isErr()) {
    return err(monthlyRentResult.error);
  }

  // Validate deposit
  const depositResult = createMoney(input.deposit);
  if (depositResult.isErr()) {
    return err(depositResult.error);
  }

  const now = new Date();
  const property: Property = {
    id: generatePropertyId(date),
    address: addressResult.value,
    propertyType: input.propertyType,
    sizeSqm: input.sizeSqm,
    monthlyRent: monthlyRentResult.value,
    deposit: depositResult.value,
    status: 'available', // AC4: Default status
    amenities: input.amenities ?? [],
    description: input.description,
    photos: input.photos,
    createdAt: now,
    updatedAt: now,
    version: 1,
  };

  return ok(property);
}

// ============================================================
// Status Transition Functions (BP-DESIGN-001)
// ============================================================

export function canTransitionPropertyStatus(
  currentStatus: PropertyStatus,
  targetStatus: PropertyStatus
): boolean {
  const validTransitions = validPropertyStatusTransitions[currentStatus];
  return validTransitions.includes(targetStatus);
}

export function transitionPropertyStatus(
  property: Property,
  targetStatus: PropertyStatus,
  reason: string
): Result<Property, InvalidStatusTransitionError> {
  if (!canTransitionPropertyStatus(property.status, targetStatus)) {
    return err(
      new InvalidStatusTransitionError('Property', property.status, targetStatus)
    );
  }

  const updatedProperty: Property = {
    ...property,
    status: targetStatus,
    updatedAt: new Date(),
    version: property.version + 1,
  };

  return ok(updatedProperty);
}

// ============================================================
// Search Filters
// ============================================================

export interface PropertySearchFilters {
  location?: string;
  minRent?: number;
  maxRent?: number;
  minSize?: number;
  maxSize?: number;
  propertyType?: PropertyType;
  amenities?: string[];
  status?: PropertyStatus;
}

export function matchesFilters(property: Property, filters: PropertySearchFilters): boolean {
  // Location filter (partial match on prefecture, city, or street)
  if (filters.location) {
    const locationLower = filters.location.toLowerCase();
    const addressString = `${property.address.prefecture}${property.address.city}${property.address.street}`.toLowerCase();
    if (!addressString.includes(locationLower)) {
      return false;
    }
  }

  // Rent range filter
  if (filters.minRent !== undefined && property.monthlyRent.amount < filters.minRent) {
    return false;
  }
  if (filters.maxRent !== undefined && property.monthlyRent.amount > filters.maxRent) {
    return false;
  }

  // Size range filter
  if (filters.minSize !== undefined && property.sizeSqm < filters.minSize) {
    return false;
  }
  if (filters.maxSize !== undefined && property.sizeSqm > filters.maxSize) {
    return false;
  }

  // Property type filter
  if (filters.propertyType !== undefined && property.propertyType !== filters.propertyType) {
    return false;
  }

  // Amenities filter (AND match - all requested amenities must be present)
  if (filters.amenities && filters.amenities.length > 0) {
    const hasAllAmenities = filters.amenities.every(amenity =>
      property.amenities.includes(amenity)
    );
    if (!hasAllAmenities) {
      return false;
    }
  }

  // Status filter
  if (filters.status !== undefined && property.status !== filters.status) {
    return false;
  }

  return true;
}
