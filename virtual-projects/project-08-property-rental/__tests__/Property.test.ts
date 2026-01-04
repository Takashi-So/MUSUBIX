/**
 * Property Entity Tests
 * TSK-026: Property Entity Unit Tests
 * 
 * @see REQ-RENTAL-001 F001-F006
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createProperty,
  updateProperty,
  updatePropertyStatus,
  matchesSearchCriteria,
  resetPropertyCounter,
} from '../src/entities/Property.js';
import type { Property, Address, CreatePropertyInput } from '../src/types/index.js';

describe('Property Entity', () => {
  let validAddress: Address;

  beforeEach(() => {
    resetPropertyCounter();
    validAddress = {
      postalCode: '150-0001',
      prefecture: '東京都',
      city: '渋谷区',
      street: '神宮前1-2-3',
      building: 'サンプルマンション 101',
    };
  });

  describe('createProperty', () => {
    it('should create a property with valid inputs', () => {
      const input: CreatePropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: validAddress,
        propertyType: 'apartment',
        sizeSqm: 45.5,
        monthlyRent: 120000,
        deposit: 240000,
        keyMoney: 120000,
        maintenanceFee: 8000,
        amenities: ['エアコン', 'バス・トイレ別'],
        description: 'オートロック完備',
      };

      const property = createProperty(input);

      expect(property.id).toMatch(/^PROP-\d{8}-\d{3}$/);
      expect(property.ownerId).toBe('OWN-20250101-001');
      expect(property.status).toBe('available');
      expect(property.monthlyRent.amount).toBe(120000);
      expect(property.monthlyRent.currency).toBe('JPY');
    });

    it('should throw error for invalid postal code', () => {
      const input: CreatePropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: { ...validAddress, postalCode: 'invalid' },
        propertyType: 'apartment',
        sizeSqm: 45,
        monthlyRent: 100000,
        deposit: 200000,
        keyMoney: 100000,
        maintenanceFee: 5000,
      };

      expect(() => createProperty(input)).toThrow('Invalid postal code format');
    });

    it('should throw error for zero size', () => {
      const input: CreatePropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: validAddress,
        propertyType: 'apartment',
        sizeSqm: 0,
        monthlyRent: 100000,
        deposit: 200000,
        keyMoney: 100000,
        maintenanceFee: 5000,
      };

      expect(() => createProperty(input)).toThrow('Size must be greater than 0');
    });

    it('should throw error for negative rent', () => {
      const input: CreatePropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: validAddress,
        propertyType: 'apartment',
        sizeSqm: 45,
        monthlyRent: -10000,
        deposit: 200000,
        keyMoney: 100000,
        maintenanceFee: 5000,
      };

      expect(() => createProperty(input)).toThrow('Monthly rent cannot be negative');
    });
  });

  describe('updateProperty', () => {
    let existingProperty: Property;

    beforeEach(() => {
      const input: CreatePropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: validAddress,
        propertyType: 'apartment',
        sizeSqm: 45,
        monthlyRent: 100000,
        deposit: 200000,
        keyMoney: 100000,
        maintenanceFee: 5000,
      };
      existingProperty = createProperty(input);
    });

    it('should update property description', () => {
      const updated = updateProperty(existingProperty, { description: '新しい説明' });
      expect(updated.description).toBe('新しい説明');
      expect(updated.id).toBe(existingProperty.id);
    });

    it('should update rent amount', () => {
      const updated = updateProperty(existingProperty, { monthlyRent: 130000 });
      expect(updated.monthlyRent.amount).toBe(130000);
    });

    it('should update timestamp', () => {
      const updated = updateProperty(existingProperty, { description: '更新' });
      expect(updated.updatedAt.getTime()).toBeGreaterThanOrEqual(
        existingProperty.updatedAt.getTime()
      );
    });
  });

  describe('updatePropertyStatus', () => {
    let property: Property;

    beforeEach(() => {
      const input: CreatePropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: validAddress,
        propertyType: 'apartment',
        sizeSqm: 45,
        monthlyRent: 100000,
        deposit: 200000,
        keyMoney: 100000,
        maintenanceFee: 5000,
      };
      property = createProperty(input);
    });

    it('should update status to occupied', () => {
      const updated = updatePropertyStatus(property, 'occupied');
      expect(updated.status).toBe('occupied');
    });

    it('should update status to under_maintenance', () => {
      const updated = updatePropertyStatus(property, 'under_maintenance');
      expect(updated.status).toBe('under_maintenance');
    });

    it('should throw error for invalid transition', () => {
      const occupied = updatePropertyStatus(property, 'occupied');
      expect(() => updatePropertyStatus(occupied, 'reserved')).toThrow('Invalid status transition');
    });
  });

  describe('matchesSearchCriteria', () => {
    let property: Property;

    beforeEach(() => {
      const input: CreatePropertyInput = {
        ownerId: 'OWN-20250101-001',
        address: validAddress,
        propertyType: 'apartment',
        sizeSqm: 45,
        monthlyRent: 100000,
        deposit: 200000,
        keyMoney: 100000,
        maintenanceFee: 5000,
        amenities: ['エアコン', '駐車場'],
      };
      property = createProperty(input);
    });

    it('should match when no criteria specified', () => {
      expect(matchesSearchCriteria(property, {})).toBe(true);
    });

    it('should match property type', () => {
      expect(matchesSearchCriteria(property, { propertyType: 'apartment' })).toBe(true);
    });

    it('should not match different property type', () => {
      expect(matchesSearchCriteria(property, { propertyType: 'house' })).toBe(false);
    });

    it('should match rent range', () => {
      expect(matchesSearchCriteria(property, { minRent: 80000, maxRent: 120000 })).toBe(true);
    });

    it('should not match rent below minimum', () => {
      expect(matchesSearchCriteria(property, { minRent: 150000 })).toBe(false);
    });

    it('should match size range', () => {
      expect(matchesSearchCriteria(property, { minSize: 40, maxSize: 50 })).toBe(true);
    });

    it('should match prefecture', () => {
      expect(matchesSearchCriteria(property, { prefecture: '東京都' })).toBe(true);
    });

    it('should match amenities', () => {
      expect(matchesSearchCriteria(property, { amenities: ['エアコン'] })).toBe(true);
    });

    it('should not match missing amenities', () => {
      expect(matchesSearchCriteria(property, { amenities: ['オートロック'] })).toBe(false);
    });
  });
});
