/**
 * Property Entity Tests
 * 
 * @requirement REQ-RENTAL-001-F001 (Property Registration)
 * @requirement REQ-RENTAL-001-F002 (Property Status Transition)
 * @design DES-RENTAL-001-C001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  Property,
  createProperty,
  CreatePropertyInput,
  canTransitionPropertyStatus,
  transitionPropertyStatus,
} from '../src/entities/Property.js';
import {
  resetPropertyCounter,
  PropertyStatus,
} from '../src/types/common.js';

describe('Property Entity', () => {
  beforeEach(() => {
    // BP-TEST-001: Reset counters before each test
    resetPropertyCounter();
  });

  describe('createProperty', () => {
    it('should create a property with valid input', () => {
      // Arrange
      const input: CreatePropertyInput = {
        address: {
          prefecture: '東京都',
          city: '渋谷区',
          street: '恵比寿1-1-1',
          building: 'テストビル101',
        },
        propertyType: 'apartment',
        sizeSqm: 50,
        monthlyRent: 150000,
        deposit: 300000,
        amenities: ['エアコン', '駐車場'],
        description: 'テスト物件',
      };

      // Act
      const result = createProperty(input);

      // Assert (BP-TEST-004: Result Type Test Pattern)
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        const property = result.value;
        expect(property.id.value).toMatch(/^PROP-\d{8}-001$/);
        expect(property.address.prefecture).toBe('東京都');
        expect(property.address.city).toBe('渋谷区');
        expect(property.propertyType).toBe('apartment');
        expect(property.sizeSqm).toBe(50);
        expect(property.monthlyRent.amount).toBe(150000);
        expect(property.deposit.amount).toBe(300000);
        expect(property.status).toBe('available'); // AC4: Default status
        expect(property.amenities).toEqual(['エアコン', '駐車場']);
        expect(property.version).toBe(1);
      }
    });

    it('should generate unique IDs for multiple properties', () => {
      const input: CreatePropertyInput = {
        address: {
          prefecture: '東京都',
          city: '新宿区',
          street: '西新宿2-2-2',
        },
        propertyType: 'house',
        sizeSqm: 100,
        monthlyRent: 200000,
        deposit: 400000,
      };

      const result1 = createProperty(input);
      const result2 = createProperty(input);

      expect(result1.isOk()).toBe(true);
      expect(result2.isOk()).toBe(true);
      if (result1.isOk() && result2.isOk()) {
        expect(result1.value.id.value).not.toBe(result2.value.id.value);
        expect(result1.value.id.value).toMatch(/-001$/);
        expect(result2.value.id.value).toMatch(/-002$/);
      }
    });

    it('should reject negative monthly rent', () => {
      const input: CreatePropertyInput = {
        address: {
          prefecture: '東京都',
          city: '渋谷区',
          street: '恵比寿1-1-1',
        },
        propertyType: 'apartment',
        sizeSqm: 50,
        monthlyRent: -10000, // Invalid
        deposit: 300000,
      };

      const result = createProperty(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('non-negative');
      }
    });

    it('should reject zero size', () => {
      const input: CreatePropertyInput = {
        address: {
          prefecture: '東京都',
          city: '渋谷区',
          street: '恵比寿1-1-1',
        },
        propertyType: 'apartment',
        sizeSqm: 0, // Invalid
        monthlyRent: 150000,
        deposit: 300000,
      };

      const result = createProperty(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('positive');
      }
    });

    it('should reject empty prefecture', () => {
      const input: CreatePropertyInput = {
        address: {
          prefecture: '', // Invalid
          city: '渋谷区',
          street: '恵比寿1-1-1',
        },
        propertyType: 'apartment',
        sizeSqm: 50,
        monthlyRent: 150000,
        deposit: 300000,
      };

      const result = createProperty(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('Prefecture');
      }
    });
  });

  describe('Property Status Transitions (BP-TEST-005)', () => {
    // REQ-RENTAL-001-F002: Valid transitions
    
    it('should allow available → pending transition', () => {
      expect(canTransitionPropertyStatus('available', 'pending')).toBe(true);
    });

    it('should allow available → maintenance transition', () => {
      expect(canTransitionPropertyStatus('available', 'maintenance')).toBe(true);
    });

    it('should allow pending → occupied transition', () => {
      expect(canTransitionPropertyStatus('pending', 'occupied')).toBe(true);
    });

    it('should allow pending → available transition', () => {
      expect(canTransitionPropertyStatus('pending', 'available')).toBe(true);
    });

    it('should allow occupied → available transition', () => {
      expect(canTransitionPropertyStatus('occupied', 'available')).toBe(true);
    });

    it('should allow occupied → maintenance transition', () => {
      expect(canTransitionPropertyStatus('occupied', 'maintenance')).toBe(true);
    });

    it('should allow maintenance → available transition', () => {
      expect(canTransitionPropertyStatus('maintenance', 'available')).toBe(true);
    });

    // Invalid transitions
    it('should NOT allow available → occupied transition', () => {
      expect(canTransitionPropertyStatus('available', 'occupied')).toBe(false);
    });

    it('should NOT allow pending → maintenance transition', () => {
      expect(canTransitionPropertyStatus('pending', 'maintenance')).toBe(false);
    });

    it('should NOT allow maintenance → occupied transition', () => {
      expect(canTransitionPropertyStatus('maintenance', 'occupied')).toBe(false);
    });

    it('should NOT allow same-status transition', () => {
      const statuses: PropertyStatus[] = ['available', 'pending', 'occupied', 'maintenance'];
      statuses.forEach(status => {
        expect(canTransitionPropertyStatus(status, status)).toBe(false);
      });
    });
  });

  describe('transitionPropertyStatus', () => {
    it('should transition property status successfully', () => {
      const input: CreatePropertyInput = {
        address: {
          prefecture: '東京都',
          city: '渋谷区',
          street: '恵比寿1-1-1',
        },
        propertyType: 'apartment',
        sizeSqm: 50,
        monthlyRent: 150000,
        deposit: 300000,
      };

      const createResult = createProperty(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const property = createResult.value;
      const transitionResult = transitionPropertyStatus(property, 'pending', 'Application received');

      expect(transitionResult.isOk()).toBe(true);
      if (transitionResult.isOk()) {
        expect(transitionResult.value.status).toBe('pending');
        expect(transitionResult.value.version).toBe(2); // Version incremented
      }
    });

    it('should reject invalid transition', () => {
      const input: CreatePropertyInput = {
        address: {
          prefecture: '東京都',
          city: '渋谷区',
          street: '恵比寿1-1-1',
        },
        propertyType: 'apartment',
        sizeSqm: 50,
        monthlyRent: 150000,
        deposit: 300000,
      };

      const createResult = createProperty(input);
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const property = createResult.value;
      // available → occupied is invalid
      const transitionResult = transitionPropertyStatus(property, 'occupied', 'Invalid');

      expect(transitionResult.isErr()).toBe(true);
      if (transitionResult.isErr()) {
        expect(transitionResult.error._tag).toBe('InvalidStatusTransitionError');
      }
    });
  });
});
