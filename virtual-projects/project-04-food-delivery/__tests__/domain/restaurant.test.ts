/**
 * Restaurant Entity Tests
 * @task TSK-DLV-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  Restaurant,
  RestaurantId,
  RestaurantStatus,
  CuisineType,
} from '../../src/domain/restaurant';
import { Money, GeoLocation, Address, OperatingHours, DayOfWeek } from '../../src/domain/shared';

describe('Restaurant', () => {
  let validRestaurant: Restaurant;

  beforeEach(() => {
    validRestaurant = Restaurant.create({
      name: 'Sushi Taro',
      address: new Address('1-2-3 Ginza', 'Tokyo', '104-0061'),
      location: new GeoLocation(35.6717, 139.7636),
      phone: '03-1234-5678',
      cuisineType: CuisineType.JAPANESE,
      minimumOrder: new Money(1000),
      deliveryFee: new Money(300),
      operatingHours: [
        new OperatingHours(DayOfWeek.MONDAY, '11:00', '22:00'),
        new OperatingHours(DayOfWeek.TUESDAY, '11:00', '22:00'),
        new OperatingHours(DayOfWeek.WEDNESDAY, '11:00', '22:00'),
      ],
    });
  });

  describe('creation', () => {
    it('should create a restaurant with valid data', () => {
      expect(validRestaurant.id).toBeInstanceOf(RestaurantId);
      expect(validRestaurant.name).toBe('Sushi Taro');
      expect(validRestaurant.cuisineType).toBe(CuisineType.JAPANESE);
      expect(validRestaurant.status).toBe(RestaurantStatus.PENDING);
    });

    it('should reject empty name', () => {
      expect(() =>
        Restaurant.create({
          name: '',
          address: new Address('1-2-3 Ginza', 'Tokyo', '104-0061'),
          location: new GeoLocation(35.6717, 139.7636),
          phone: '03-1234-5678',
          cuisineType: CuisineType.JAPANESE,
          minimumOrder: new Money(1000),
          deliveryFee: new Money(300),
          operatingHours: [],
        })
      ).toThrow('Name is required');
    });

    it('should reject name shorter than 2 characters', () => {
      expect(() =>
        Restaurant.create({
          name: 'A',
          address: new Address('1-2-3 Ginza', 'Tokyo', '104-0061'),
          location: new GeoLocation(35.6717, 139.7636),
          phone: '03-1234-5678',
          cuisineType: CuisineType.JAPANESE,
          minimumOrder: new Money(1000),
          deliveryFee: new Money(300),
          operatingHours: [],
        })
      ).toThrow('Name must be at least 2 characters');
    });
  });

  describe('status management', () => {
    it('should start with PENDING status', () => {
      expect(validRestaurant.status).toBe(RestaurantStatus.PENDING);
    });

    it('should allow activation', () => {
      validRestaurant.activate();
      expect(validRestaurant.status).toBe(RestaurantStatus.ACTIVE);
    });

    it('should allow suspension', () => {
      validRestaurant.activate();
      validRestaurant.suspend();
      expect(validRestaurant.status).toBe(RestaurantStatus.SUSPENDED);
    });

    it('should allow closing', () => {
      validRestaurant.activate();
      validRestaurant.close();
      expect(validRestaurant.status).toBe(RestaurantStatus.CLOSED);
    });
  });

  describe('isOpen', () => {
    it('should return true when within operating hours', () => {
      validRestaurant.activate();
      // Mock current time to Monday 12:00
      const monday = new Date('2024-01-15T12:00:00'); // Monday
      expect(validRestaurant.isOpenAt(monday)).toBe(true);
    });

    it('should return false when outside operating hours', () => {
      validRestaurant.activate();
      const monday = new Date('2024-01-15T08:00:00'); // Monday 8:00
      expect(validRestaurant.isOpenAt(monday)).toBe(false);
    });

    it('should return false when restaurant is not active', () => {
      const monday = new Date('2024-01-15T12:00:00');
      expect(validRestaurant.isOpenAt(monday)).toBe(false);
    });

    it('should return false on days without operating hours', () => {
      validRestaurant.activate();
      const sunday = new Date('2024-01-14T12:00:00'); // Sunday
      expect(validRestaurant.isOpenAt(sunday)).toBe(false);
    });
  });

  describe('canAcceptOrder', () => {
    it('should accept order meeting minimum', () => {
      validRestaurant.activate();
      expect(validRestaurant.canAcceptOrder(new Money(1000))).toBe(true);
      expect(validRestaurant.canAcceptOrder(new Money(1500))).toBe(true);
    });

    it('should reject order below minimum', () => {
      validRestaurant.activate();
      expect(validRestaurant.canAcceptOrder(new Money(500))).toBe(false);
    });

    it('should reject order when not active', () => {
      expect(validRestaurant.canAcceptOrder(new Money(2000))).toBe(false);
    });
  });

  describe('rating', () => {
    it('should start with 0 rating', () => {
      expect(validRestaurant.rating).toBe(0);
    });

    it('should update rating', () => {
      validRestaurant.updateRating(4.5);
      expect(validRestaurant.rating).toBe(4.5);
    });

    it('should reject rating outside 0-5 range', () => {
      expect(() => validRestaurant.updateRating(-1)).toThrow();
      expect(() => validRestaurant.updateRating(6)).toThrow();
    });
  });
});

describe('RestaurantId', () => {
  it('should generate unique IDs', () => {
    const id1 = RestaurantId.generate();
    const id2 = RestaurantId.generate();
    expect(id1.value).not.toBe(id2.value);
  });

  it('should create from existing value', () => {
    const id = new RestaurantId('res-123');
    expect(id.value).toBe('res-123');
  });
});
