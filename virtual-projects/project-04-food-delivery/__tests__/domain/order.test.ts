/**
 * Order Entity Tests
 * @task TSK-DLV-004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  Order,
  OrderId,
  OrderStatus,
  OrderItem,
} from '../../src/domain/order';
import { Money, GeoLocation, Address } from '../../src/domain/shared';
import { RestaurantId } from '../../src/domain/restaurant';
import { CustomerId } from '../../src/domain/customer';

describe('Order', () => {
  let validOrder: Order;
  const restaurantId = new RestaurantId('res-123');
  const customerId = new CustomerId('cust-456');
  const deliveryAddress = {
    street: '1-2-3 Shibuya',
    city: 'Tokyo',
    postalCode: '150-0001',
    location: new GeoLocation(35.6580, 139.7016),
    instructions: 'Ring twice',
  };

  beforeEach(() => {
    const items: OrderItem[] = [
      {
        menuItemId: 'item-1',
        name: 'Ramen',
        quantity: 2,
        unitPrice: new Money(1000),
        customizations: ['Extra noodles'],
        totalPrice: new Money(2000),
      },
      {
        menuItemId: 'item-2',
        name: 'Gyoza',
        quantity: 1,
        unitPrice: new Money(500),
        customizations: [],
        totalPrice: new Money(500),
      },
    ];

    validOrder = Order.create({
      customerId,
      restaurantId,
      items,
      deliveryAddress,
      deliveryFee: new Money(300),
    });
  });

  describe('creation', () => {
    it('should create order with valid data', () => {
      expect(validOrder.id).toBeInstanceOf(OrderId);
      expect(validOrder.customerId.equals(customerId)).toBe(true);
      expect(validOrder.restaurantId.equals(restaurantId)).toBe(true);
      expect(validOrder.status).toBe(OrderStatus.PLACED);
    });

    it('should calculate totals correctly', () => {
      expect(validOrder.subtotal.amount).toBe(2500);
      expect(validOrder.deliveryFee.amount).toBe(300);
      expect(validOrder.tax.amount).toBe(250); // 10% of subtotal
      expect(validOrder.total.amount).toBe(3050); // 2500 + 300 + 250
    });

    it('should reject empty items', () => {
      expect(() =>
        Order.create({
          customerId,
          restaurantId,
          items: [],
          deliveryAddress,
          deliveryFee: new Money(300),
        })
      ).toThrow('Order must have at least one item');
    });

    it('should set placedAt timestamp', () => {
      expect(validOrder.placedAt).toBeInstanceOf(Date);
    });
  });

  describe('status transitions', () => {
    it('should transition from PLACED to ACCEPTED', () => {
      validOrder.accept();
      expect(validOrder.status).toBe(OrderStatus.ACCEPTED);
    });

    it('should transition from ACCEPTED to PREPARING', () => {
      validOrder.accept();
      validOrder.startPreparing();
      expect(validOrder.status).toBe(OrderStatus.PREPARING);
    });

    it('should transition from PREPARING to READY', () => {
      validOrder.accept();
      validOrder.startPreparing();
      validOrder.markReady();
      expect(validOrder.status).toBe(OrderStatus.READY);
    });

    it('should transition from READY to PICKED_UP', () => {
      validOrder.accept();
      validOrder.startPreparing();
      validOrder.markReady();
      validOrder.markPickedUp();
      expect(validOrder.status).toBe(OrderStatus.PICKED_UP);
    });

    it('should transition from PICKED_UP to DELIVERED', () => {
      validOrder.accept();
      validOrder.startPreparing();
      validOrder.markReady();
      validOrder.markPickedUp();
      validOrder.markDelivered();
      expect(validOrder.status).toBe(OrderStatus.DELIVERED);
    });

    it('should reject invalid status transition', () => {
      expect(() => validOrder.startPreparing()).toThrow('Invalid status transition');
    });
  });

  describe('cancellation', () => {
    it('should allow customer cancellation when PLACED', () => {
      expect(validOrder.canBeCancelledByCustomer()).toBe(true);
      validOrder.cancel('Changed my mind');
      expect(validOrder.status).toBe(OrderStatus.CANCELLED);
    });

    it('should not allow customer cancellation when ACCEPTED', () => {
      validOrder.accept();
      expect(validOrder.canBeCancelledByCustomer()).toBe(false);
    });

    it('should allow restaurant cancellation when ACCEPTED', () => {
      validOrder.accept();
      expect(validOrder.canBeCancelledByRestaurant()).toBe(true);
      validOrder.cancel('Out of ingredients');
      expect(validOrder.status).toBe(OrderStatus.CANCELLED);
    });

    it('should not allow cancellation when PREPARING', () => {
      validOrder.accept();
      validOrder.startPreparing();
      expect(validOrder.canBeCancelledByRestaurant()).toBe(false);
    });
  });

  describe('estimated delivery time', () => {
    it('should set estimated delivery time', () => {
      const eta = new Date(Date.now() + 30 * 60 * 1000); // 30 minutes
      validOrder.setEstimatedDeliveryTime(eta);
      expect(validOrder.estimatedDeliveryTime).toEqual(eta);
    });
  });
});

describe('OrderId', () => {
  it('should generate unique IDs', () => {
    const id1 = OrderId.generate();
    const id2 = OrderId.generate();
    expect(id1.value).not.toBe(id2.value);
  });
});
