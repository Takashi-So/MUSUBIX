/**
 * Domain Events Tests
 * @task TSK-DLV-018, TSK-DLV-019, TSK-DLV-020, TSK-DLV-021
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  EventBus,
  DomainEvent,
  OrderPlacedEvent,
  OrderAcceptedEvent,
  OrderCancelledEvent,
  DeliveryAssignedEvent,
  DeliveryCompletedEvent,
  DriverLocationUpdatedEvent,
} from '../../src/domain/events';
import { OrderId, OrderStatus } from '../../src/domain/order';
import { CustomerId } from '../../src/domain/customer';
import { RestaurantId } from '../../src/domain/restaurant';
import { DriverId, DeliveryId } from '../../src/domain/delivery';
import { Money, GeoLocation } from '../../src/domain/shared';

describe('EventBus', () => {
  let eventBus: EventBus;

  beforeEach(() => {
    eventBus = new EventBus();
  });

  describe('subscribe and publish', () => {
    it('should call handler when event is published', () => {
      const handler = vi.fn();
      eventBus.subscribe('OrderPlacedEvent', handler);

      const event = new OrderPlacedEvent({
        orderId: 'order-1',
        customerId: 'cust-1',
        restaurantId: 'rest-1',
        items: [{ name: 'Ramen', quantity: 1, price: 1200 }],
        total: 1500,
      });
      eventBus.publish(event);

      expect(handler).toHaveBeenCalledWith(event);
    });

    it('should call multiple handlers for same event', () => {
      const handler1 = vi.fn();
      const handler2 = vi.fn();
      eventBus.subscribe('OrderPlacedEvent', handler1);
      eventBus.subscribe('OrderPlacedEvent', handler2);

      const event = new OrderPlacedEvent({
        orderId: 'order-1',
        customerId: 'cust-1',
        restaurantId: 'rest-1',
        items: [],
        total: 0,
      });
      eventBus.publish(event);

      expect(handler1).toHaveBeenCalled();
      expect(handler2).toHaveBeenCalled();
    });
  });

  describe('unsubscribe', () => {
    it('should not call handler after unsubscribe', () => {
      const handler = vi.fn();
      eventBus.subscribe('OrderPlacedEvent', handler);
      eventBus.unsubscribe('OrderPlacedEvent', handler);

      const event = new OrderPlacedEvent({
        orderId: 'order-1',
        customerId: 'cust-1',
        restaurantId: 'rest-1',
        items: [],
        total: 0,
      });
      eventBus.publish(event);

      expect(handler).not.toHaveBeenCalled();
    });
  });
});

describe('Order Events', () => {
  describe('OrderPlacedEvent', () => {
    it('should create event with correct data', () => {
      const event = new OrderPlacedEvent({
        orderId: 'order-1',
        customerId: 'cust-1',
        restaurantId: 'rest-1',
        items: [{ name: 'Ramen', quantity: 2, price: 1200 }],
        total: 2700,
      });

      expect(event.eventName).toBe('OrderPlacedEvent');
      expect(event.payload.orderId).toBe('order-1');
      expect(event.payload.total).toBe(2700);
      expect(event.occurredAt).toBeInstanceOf(Date);
    });
  });

  describe('OrderAcceptedEvent', () => {
    it('should create event with estimated time', () => {
      const event = new OrderAcceptedEvent({
        orderId: 'order-1',
        restaurantId: 'rest-1',
        estimatedPreparationMinutes: 20,
      });

      expect(event.eventName).toBe('OrderAcceptedEvent');
      expect(event.payload.estimatedPreparationMinutes).toBe(20);
    });
  });

  describe('OrderCancelledEvent', () => {
    it('should include cancellation reason', () => {
      const event = new OrderCancelledEvent({
        orderId: 'order-1',
        reason: 'Customer requested',
        cancelledBy: 'customer',
      });

      expect(event.eventName).toBe('OrderCancelledEvent');
      expect(event.payload.reason).toBe('Customer requested');
    });
  });
});

describe('Delivery Events', () => {
  describe('DeliveryAssignedEvent', () => {
    it('should create event with driver and ETA', () => {
      const event = new DeliveryAssignedEvent({
        deliveryId: 'del-1',
        orderId: 'order-1',
        driverId: 'driver-1',
        driverName: 'John Driver',
        estimatedArrival: new Date('2024-01-01T12:30:00'),
      });

      expect(event.eventName).toBe('DeliveryAssignedEvent');
      expect(event.payload.driverId).toBe('driver-1');
    });
  });

  describe('DeliveryCompletedEvent', () => {
    it('should include completion time', () => {
      const event = new DeliveryCompletedEvent({
        deliveryId: 'del-1',
        orderId: 'order-1',
        driverId: 'driver-1',
        completedAt: new Date(),
      });

      expect(event.eventName).toBe('DeliveryCompletedEvent');
      expect(event.payload.completedAt).toBeInstanceOf(Date);
    });
  });

  describe('DriverLocationUpdatedEvent', () => {
    it('should include new location', () => {
      const event = new DriverLocationUpdatedEvent({
        driverId: 'driver-1',
        latitude: 35.6762,
        longitude: 139.6503,
        deliveryId: 'del-1',
      });

      expect(event.eventName).toBe('DriverLocationUpdatedEvent');
      expect(event.payload.latitude).toBe(35.6762);
    });
  });
});
