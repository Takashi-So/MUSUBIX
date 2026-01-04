/**
 * Domain Events
 * @design DES-DELIVERY-001 §8
 * @task TSK-DLV-018, TSK-DLV-019, TSK-DLV-020, TSK-DLV-021
 */

// ============================================================
// Base Event
// ============================================================
export abstract class DomainEvent<T = unknown> {
  public readonly occurredAt: Date;
  public abstract readonly eventName: string;

  constructor(public readonly payload: T) {
    this.occurredAt = new Date();
  }
}

// ============================================================
// Event Bus
// ============================================================
export type EventHandler<T = unknown> = (event: DomainEvent<T>) => void;

export class EventBus {
  private handlers: Map<string, EventHandler[]> = new Map();

  subscribe(eventName: string, handler: EventHandler): void {
    const existingHandlers = this.handlers.get(eventName) || [];
    this.handlers.set(eventName, [...existingHandlers, handler]);
  }

  unsubscribe(eventName: string, handler: EventHandler): void {
    const existingHandlers = this.handlers.get(eventName) || [];
    this.handlers.set(
      eventName,
      existingHandlers.filter((h) => h !== handler)
    );
  }

  publish(event: DomainEvent): void {
    const eventHandlers = this.handlers.get(event.eventName) || [];
    eventHandlers.forEach((handler) => handler(event));
  }
}

// ============================================================
// Order Events
// ============================================================
export interface OrderPlacedPayload {
  orderId: string;
  customerId: string;
  restaurantId: string;
  items: Array<{ name: string; quantity: number; price: number }>;
  total: number;
}

export class OrderPlacedEvent extends DomainEvent<OrderPlacedPayload> {
  readonly eventName = 'OrderPlacedEvent';
}

export interface OrderAcceptedPayload {
  orderId: string;
  restaurantId: string;
  estimatedPreparationMinutes: number;
}

export class OrderAcceptedEvent extends DomainEvent<OrderAcceptedPayload> {
  readonly eventName = 'OrderAcceptedEvent';
}

export interface OrderCancelledPayload {
  orderId: string;
  reason: string;
  cancelledBy: 'customer' | 'restaurant' | 'system';
}

export class OrderCancelledEvent extends DomainEvent<OrderCancelledPayload> {
  readonly eventName = 'OrderCancelledEvent';
}

// ============================================================
// Delivery Events
// ============================================================
export interface DeliveryAssignedPayload {
  deliveryId: string;
  orderId: string;
  driverId: string;
  driverName: string;
  estimatedArrival: Date;
}

export class DeliveryAssignedEvent extends DomainEvent<DeliveryAssignedPayload> {
  readonly eventName = 'DeliveryAssignedEvent';
}

export interface DeliveryCompletedPayload {
  deliveryId: string;
  orderId: string;
  driverId: string;
  completedAt: Date;
}

export class DeliveryCompletedEvent extends DomainEvent<DeliveryCompletedPayload> {
  readonly eventName = 'DeliveryCompletedEvent';
}

export interface DriverLocationUpdatedPayload {
  driverId: string;
  latitude: number;
  longitude: number;
  deliveryId?: string;
}

export class DriverLocationUpdatedEvent extends DomainEvent<DriverLocationUpdatedPayload> {
  readonly eventName = 'DriverLocationUpdatedEvent';
}

// ============================================================
// Payment Events
// ============================================================
export interface PaymentCompletedPayload {
  paymentId: string;
  orderId: string;
  amount: number;
  method: string;
}

export class PaymentCompletedEvent extends DomainEvent<PaymentCompletedPayload> {
  readonly eventName = 'PaymentCompletedEvent';
}

export interface PaymentFailedPayload {
  paymentId: string;
  orderId: string;
  reason: string;
}

export class PaymentFailedEvent extends DomainEvent<PaymentFailedPayload> {
  readonly eventName = 'PaymentFailedEvent';
}
