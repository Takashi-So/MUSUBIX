/**
 * Order Entity
 * @design DES-DELIVERY-001 §3.2
 * @task TSK-DLV-004
 */

import { Money, GeoLocation } from '../shared';
import { RestaurantId } from '../restaurant';
import { CustomerId } from '../customer';

// ============================================================
// Order ID
// ============================================================
export class OrderId {
  constructor(public readonly value: string) {}

  static generate(): OrderId {
    return new OrderId(`ord-${crypto.randomUUID()}`);
  }

  equals(other: OrderId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Order Status
// ============================================================
export enum OrderStatus {
  PLACED = 'PLACED',
  ACCEPTED = 'ACCEPTED',
  PREPARING = 'PREPARING',
  READY = 'READY',
  PICKED_UP = 'PICKED_UP',
  DELIVERED = 'DELIVERED',
  CANCELLED = 'CANCELLED',
}

// ============================================================
// Order Item (Value Object)
// ============================================================
export interface OrderItem {
  menuItemId: string;
  name: string;
  quantity: number;
  unitPrice: Money;
  customizations: string[];
  totalPrice: Money;
}

// ============================================================
// Delivery Address
// ============================================================
export interface OrderDeliveryAddress {
  street: string;
  city: string;
  postalCode: string;
  location: GeoLocation;
  instructions?: string;
}

// ============================================================
// Create Order Props
// ============================================================
export interface CreateOrderProps {
  customerId: CustomerId;
  restaurantId: RestaurantId;
  items: OrderItem[];
  deliveryAddress: OrderDeliveryAddress;
  deliveryFee: Money;
  discount?: Money;
}

// ============================================================
// Order Entity
// ============================================================
export class Order {
  private _status: OrderStatus = OrderStatus.PLACED;
  private _estimatedDeliveryTime?: Date;
  private _cancelledReason?: string;

  private constructor(
    public readonly id: OrderId,
    public readonly customerId: CustomerId,
    public readonly restaurantId: RestaurantId,
    private readonly _items: OrderItem[],
    private readonly _deliveryAddress: OrderDeliveryAddress,
    private readonly _subtotal: Money,
    private readonly _deliveryFee: Money,
    private readonly _tax: Money,
    private readonly _discount: Money,
    private readonly _total: Money,
    public readonly placedAt: Date
  ) {}

  static create(props: CreateOrderProps): Order {
    if (!props.items || props.items.length === 0) {
      throw new Error('Order must have at least one item');
    }

    // Calculate subtotal
    let subtotal = new Money(0);
    for (const item of props.items) {
      subtotal = subtotal.add(item.totalPrice);
    }

    // Calculate tax (10% in Japan)
    const tax = subtotal.multiply(0.1);

    // Discount
    const discount = props.discount || new Money(0);

    // Total
    const total = subtotal.add(props.deliveryFee).add(tax).subtract(discount);

    return new Order(
      OrderId.generate(),
      props.customerId,
      props.restaurantId,
      [...props.items],
      props.deliveryAddress,
      subtotal,
      props.deliveryFee,
      tax,
      discount,
      total,
      new Date()
    );
  }

  // Getters
  get items(): OrderItem[] {
    return [...this._items];
  }
  get deliveryAddress(): OrderDeliveryAddress {
    return { ...this._deliveryAddress };
  }
  get subtotal(): Money {
    return this._subtotal;
  }
  get deliveryFee(): Money {
    return this._deliveryFee;
  }
  get tax(): Money {
    return this._tax;
  }
  get discount(): Money {
    return this._discount;
  }
  get total(): Money {
    return this._total;
  }
  get status(): OrderStatus {
    return this._status;
  }
  get estimatedDeliveryTime(): Date | undefined {
    return this._estimatedDeliveryTime;
  }
  get cancelledReason(): string | undefined {
    return this._cancelledReason;
  }

  // Status transitions
  accept(): void {
    this.assertStatus(OrderStatus.PLACED);
    this._status = OrderStatus.ACCEPTED;
  }

  startPreparing(): void {
    this.assertStatus(OrderStatus.ACCEPTED);
    this._status = OrderStatus.PREPARING;
  }

  markReady(): void {
    this.assertStatus(OrderStatus.PREPARING);
    this._status = OrderStatus.READY;
  }

  markPickedUp(): void {
    this.assertStatus(OrderStatus.READY);
    this._status = OrderStatus.PICKED_UP;
  }

  markDelivered(): void {
    this.assertStatus(OrderStatus.PICKED_UP);
    this._status = OrderStatus.DELIVERED;
  }

  cancel(reason: string): void {
    if (
      this._status !== OrderStatus.PLACED &&
      this._status !== OrderStatus.ACCEPTED
    ) {
      throw new Error('Order cannot be cancelled at this stage');
    }
    this._status = OrderStatus.CANCELLED;
    this._cancelledReason = reason;
  }

  // Cancellation rules
  canBeCancelledByCustomer(): boolean {
    return this._status === OrderStatus.PLACED;
  }

  canBeCancelledByRestaurant(): boolean {
    return this._status === OrderStatus.ACCEPTED;
  }

  // ETA
  setEstimatedDeliveryTime(eta: Date): void {
    this._estimatedDeliveryTime = eta;
  }

  private assertStatus(expected: OrderStatus): void {
    if (this._status !== expected) {
      throw new Error(`Invalid status transition from ${this._status}`);
    }
  }
}
