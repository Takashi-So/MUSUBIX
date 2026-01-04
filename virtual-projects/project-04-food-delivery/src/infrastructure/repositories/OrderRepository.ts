/**
 * InMemory Order Repository
 * @design DES-DELIVERY-001 §6.2
 * @task TSK-DLV-011
 */

import {
  Order,
  OrderId,
  OrderStatus,
} from '../../domain/order';
import { CustomerId } from '../../domain/customer';
import { RestaurantId } from '../../domain/restaurant';

export interface OrderRepository {
  save(order: Order): Promise<void>;
  findById(id: OrderId): Promise<Order | undefined>;
  findByCustomerId(customerId: CustomerId): Promise<Order[]>;
  findByRestaurantId(restaurantId: RestaurantId): Promise<Order[]>;
  findByStatus(status: OrderStatus): Promise<Order[]>;
}

export class InMemoryOrderRepository implements OrderRepository {
  private orders: Map<string, Order> = new Map();

  async save(order: Order): Promise<void> {
    this.orders.set(order.id.value, order);
  }

  async findById(id: OrderId): Promise<Order | undefined> {
    return this.orders.get(id.value);
  }

  async findByCustomerId(customerId: CustomerId): Promise<Order[]> {
    return Array.from(this.orders.values()).filter(
      (order) => order.customerId.equals(customerId)
    );
  }

  async findByRestaurantId(restaurantId: RestaurantId): Promise<Order[]> {
    return Array.from(this.orders.values()).filter(
      (order) => order.restaurantId.equals(restaurantId)
    );
  }

  async findByStatus(status: OrderStatus): Promise<Order[]> {
    return Array.from(this.orders.values()).filter(
      (order) => order.status === status
    );
  }
}
