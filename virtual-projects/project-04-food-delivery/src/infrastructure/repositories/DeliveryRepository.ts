/**
 * InMemory Delivery Repository
 * @design DES-DELIVERY-001 §6.5
 * @task TSK-DLV-013
 */

import {
  Delivery,
  DeliveryId,
  DeliveryStatus,
  DriverId,
} from '../../domain/delivery';
import { OrderId } from '../../domain/order';

export interface DeliveryRepository {
  save(delivery: Delivery): Promise<void>;
  findById(id: DeliveryId): Promise<Delivery | undefined>;
  findByOrderId(orderId: OrderId): Promise<Delivery | undefined>;
  findByDriverId(driverId: DriverId): Promise<Delivery[]>;
  findActiveByDriverId(driverId: DriverId): Promise<Delivery[]>;
}

export class InMemoryDeliveryRepository implements DeliveryRepository {
  private deliveries: Map<string, Delivery> = new Map();

  async save(delivery: Delivery): Promise<void> {
    this.deliveries.set(delivery.id.value, delivery);
  }

  async findById(id: DeliveryId): Promise<Delivery | undefined> {
    return this.deliveries.get(id.value);
  }

  async findByOrderId(orderId: OrderId): Promise<Delivery | undefined> {
    return Array.from(this.deliveries.values()).find(
      (delivery) => delivery.orderId.equals(orderId)
    );
  }

  async findByDriverId(driverId: DriverId): Promise<Delivery[]> {
    return Array.from(this.deliveries.values()).filter(
      (delivery) => delivery.driverId.equals(driverId)
    );
  }

  async findActiveByDriverId(driverId: DriverId): Promise<Delivery[]> {
    const activeStatuses = [
      DeliveryStatus.ASSIGNED,
      DeliveryStatus.PICKED_UP,
      DeliveryStatus.IN_TRANSIT,
    ];
    return Array.from(this.deliveries.values()).filter(
      (delivery) =>
        delivery.driverId.equals(driverId) &&
        activeStatuses.includes(delivery.status)
    );
  }
}
