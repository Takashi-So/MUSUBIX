/**
 * InMemory Driver Repository
 * @design DES-DELIVERY-001 §6.4
 * @task TSK-DLV-013
 */

import {
  Driver,
  DriverId,
  DriverStatus,
} from '../../domain/delivery';
import { GeoLocation } from '../../domain/shared';

export interface DriverRepository {
  save(driver: Driver): Promise<void>;
  findById(id: DriverId): Promise<Driver | undefined>;
  findAvailableNearby(location: GeoLocation, radiusKm: number): Promise<Driver[]>;
}

export class InMemoryDriverRepository implements DriverRepository {
  private drivers: Map<string, Driver> = new Map();

  async save(driver: Driver): Promise<void> {
    this.drivers.set(driver.id.value, driver);
  }

  async findById(id: DriverId): Promise<Driver | undefined> {
    return this.drivers.get(id.value);
  }

  async findAvailableNearby(location: GeoLocation, radiusKm: number): Promise<Driver[]> {
    return Array.from(this.drivers.values()).filter(
      (driver) =>
        driver.status === DriverStatus.AVAILABLE &&
        location.distanceTo(driver.currentLocation) <= radiusKm
    );
  }
}
