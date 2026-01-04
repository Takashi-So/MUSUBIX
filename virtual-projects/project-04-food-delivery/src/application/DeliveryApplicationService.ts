/**
 * Delivery Application Service
 * @design DES-DELIVERY-001 §7.3
 * @task TSK-DLV-016
 */

import {
  Delivery,
  DeliveryId,
  Driver,
  DriverId,
  DriverStatus,
} from '../domain/delivery';
import { OrderId } from '../domain/order';
import {
  DeliveryRepository,
  DriverRepository,
  OrderRepository,
} from '../infrastructure/repositories';
import { GeoLocation } from '../domain/shared';

export interface AssignDeliveryCommand {
  orderId: string;
  pickupLocation: { latitude: number; longitude: number };
  deliveryLocation: { latitude: number; longitude: number };
}

export interface AssignDeliveryResult {
  success: boolean;
  delivery?: Delivery;
  error?: string;
}

export interface UpdateLocationResult {
  success: boolean;
  error?: string;
}

export interface CompleteDeliveryResult {
  success: boolean;
  error?: string;
}

export class DeliveryApplicationService {
  constructor(
    private readonly deliveryRepo: DeliveryRepository,
    private readonly driverRepo: DriverRepository,
    private readonly orderRepo: OrderRepository
  ) {}

  async assignDelivery(command: AssignDeliveryCommand): Promise<AssignDeliveryResult> {
    try {
      const pickupLocation = new GeoLocation(
        command.pickupLocation.latitude,
        command.pickupLocation.longitude
      );

      // Find nearest available driver
      const availableDrivers = await this.driverRepo.findAvailableNearby(
        pickupLocation,
        5 // 5km radius
      );

      if (availableDrivers.length === 0) {
        return { success: false, error: 'No available drivers nearby' };
      }

      // Select nearest driver
      const driver = availableDrivers.reduce((nearest, current) => {
        const nearestDist = nearest.currentLocation
          ? pickupLocation.distanceTo(nearest.currentLocation)
          : Infinity;
        const currentDist = current.currentLocation
          ? pickupLocation.distanceTo(current.currentLocation)
          : Infinity;
        return currentDist < nearestDist ? current : nearest;
      });

      // Create delivery
      const deliveryLocation = new GeoLocation(
        command.deliveryLocation.latitude,
        command.deliveryLocation.longitude
      );

      const distance = pickupLocation.distanceTo(deliveryLocation);
      const estimatedMinutes = Math.ceil(distance * 3) + 10; // 3 min/km + 10 min prep
      const estimatedArrival = new Date(Date.now() + estimatedMinutes * 60 * 1000);

      const delivery = Delivery.create({
        orderId: new OrderId(command.orderId),
        driverId: driver.id,
        pickupLocation,
        deliveryLocation,
        estimatedArrival,
      });

      // Update driver status
      driver.startDelivery(new OrderId(command.orderId));
      await this.driverRepo.save(driver);
      await this.deliveryRepo.save(delivery);

      return { success: true, delivery };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Assignment failed',
      };
    }
  }

  async updateDriverLocation(
    driverId: string,
    latitude: number,
    longitude: number
  ): Promise<UpdateLocationResult> {
    try {
      const driver = await this.driverRepo.findById(new DriverId(driverId));
      if (!driver) {
        return { success: false, error: 'Driver not found' };
      }

      driver.updateLocation(new GeoLocation(latitude, longitude));
      await this.driverRepo.save(driver);
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Location update failed',
      };
    }
  }

  async completeDelivery(deliveryId: string): Promise<CompleteDeliveryResult> {
    try {
      const delivery = await this.deliveryRepo.findById(
        new DeliveryId(deliveryId)
      );
      if (!delivery) {
        return { success: false, error: 'Delivery not found' };
      }

      delivery.complete();
      await this.deliveryRepo.save(delivery);

      // Update driver status
      const driver = await this.driverRepo.findById(delivery.driverId);
      if (driver) {
        driver.completeDelivery();
        await this.driverRepo.save(driver);
      }

      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Completion failed',
      };
    }
  }

  async getDeliveryByOrderId(orderId: string): Promise<Delivery | undefined> {
    return this.deliveryRepo.findByOrderId(new OrderId(orderId));
  }

  async getDriverActiveDeliveries(driverId: string): Promise<Delivery[]> {
    return this.deliveryRepo.findActiveByDriverId(new DriverId(driverId));
  }
}
