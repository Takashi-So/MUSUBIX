/**
 * Delivery Domain Service
 * @design DES-DELIVERY-001 §5.2
 * @task TSK-DLV-008
 */

import { Order } from '../order';
import { Driver, Delivery } from '../delivery';
import { GeoLocation } from '../shared';

export interface AssignDriverResult {
  success: boolean;
  delivery?: Delivery;
  error?: string;
}

export class DeliveryService {
  private readonly DEFAULT_RADIUS_KM = 3;

  assignDriver(
    order: Order,
    availableDrivers: Driver[],
    restaurantLocation: GeoLocation
  ): AssignDriverResult {
    // Filter available drivers within radius
    const driversInRange = availableDrivers
      .filter((driver) => {
        if (!driver.isAvailable() || !driver.currentLocation) {
          return false;
        }
        const distance = driver.currentLocation.distanceTo(restaurantLocation);
        return distance <= this.DEFAULT_RADIUS_KM;
      })
      .sort((a, b) => {
        const distA = a.currentLocation!.distanceTo(restaurantLocation);
        const distB = b.currentLocation!.distanceTo(restaurantLocation);
        return distA - distB;
      });

    if (driversInRange.length === 0) {
      return {
        success: false,
        error: 'No available drivers within range',
      };
    }

    const nearestDriver = driversInRange[0];

    // Calculate ETA (rough estimate: 5 min pickup + distance/30km*h)
    const distanceToRestaurant = nearestDriver.currentLocation!.distanceTo(restaurantLocation);
    const distanceToCustomer = restaurantLocation.distanceTo(order.deliveryAddress.location);
    const totalDistanceKm = distanceToRestaurant + distanceToCustomer;
    const estimatedMinutes = 5 + (totalDistanceKm / 30) * 60;

    const eta = new Date(Date.now() + estimatedMinutes * 60 * 1000);

    const delivery = Delivery.create({
      orderId: order.id,
      driverId: nearestDriver.id,
      pickupLocation: restaurantLocation,
      deliveryLocation: order.deliveryAddress.location,
      estimatedArrival: eta,
    });

    nearestDriver.startDelivery(order.id);

    return { success: true, delivery };
  }

  updateDriverLocation(driver: Driver, location: GeoLocation): void {
    driver.updateLocation(location);
  }

  completeDelivery(delivery: Delivery): void {
    delivery.complete();
  }

  calculateETA(
    driverLocation: GeoLocation,
    restaurantLocation: GeoLocation,
    customerLocation: GeoLocation
  ): Date {
    const distanceToRestaurant = driverLocation.distanceTo(restaurantLocation);
    const distanceToCustomer = restaurantLocation.distanceTo(customerLocation);
    const totalDistanceKm = distanceToRestaurant + distanceToCustomer;
    
    // Assume average speed of 30 km/h + 5 min pickup time
    const estimatedMinutes = 5 + (totalDistanceKm / 30) * 60;
    
    return new Date(Date.now() + estimatedMinutes * 60 * 1000);
  }
}
