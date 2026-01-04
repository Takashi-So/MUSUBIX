/**
 * Restaurant Application Service
 * @design DES-DELIVERY-001 §7.1
 * @task TSK-DLV-014
 */

import {
  Restaurant,
  RestaurantId,
  CuisineType,
} from '../domain/restaurant';
import { RestaurantRepository } from '../infrastructure/repositories';
import { GeoLocation, Money, Address, OperatingHours, DayOfWeek } from '../domain/shared';

export interface RegisterRestaurantCommand {
  name: string;
  address: { street: string; city: string; postalCode: string };
  phone: string;
  cuisineType: CuisineType;
  minimumOrder: number;
  deliveryFee: number;
  location?: { latitude: number; longitude: number };
}

export interface SearchRestaurantsQuery {
  latitude: number;
  longitude: number;
  radiusKm: number;
  cuisineType?: CuisineType;
}

export interface RegisterRestaurantResult {
  success: boolean;
  restaurant?: Restaurant;
  error?: string;
}

export interface ActivateRestaurantResult {
  success: boolean;
  error?: string;
}

export class RestaurantApplicationService {
  constructor(private readonly restaurantRepo: RestaurantRepository) {}

  async registerRestaurant(
    command: RegisterRestaurantCommand
  ): Promise<RegisterRestaurantResult> {
    try {
      const location = command.location
        ? new GeoLocation(command.location.latitude, command.location.longitude)
        : new GeoLocation(35.6762, 139.6503); // Default Tokyo

      const restaurant = Restaurant.create({
        name: command.name,
        address: new Address(
          command.address.street,
          command.address.city,
          command.address.postalCode
        ),
        location,
        phone: command.phone,
        cuisineType: command.cuisineType,
        minimumOrder: new Money(command.minimumOrder, 'JPY'),
        deliveryFee: new Money(command.deliveryFee, 'JPY'),
        operatingHours: [
          new OperatingHours(DayOfWeek.MONDAY, '09:00', '22:00'),
          new OperatingHours(DayOfWeek.TUESDAY, '09:00', '22:00'),
          new OperatingHours(DayOfWeek.WEDNESDAY, '09:00', '22:00'),
          new OperatingHours(DayOfWeek.THURSDAY, '09:00', '22:00'),
          new OperatingHours(DayOfWeek.FRIDAY, '09:00', '22:00'),
          new OperatingHours(DayOfWeek.SATURDAY, '10:00', '22:00'),
          new OperatingHours(DayOfWeek.SUNDAY, '10:00', '21:00'),
        ],
      });

      await this.restaurantRepo.save(restaurant);
      return { success: true, restaurant };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Registration failed',
      };
    }
  }

  async activateRestaurant(restaurantId: string): Promise<ActivateRestaurantResult> {
    try {
      const restaurant = await this.restaurantRepo.findById(
        new RestaurantId(restaurantId)
      );

      if (!restaurant) {
        return { success: false, error: 'Restaurant not found' };
      }

      restaurant.activate();
      await this.restaurantRepo.save(restaurant);
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Activation failed',
      };
    }
  }

  async searchRestaurants(query: SearchRestaurantsQuery): Promise<Restaurant[]> {
    const location = new GeoLocation(query.latitude, query.longitude);
    let restaurants = await this.restaurantRepo.findByLocation(
      location,
      query.radiusKm
    );

    if (query.cuisineType) {
      restaurants = restaurants.filter(
        (r) => r.cuisineType === query.cuisineType
      );
    }

    return restaurants;
  }

  async getRestaurantById(id: string): Promise<Restaurant | undefined> {
    return this.restaurantRepo.findById(new RestaurantId(id));
  }
}
