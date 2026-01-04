/**
 * InMemory Restaurant Repository
 * @design DES-DELIVERY-001 §6.1
 * @task TSK-DLV-010
 */

import {
  Restaurant,
  RestaurantId,
  RestaurantStatus,
  CuisineType,
} from '../../domain/restaurant';
import { GeoLocation } from '../../domain/shared';

export interface RestaurantRepository {
  save(restaurant: Restaurant): Promise<void>;
  findById(id: RestaurantId): Promise<Restaurant | undefined>;
  findByLocation(location: GeoLocation, radiusKm: number): Promise<Restaurant[]>;
  findByCuisineType(cuisineType: CuisineType): Promise<Restaurant[]>;
  findActive(): Promise<Restaurant[]>;
  delete(id: RestaurantId): Promise<void>;
}

export class InMemoryRestaurantRepository implements RestaurantRepository {
  private restaurants: Map<string, Restaurant> = new Map();

  async save(restaurant: Restaurant): Promise<void> {
    this.restaurants.set(restaurant.id.value, restaurant);
  }

  async findById(id: RestaurantId): Promise<Restaurant | undefined> {
    return this.restaurants.get(id.value);
  }

  async findByLocation(location: GeoLocation, radiusKm: number): Promise<Restaurant[]> {
    return Array.from(this.restaurants.values()).filter((restaurant) =>
      location.distanceTo(restaurant.location) <= radiusKm
    );
  }

  async findByCuisineType(cuisineType: CuisineType): Promise<Restaurant[]> {
    return Array.from(this.restaurants.values()).filter((restaurant) =>
      restaurant.cuisineType === cuisineType
    );
  }

  async findActive(): Promise<Restaurant[]> {
    return Array.from(this.restaurants.values()).filter(
      (restaurant) => restaurant.status === RestaurantStatus.ACTIVE
    );
  }

  async delete(id: RestaurantId): Promise<void> {
    this.restaurants.delete(id.value);
  }
}
