/**
 * Application Services Tests
 * @task TSK-DLV-014, TSK-DLV-015, TSK-DLV-016, TSK-DLV-017
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  OrderApplicationService,
  RestaurantApplicationService,
  DeliveryApplicationService,
  CustomerApplicationService,
} from '../../src/application';
import {
  InMemoryRestaurantRepository,
  InMemoryOrderRepository,
  InMemoryCustomerRepository,
  InMemoryDriverRepository,
  InMemoryDeliveryRepository,
} from '../../src/infrastructure/repositories';
import {
  Restaurant,
  RestaurantId,
  CuisineType,
  MenuItem,
} from '../../src/domain/restaurant';
import { Customer, CustomerId } from '../../src/domain/customer';
import { Driver, DriverId, VehicleType, Delivery } from '../../src/domain/delivery';
import { Order, OrderId, OrderStatus } from '../../src/domain/order';
import { GeoLocation, Money, OperatingHours, DayOfWeek, Address } from '../../src/domain/shared';

// ============================================================
// Restaurant Application Service Tests
// ============================================================
describe('RestaurantApplicationService', () => {
  let service: RestaurantApplicationService;
  let restaurantRepo: InMemoryRestaurantRepository;

  beforeEach(() => {
    restaurantRepo = new InMemoryRestaurantRepository();
    service = new RestaurantApplicationService(restaurantRepo);
  });

  describe('registerRestaurant', () => {
    it('should register new restaurant', async () => {
      const result = await service.registerRestaurant({
        name: 'Test Restaurant',
        address: { street: '123 Main St', city: 'Tokyo', postalCode: '100-0001' },
        phone: '03-1234-5678',
        cuisineType: CuisineType.JAPANESE,
        minimumOrder: 500,
        deliveryFee: 300,
      });

      expect(result.success).toBe(true);
      expect(result.restaurant).toBeDefined();
      expect(result.restaurant!.name).toBe('Test Restaurant');
    });
  });

  describe('activateRestaurant', () => {
    it('should activate pending restaurant', async () => {
      const registerResult = await service.registerRestaurant({
        name: 'Test Restaurant',
        address: { street: '123 Main St', city: 'Tokyo', postalCode: '100-0001' },
        phone: '03-1234-5678',
        cuisineType: CuisineType.JAPANESE,
        minimumOrder: 500,
        deliveryFee: 300,
      });

      const result = await service.activateRestaurant(registerResult.restaurant!.id.value);
      expect(result.success).toBe(true);
    });
  });

  describe('searchRestaurants', () => {
    it('should find restaurants by location', async () => {
      await service.registerRestaurant({
        name: 'Test Restaurant',
        address: { street: '123 Main St', city: 'Tokyo', postalCode: '100-0001' },
        phone: '03-1234-5678',
        cuisineType: CuisineType.JAPANESE,
        minimumOrder: 500,
        deliveryFee: 300,
        location: { latitude: 35.6762, longitude: 139.6503 },
      });

      const results = await service.searchRestaurants({
        latitude: 35.6762,
        longitude: 139.6503,
        radiusKm: 5,
      });

      expect(results.length).toBeGreaterThan(0);
    });
  });
});

// ============================================================
// Order Application Service Tests
// ============================================================
describe('OrderApplicationService', () => {
  let service: OrderApplicationService;
  let orderRepo: InMemoryOrderRepository;
  let restaurantRepo: InMemoryRestaurantRepository;
  let customerRepo: InMemoryCustomerRepository;
  let restaurant: Restaurant;
  let customer: Customer;

  beforeEach(async () => {
    orderRepo = new InMemoryOrderRepository();
    restaurantRepo = new InMemoryRestaurantRepository();
    customerRepo = new InMemoryCustomerRepository();
    service = new OrderApplicationService(orderRepo, restaurantRepo, customerRepo);

    // Create test restaurant
    restaurant = Restaurant.create({
      name: 'Test Restaurant',
      address: new Address('123 Main St', 'Tokyo', '100-0001'),
      location: new GeoLocation(35.6762, 139.6503),
      phone: '03-1234-5678',
      cuisineType: CuisineType.JAPANESE,
      minimumOrder: new Money(500, 'JPY'),
      deliveryFee: new Money(300, 'JPY'),
      operatingHours: [new OperatingHours(DayOfWeek.MONDAY, '09:00', '22:00')],
    });
    restaurant.activate();
    await restaurantRepo.save(restaurant);

    // Create test customer
    customer = Customer.create({
      name: 'John Doe',
      email: 'john@example.com',
      phone: '090-1234-5678',
    });
    await customerRepo.save(customer);
  });

  describe('placeOrder', () => {
    it('should place order successfully', async () => {
      const result = await service.placeOrder({
        customerId: customer.id.value,
        restaurantId: restaurant.id.value,
        items: [
          { menuItemId: 'item-1', name: 'Ramen', quantity: 2, unitPrice: 1200 },
        ],
        deliveryAddress: {
          street: '456 Side St',
          city: 'Tokyo',
          postalCode: '100-0002',
          latitude: 35.68,
          longitude: 139.66,
        },
      });

      expect(result.success).toBe(true);
      expect(result.order).toBeDefined();
    });
  });

  describe('cancelOrder', () => {
    it('should cancel pending order', async () => {
      const placeResult = await service.placeOrder({
        customerId: customer.id.value,
        restaurantId: restaurant.id.value,
        items: [
          { menuItemId: 'item-1', name: 'Ramen', quantity: 1, unitPrice: 1200 },
        ],
        deliveryAddress: {
          street: '456 Side St',
          city: 'Tokyo',
          postalCode: '100-0002',
          latitude: 35.68,
          longitude: 139.66,
        },
      });

      const result = await service.cancelOrder(
        placeResult.order!.id.value,
        'Changed my mind'
      );
      expect(result.success).toBe(true);
    });
  });

  describe('getOrderHistory', () => {
    it('should get customer order history', async () => {
      await service.placeOrder({
        customerId: customer.id.value,
        restaurantId: restaurant.id.value,
        items: [
          { menuItemId: 'item-1', name: 'Ramen', quantity: 1, unitPrice: 1200 },
        ],
        deliveryAddress: {
          street: '456 Side St',
          city: 'Tokyo',
          postalCode: '100-0002',
          latitude: 35.68,
          longitude: 139.66,
        },
      });

      const orders = await service.getOrderHistory(customer.id.value);
      expect(orders.length).toBeGreaterThan(0);
    });
  });
});

// ============================================================
// Delivery Application Service Tests
// ============================================================
describe('DeliveryApplicationService', () => {
  let service: DeliveryApplicationService;
  let deliveryRepo: InMemoryDeliveryRepository;
  let driverRepo: InMemoryDriverRepository;
  let orderRepo: InMemoryOrderRepository;
  let driver: Driver;

  beforeEach(async () => {
    deliveryRepo = new InMemoryDeliveryRepository();
    driverRepo = new InMemoryDriverRepository();
    orderRepo = new InMemoryOrderRepository();
    service = new DeliveryApplicationService(deliveryRepo, driverRepo, orderRepo);

    // Create test driver
    driver = Driver.create({
      name: 'Driver One',
      phone: '090-1111-2222',
      vehicleType: VehicleType.MOTORCYCLE,
      license: 'DRV-12345',
    });
    driver.updateLocation(new GeoLocation(35.6762, 139.6503));
    driver.goOnline();
    await driverRepo.save(driver);
  });

  describe('assignDelivery', () => {
    it('should assign driver to order', async () => {
      const orderId = OrderId.generate();
      const result = await service.assignDelivery({
        orderId: orderId.value,
        pickupLocation: { latitude: 35.6762, longitude: 139.6503 },
        deliveryLocation: { latitude: 35.68, longitude: 139.66 },
      });

      expect(result.success).toBe(true);
      expect(result.delivery).toBeDefined();
    });
  });

  describe('updateDriverLocation', () => {
    it('should update driver location', async () => {
      const result = await service.updateDriverLocation(
        driver.id.value,
        35.68,
        139.66
      );
      expect(result.success).toBe(true);
    });
  });

  describe('completeDelivery', () => {
    it('should complete delivery', async () => {
      const orderId = OrderId.generate();
      const assignResult = await service.assignDelivery({
        orderId: orderId.value,
        pickupLocation: { latitude: 35.6762, longitude: 139.6503 },
        deliveryLocation: { latitude: 35.68, longitude: 139.66 },
      });

      // Simulate pickup
      assignResult.delivery!.pickup();
      await deliveryRepo.save(assignResult.delivery!);

      const result = await service.completeDelivery(assignResult.delivery!.id.value);
      expect(result.success).toBe(true);
    });
  });
});

// ============================================================
// Customer Application Service Tests
// ============================================================
describe('CustomerApplicationService', () => {
  let service: CustomerApplicationService;
  let customerRepo: InMemoryCustomerRepository;

  beforeEach(() => {
    customerRepo = new InMemoryCustomerRepository();
    service = new CustomerApplicationService(customerRepo);
  });

  describe('registerCustomer', () => {
    it('should register new customer', async () => {
      const result = await service.registerCustomer({
        name: 'John Doe',
        email: 'john@example.com',
        phone: '090-1234-5678',
      });

      expect(result.success).toBe(true);
      expect(result.customer).toBeDefined();
    });
  });

  describe('addDeliveryAddress', () => {
    it('should add delivery address to customer', async () => {
      const registerResult = await service.registerCustomer({
        name: 'John Doe',
        email: 'john@example.com',
        phone: '090-1234-5678',
      });

      const result = await service.addDeliveryAddress(
        registerResult.customer!.id.value,
        {
          label: 'Home',
          street: '123 Main St',
          city: 'Tokyo',
          postalCode: '100-0001',
          latitude: 35.6762,
          longitude: 139.6503,
        }
      );

      expect(result.success).toBe(true);
    });
  });

  describe('getCustomerProfile', () => {
    it('should get customer profile', async () => {
      const registerResult = await service.registerCustomer({
        name: 'John Doe',
        email: 'john@example.com',
        phone: '090-1234-5678',
      });

      const profile = await service.getCustomerProfile(
        registerResult.customer!.id.value
      );
      expect(profile).toBeDefined();
      expect(profile!.name).toBe('John Doe');
    });
  });
});
