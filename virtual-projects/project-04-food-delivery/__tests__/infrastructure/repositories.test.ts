/**
 * Repository Tests
 * @task TSK-DLV-010, TSK-DLV-011, TSK-DLV-012, TSK-DLV-013
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  Restaurant,
  RestaurantId,
  RestaurantStatus,
  CuisineType,
  MenuItem,
} from '../../src/domain/restaurant';
import {
  Order,
  OrderId,
  OrderStatus,
} from '../../src/domain/order';
import {
  Customer,
  CustomerId,
} from '../../src/domain/customer';
import {
  Driver,
  DriverId,
  DriverStatus,
  VehicleType,
  Delivery,
  DeliveryStatus,
} from '../../src/domain/delivery';
import { GeoLocation, Money, OperatingHours, DayOfWeek, Address } from '../../src/domain/shared';
import {
  InMemoryRestaurantRepository,
  InMemoryOrderRepository,
  InMemoryCustomerRepository,
  InMemoryDriverRepository,
  InMemoryDeliveryRepository,
} from '../../src/infrastructure/repositories';

// ============================================================
// Restaurant Repository Tests
// ============================================================
describe('InMemoryRestaurantRepository', () => {
  let repository: InMemoryRestaurantRepository;
  let restaurant: Restaurant;

  beforeEach(() => {
    repository = new InMemoryRestaurantRepository();
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
  });

  describe('save and findById', () => {
    it('should save and retrieve restaurant', async () => {
      await repository.save(restaurant);
      const found = await repository.findById(restaurant.id);
      expect(found).toBeDefined();
      expect(found!.name).toBe('Test Restaurant');
    });
  });

  describe('findByLocation', () => {
    it('should find restaurants within radius', async () => {
      await repository.save(restaurant);
      const location = new GeoLocation(35.6762, 139.6503);
      const found = await repository.findByLocation(location, 5);
      expect(found.length).toBeGreaterThan(0);
    });

    it('should not find restaurants outside radius', async () => {
      await repository.save(restaurant);
      const farLocation = new GeoLocation(34.0, 135.0);
      const found = await repository.findByLocation(farLocation, 1);
      expect(found.length).toBe(0);
    });
  });

  describe('findByCuisineType', () => {
    it('should find restaurants by cuisine type', async () => {
      await repository.save(restaurant);
      const found = await repository.findByCuisineType(CuisineType.JAPANESE);
      expect(found.length).toBeGreaterThan(0);
      expect(found[0].cuisineType).toBe(CuisineType.JAPANESE);
    });
  });

  describe('findActive', () => {
    it('should only return active restaurants', async () => {
      await repository.save(restaurant);
      const inactive = Restaurant.create({
        name: 'Inactive Restaurant',
        address: new Address('456 Side St', 'Tokyo', '100-0002'),
        location: new GeoLocation(35.0, 139.0),
        phone: '03-9876-5432',
        cuisineType: CuisineType.ITALIAN,
        minimumOrder: new Money(500, 'JPY'),
        deliveryFee: new Money(300, 'JPY'),
        operatingHours: [new OperatingHours(DayOfWeek.MONDAY, '10:00', '20:00')],
      });
      await repository.save(inactive);

      const found = await repository.findActive();
      expect(found.length).toBe(1);
      expect(found[0].status).toBe(RestaurantStatus.ACTIVE);
    });
  });

  describe('delete', () => {
    it('should delete restaurant', async () => {
      await repository.save(restaurant);
      await repository.delete(restaurant.id);
      const found = await repository.findById(restaurant.id);
      expect(found).toBeUndefined();
    });
  });
});

// ============================================================
// Order Repository Tests
// ============================================================
describe('InMemoryOrderRepository', () => {
  let repository: InMemoryOrderRepository;
  let order: Order;

  beforeEach(() => {
    repository = new InMemoryOrderRepository();
    order = Order.create({
      customerId: new CustomerId('cust-1'),
      restaurantId: new RestaurantId('rest-1'),
      items: [{
        menuItemId: 'item-1',
        name: 'Ramen',
        quantity: 2,
        unitPrice: new Money(1200, 'JPY'),
        customizations: [],
        totalPrice: new Money(2400, 'JPY'),
      }],
      deliveryAddress: {
        street: '123 Main St',
        city: 'Tokyo',
        postalCode: '100-0001',
        location: new GeoLocation(35.6762, 139.6503),
      },
      deliveryFee: new Money(300, 'JPY'),
    });
  });

  describe('save and findById', () => {
    it('should save and retrieve order', async () => {
      await repository.save(order);
      const found = await repository.findById(order.id);
      expect(found).toBeDefined();
      expect(found!.id.equals(order.id)).toBe(true);
    });
  });

  describe('findByCustomerId', () => {
    it('should find orders by customer', async () => {
      await repository.save(order);
      const found = await repository.findByCustomerId(new CustomerId('cust-1'));
      expect(found.length).toBeGreaterThan(0);
    });
  });

  describe('findByRestaurantId', () => {
    it('should find orders by restaurant', async () => {
      await repository.save(order);
      const found = await repository.findByRestaurantId(new RestaurantId('rest-1'));
      expect(found.length).toBeGreaterThan(0);
    });
  });

  describe('findByStatus', () => {
    it('should find orders by status', async () => {
      await repository.save(order);
      const found = await repository.findByStatus(OrderStatus.PLACED);
      expect(found.length).toBeGreaterThan(0);
    });
  });
});

// ============================================================
// Customer Repository Tests
// ============================================================
describe('InMemoryCustomerRepository', () => {
  let repository: InMemoryCustomerRepository;
  let customer: Customer;

  beforeEach(() => {
    repository = new InMemoryCustomerRepository();
    customer = Customer.create({
      name: 'John Doe',
      email: 'john@example.com',
      phone: '090-1234-5678',
    });
  });

  describe('save and findById', () => {
    it('should save and retrieve customer', async () => {
      await repository.save(customer);
      const found = await repository.findById(customer.id);
      expect(found).toBeDefined();
      expect(found!.name).toBe('John Doe');
    });
  });

  describe('findByEmail', () => {
    it('should find customer by email', async () => {
      await repository.save(customer);
      const found = await repository.findByEmail('john@example.com');
      expect(found).toBeDefined();
      expect(found!.email).toBe('john@example.com');
    });
  });
});

// ============================================================
// Driver Repository Tests
// ============================================================
describe('InMemoryDriverRepository', () => {
  let repository: InMemoryDriverRepository;
  let driver: Driver;

  beforeEach(() => {
    repository = new InMemoryDriverRepository();
    driver = Driver.create({
      name: 'Driver One',
      phone: '090-1111-2222',
      vehicleType: VehicleType.MOTORCYCLE,
      license: 'DRV-12345',
    });
    driver.updateLocation(new GeoLocation(35.6762, 139.6503));
    driver.goOnline();
  });

  describe('save and findById', () => {
    it('should save and retrieve driver', async () => {
      await repository.save(driver);
      const found = await repository.findById(driver.id);
      expect(found).toBeDefined();
      expect(found!.name).toBe('Driver One');
    });
  });

  describe('findAvailableNearby', () => {
    it('should find available drivers within radius', async () => {
      await repository.save(driver);
      const location = new GeoLocation(35.6762, 139.6503);
      const found = await repository.findAvailableNearby(location, 5);
      expect(found.length).toBeGreaterThan(0);
    });

    it('should not find busy drivers', async () => {
      driver.startDelivery(new OrderId('order-1'));
      await repository.save(driver);
      const location = new GeoLocation(35.6762, 139.6503);
      const found = await repository.findAvailableNearby(location, 5);
      expect(found.length).toBe(0);
    });
  });
});

// ============================================================
// Delivery Repository Tests
// ============================================================
describe('InMemoryDeliveryRepository', () => {
  let repository: InMemoryDeliveryRepository;
  let delivery: Delivery;
  let orderId: OrderId;
  let driverId: DriverId;

  beforeEach(() => {
    repository = new InMemoryDeliveryRepository();
    orderId = new OrderId('order-1');
    driverId = new DriverId('driver-1');
    delivery = Delivery.create({
      orderId,
      driverId,
      pickupLocation: new GeoLocation(35.6762, 139.6503),
      deliveryLocation: new GeoLocation(35.68, 139.66),
      estimatedArrival: new Date(Date.now() + 30 * 60 * 1000), // 30 min from now
    });
  });

  describe('save and findById', () => {
    it('should save and retrieve delivery', async () => {
      await repository.save(delivery);
      const found = await repository.findById(delivery.id);
      expect(found).toBeDefined();
    });
  });

  describe('findByOrderId', () => {
    it('should find delivery by order', async () => {
      await repository.save(delivery);
      const found = await repository.findByOrderId(orderId);
      expect(found).toBeDefined();
    });
  });

  describe('findByDriverId', () => {
    it('should find deliveries by driver', async () => {
      await repository.save(delivery);
      const found = await repository.findByDriverId(driverId);
      expect(found.length).toBeGreaterThan(0);
    });
  });

  describe('findActiveByDriverId', () => {
    it('should find active deliveries', async () => {
      await repository.save(delivery);
      const found = await repository.findActiveByDriverId(driverId);
      expect(found.length).toBeGreaterThan(0);
    });

    it('should not include completed deliveries', async () => {
      delivery.pickup();
      delivery.complete();
      await repository.save(delivery);
      const found = await repository.findActiveByDriverId(driverId);
      expect(found.length).toBe(0);
    });
  });
});
