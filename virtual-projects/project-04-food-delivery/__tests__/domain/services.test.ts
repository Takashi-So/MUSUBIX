/**
 * Domain Services Tests
 * @task TSK-DLV-007, TSK-DLV-008, TSK-DLV-009
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { OrderService } from '../../src/domain/services/OrderService';
import { DeliveryService } from '../../src/domain/services/DeliveryService';
import { PaymentService } from '../../src/domain/services/PaymentService';
import { Restaurant, RestaurantId, CuisineType, MenuItem } from '../../src/domain/restaurant';
import { Customer, CustomerId, DeliveryAddress } from '../../src/domain/customer';
import { Order, OrderItem, OrderStatus } from '../../src/domain/order';
import { Driver, DriverStatus, VehicleType, Delivery, DeliveryStatus } from '../../src/domain/delivery';
import { Money, GeoLocation, Address, OperatingHours, DayOfWeek } from '../../src/domain/shared';

// ============================================================
// OrderService Tests
// ============================================================
describe('OrderService', () => {
  let orderService: OrderService;
  let restaurant: Restaurant;
  let customer: Customer;
  let menuItems: MenuItem[];

  beforeEach(() => {
    orderService = new OrderService();

    restaurant = Restaurant.create({
      name: 'Test Restaurant',
      address: new Address('1-2-3 Test', 'Tokyo', '100-0001'),
      location: new GeoLocation(35.6812, 139.7671),
      phone: '03-1234-5678',
      cuisineType: CuisineType.JAPANESE,
      minimumOrder: new Money(1000),
      deliveryFee: new Money(300),
      operatingHours: [
        new OperatingHours(DayOfWeek.MONDAY, '09:00', '22:00'),
      ],
    });
    restaurant.activate();

    customer = Customer.create({
      name: 'Test Customer',
      email: 'test@example.com',
      phone: '090-1234-5678',
    });

    const address = DeliveryAddress.create({
      label: 'Home',
      street: '4-5-6 Home',
      city: 'Tokyo',
      postalCode: '150-0001',
      location: new GeoLocation(35.6580, 139.7016),
    });
    customer.addAddress(address);

    menuItems = [
      MenuItem.create({
        restaurantId: restaurant.id,
        name: 'Ramen',
        description: 'Delicious ramen',
        price: new Money(1000),
        category: 'Main',
      }),
    ];
  });

  describe('createOrder', () => {
    it('should create order when all conditions are met', () => {
      const orderItems: OrderItem[] = [
        {
          menuItemId: menuItems[0].id.value,
          name: menuItems[0].name,
          quantity: 2,
          unitPrice: menuItems[0].price,
          customizations: [],
          totalPrice: menuItems[0].price.multiply(2),
        },
      ];

      const result = orderService.createOrder(
        customer,
        restaurant,
        orderItems,
        customer.getDefaultAddress()!
      );

      expect(result.success).toBe(true);
      expect(result.order).toBeDefined();
      expect(result.order!.status).toBe(OrderStatus.PLACED);
    });

    it('should reject order below minimum amount', () => {
      const orderItems: OrderItem[] = [
        {
          menuItemId: menuItems[0].id.value,
          name: menuItems[0].name,
          quantity: 1,
          unitPrice: new Money(500),
          customizations: [],
          totalPrice: new Money(500),
        },
      ];

      const result = orderService.createOrder(
        customer,
        restaurant,
        orderItems,
        customer.getDefaultAddress()!
      );

      expect(result.success).toBe(false);
      expect(result.error).toContain('minimum');
    });

    it('should reject order when restaurant is not active', () => {
      restaurant.suspend();

      const orderItems: OrderItem[] = [
        {
          menuItemId: menuItems[0].id.value,
          name: menuItems[0].name,
          quantity: 2,
          unitPrice: new Money(1000),
          customizations: [],
          totalPrice: new Money(2000),
        },
      ];

      const result = orderService.createOrder(
        customer,
        restaurant,
        orderItems,
        customer.getDefaultAddress()!
      );

      expect(result.success).toBe(false);
      expect(result.error).toContain('not accepting');
    });
  });

  describe('acceptOrder', () => {
    it('should accept order when restaurant is valid', () => {
      const orderItems: OrderItem[] = [
        {
          menuItemId: menuItems[0].id.value,
          name: 'Test',
          quantity: 2,
          unitPrice: new Money(1000),
          customizations: [],
          totalPrice: new Money(2000),
        },
      ];

      const createResult = orderService.createOrder(
        customer,
        restaurant,
        orderItems,
        customer.getDefaultAddress()!
      );

      const result = orderService.acceptOrder(createResult.order!, restaurant);
      expect(result.success).toBe(true);
      expect(createResult.order!.status).toBe(OrderStatus.ACCEPTED);
    });
  });

  describe('cancelOrder', () => {
    it('should allow cancellation when order is PLACED', () => {
      const orderItems: OrderItem[] = [
        {
          menuItemId: menuItems[0].id.value,
          name: 'Test',
          quantity: 2,
          unitPrice: new Money(1000),
          customizations: [],
          totalPrice: new Money(2000),
        },
      ];

      const createResult = orderService.createOrder(
        customer,
        restaurant,
        orderItems,
        customer.getDefaultAddress()!
      );

      const result = orderService.cancelOrder(createResult.order!, 'Changed mind');
      expect(result.success).toBe(true);
      expect(createResult.order!.status).toBe(OrderStatus.CANCELLED);
    });
  });
});

// ============================================================
// DeliveryService Tests
// ============================================================
describe('DeliveryService', () => {
  let deliveryService: DeliveryService;
  let order: Order;
  let drivers: Driver[];
  const restaurantLocation = new GeoLocation(35.6812, 139.7671);

  beforeEach(() => {
    deliveryService = new DeliveryService();

    order = Order.create({
      customerId: new CustomerId('cust-1'),
      restaurantId: new RestaurantId('res-1'),
      items: [
        {
          menuItemId: 'item-1',
          name: 'Test Item',
          quantity: 1,
          unitPrice: new Money(1000),
          customizations: [],
          totalPrice: new Money(1000),
        },
      ],
      deliveryAddress: {
        street: '1-2-3 Customer',
        city: 'Tokyo',
        postalCode: '150-0001',
        location: new GeoLocation(35.6580, 139.7016),
      },
      deliveryFee: new Money(300),
    });
    order.accept();
    order.startPreparing();
    order.markReady();

    drivers = [
      Driver.create({
        name: 'Near Driver',
        phone: '090-0001-0001',
        vehicleType: VehicleType.MOTORCYCLE,
        license: 'LICENSE-1',
      }),
      Driver.create({
        name: 'Far Driver',
        phone: '090-0002-0002',
        vehicleType: VehicleType.CAR,
        license: 'LICENSE-2',
      }),
    ];

    // Near driver - 1km away
    drivers[0].goOnline();
    drivers[0].updateLocation(new GeoLocation(35.6850, 139.7700));

    // Far driver - 10km away
    drivers[1].goOnline();
    drivers[1].updateLocation(new GeoLocation(35.7500, 139.8000));
  });

  describe('assignDriver', () => {
    it('should assign nearest available driver', () => {
      const result = deliveryService.assignDriver(order, drivers, restaurantLocation);

      expect(result.success).toBe(true);
      expect(result.delivery).toBeDefined();
      expect(result.delivery!.driverId.equals(drivers[0].id)).toBe(true);
    });

    it('should reject when no drivers available', () => {
      drivers.forEach((d) => d.goOffline());

      const result = deliveryService.assignDriver(order, drivers, restaurantLocation);

      expect(result.success).toBe(false);
      expect(result.error).toContain('No available drivers');
    });

    it('should reject drivers beyond radius', () => {
      // All drivers far away
      drivers[0].updateLocation(new GeoLocation(36.0000, 140.0000)); // Very far

      const result = deliveryService.assignDriver(order, [drivers[0]], restaurantLocation);

      expect(result.success).toBe(false);
    });
  });

  describe('completeDelivery', () => {
    it('should complete delivery', () => {
      const assignResult = deliveryService.assignDriver(order, drivers, restaurantLocation);
      assignResult.delivery!.pickup();

      deliveryService.completeDelivery(assignResult.delivery!);

      expect(assignResult.delivery!.status).toBe(DeliveryStatus.DELIVERED);
    });
  });
});

// ============================================================
// PaymentService Tests
// ============================================================
describe('PaymentService', () => {
  let paymentService: PaymentService;
  let order: Order;

  beforeEach(() => {
    paymentService = new PaymentService();

    order = Order.create({
      customerId: new CustomerId('cust-1'),
      restaurantId: new RestaurantId('res-1'),
      items: [
        {
          menuItemId: 'item-1',
          name: 'Test Item',
          quantity: 1,
          unitPrice: new Money(1000),
          customizations: [],
          totalPrice: new Money(1000),
        },
      ],
      deliveryAddress: {
        street: '1-2-3 Test',
        city: 'Tokyo',
        postalCode: '100-0001',
        location: new GeoLocation(35.6812, 139.7671),
      },
      deliveryFee: new Money(300),
    });
  });

  describe('processPayment', () => {
    it('should process credit card payment', () => {
      const result = paymentService.processPayment(order, 'CREDIT_CARD');

      expect(result.success).toBe(true);
      expect(result.payment).toBeDefined();
      expect(result.payment!.amount.equals(order.total)).toBe(true);
    });

    it('should process cash payment', () => {
      const result = paymentService.processPayment(order, 'CASH');

      expect(result.success).toBe(true);
      expect(result.payment!.method).toBe('CASH');
    });
  });

  describe('refundPayment', () => {
    it('should refund completed payment', () => {
      const processResult = paymentService.processPayment(order, 'CREDIT_CARD');
      processResult.payment!.complete();

      const refundResult = paymentService.refundPayment(processResult.payment!, 'Order cancelled');

      expect(refundResult.success).toBe(true);
    });
  });
});
