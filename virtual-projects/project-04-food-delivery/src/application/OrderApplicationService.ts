/**
 * Order Application Service
 * @design DES-DELIVERY-001 §7.2
 * @task TSK-DLV-015
 */

import {
  Order,
  OrderId,
  OrderItem,
} from '../domain/order';
import { CustomerId } from '../domain/customer';
import { RestaurantId } from '../domain/restaurant';
import {
  OrderRepository,
  RestaurantRepository,
  CustomerRepository,
} from '../infrastructure/repositories';
import { GeoLocation, Money } from '../domain/shared';

export interface PlaceOrderCommand {
  customerId: string;
  restaurantId: string;
  items: Array<{
    menuItemId: string;
    name: string;
    quantity: number;
    unitPrice: number;
  }>;
  deliveryAddress: {
    street: string;
    city: string;
    postalCode: string;
    latitude: number;
    longitude: number;
    instructions?: string;
  };
}

export interface PlaceOrderResult {
  success: boolean;
  order?: Order;
  error?: string;
}

export interface CancelOrderResult {
  success: boolean;
  error?: string;
}

export class OrderApplicationService {
  constructor(
    private readonly orderRepo: OrderRepository,
    private readonly restaurantRepo: RestaurantRepository,
    private readonly customerRepo: CustomerRepository
  ) {}

  async placeOrder(command: PlaceOrderCommand): Promise<PlaceOrderResult> {
    try {
      // Verify restaurant exists
      const restaurant = await this.restaurantRepo.findById(
        new RestaurantId(command.restaurantId)
      );
      if (!restaurant) {
        return { success: false, error: 'Restaurant not found' };
      }

      // Verify customer exists
      const customer = await this.customerRepo.findById(
        new CustomerId(command.customerId)
      );
      if (!customer) {
        return { success: false, error: 'Customer not found' };
      }

      // Create order items
      const orderItems: OrderItem[] = command.items.map((item) => ({
        menuItemId: item.menuItemId,
        name: item.name,
        quantity: item.quantity,
        unitPrice: new Money(item.unitPrice, 'JPY'),
        customizations: [],
        totalPrice: new Money(item.unitPrice * item.quantity, 'JPY'),
      }));

      // Create order
      const order = Order.create({
        customerId: new CustomerId(command.customerId),
        restaurantId: new RestaurantId(command.restaurantId),
        items: orderItems,
        deliveryAddress: {
          street: command.deliveryAddress.street,
          city: command.deliveryAddress.city,
          postalCode: command.deliveryAddress.postalCode,
          location: new GeoLocation(
            command.deliveryAddress.latitude,
            command.deliveryAddress.longitude
          ),
          instructions: command.deliveryAddress.instructions,
        },
        deliveryFee: restaurant.deliveryFee,
      });

      await this.orderRepo.save(order);
      return { success: true, order };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Order placement failed',
      };
    }
  }

  async cancelOrder(orderId: string, reason: string): Promise<CancelOrderResult> {
    try {
      const order = await this.orderRepo.findById(new OrderId(orderId));
      if (!order) {
        return { success: false, error: 'Order not found' };
      }

      order.cancel(reason);
      await this.orderRepo.save(order);
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Cancellation failed',
      };
    }
  }

  async getOrderById(orderId: string): Promise<Order | undefined> {
    return this.orderRepo.findById(new OrderId(orderId));
  }

  async getOrderHistory(customerId: string): Promise<Order[]> {
    return this.orderRepo.findByCustomerId(new CustomerId(customerId));
  }
}
