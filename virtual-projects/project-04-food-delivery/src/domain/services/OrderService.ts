/**
 * Order Domain Service
 * @design DES-DELIVERY-001 §5.1
 * @task TSK-DLV-007
 */

import { Order, OrderItem } from '../order';
import { Restaurant } from '../restaurant';
import { Customer, DeliveryAddress } from '../customer';

export interface CreateOrderResult {
  success: boolean;
  order?: Order;
  error?: string;
}

export interface AcceptOrderResult {
  success: boolean;
  error?: string;
}

export interface CancelOrderResult {
  success: boolean;
  requiresRefund: boolean;
  error?: string;
}

export class OrderService {
  createOrder(
    customer: Customer,
    restaurant: Restaurant,
    items: OrderItem[],
    deliveryAddress: DeliveryAddress
  ): CreateOrderResult {
    // Calculate subtotal
    let subtotal = items.reduce(
      (sum, item) => sum.add(item.totalPrice),
      items[0].totalPrice.subtract(items[0].totalPrice) // 0 money
    );

    // Check restaurant can accept order
    if (!restaurant.canAcceptOrder(subtotal)) {
      return {
        success: false,
        error: `Order is below minimum amount or restaurant is not accepting orders`,
      };
    }

    try {
      const order = Order.create({
        customerId: customer.id,
        restaurantId: restaurant.id,
        items,
        deliveryAddress: {
          street: deliveryAddress.street,
          city: deliveryAddress.city,
          postalCode: deliveryAddress.postalCode,
          location: deliveryAddress.location,
          instructions: deliveryAddress.instructions,
        },
        deliveryFee: restaurant.deliveryFee,
      });

      return { success: true, order };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Failed to create order',
      };
    }
  }

  acceptOrder(order: Order, restaurant: Restaurant): AcceptOrderResult {
    if (!order.restaurantId.equals(restaurant.id)) {
      return { success: false, error: 'Order does not belong to this restaurant' };
    }

    try {
      order.accept();
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Failed to accept order',
      };
    }
  }

  cancelOrder(order: Order, reason: string): CancelOrderResult {
    const requiresRefund = !order.canBeCancelledByCustomer(); // If already accepted, needs refund

    try {
      order.cancel(reason);
      return { success: true, requiresRefund };
    } catch (error) {
      return {
        success: false,
        requiresRefund: false,
        error: error instanceof Error ? error.message : 'Failed to cancel order',
      };
    }
  }
}
