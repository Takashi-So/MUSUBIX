/**
 * REST API with Hono
 * @design DES-DELIVERY-001 §9
 * @task TSK-DLV-022 to TSK-DLV-026
 */

import { Hono } from 'hono';
import { cors } from 'hono/cors';

import {
  RestaurantApplicationService,
  OrderApplicationService,
  CustomerApplicationService,
  DeliveryApplicationService,
} from '../application';
import {
  InMemoryRestaurantRepository,
  InMemoryOrderRepository,
  InMemoryCustomerRepository,
  InMemoryDriverRepository,
  InMemoryDeliveryRepository,
} from '../infrastructure/repositories';
import { Driver, VehicleType, DriverId } from '../domain/delivery';
import { CuisineType } from '../domain/restaurant';
import { GeoLocation } from '../domain/shared';

// ============================================================
// Initialize Repositories
// ============================================================
const restaurantRepo = new InMemoryRestaurantRepository();
const orderRepo = new InMemoryOrderRepository();
const customerRepo = new InMemoryCustomerRepository();
const driverRepo = new InMemoryDriverRepository();
const deliveryRepo = new InMemoryDeliveryRepository();

// ============================================================
// Initialize Services
// ============================================================
const restaurantService = new RestaurantApplicationService(restaurantRepo);
const orderService = new OrderApplicationService(orderRepo, restaurantRepo, customerRepo);
const customerService = new CustomerApplicationService(customerRepo);
const deliveryService = new DeliveryApplicationService(deliveryRepo, driverRepo, orderRepo);

// ============================================================
// Create App
// ============================================================
export const app = new Hono();

// Middleware
app.use('*', cors());

// ============================================================
// Health Check
// ============================================================
app.get('/health', (c) => {
  return c.json({ status: 'healthy', timestamp: new Date().toISOString() });
});

// ============================================================
// Restaurant Routes
// ============================================================
app.post('/restaurants', async (c) => {
  const body = await c.req.json();
  const result = await restaurantService.registerRestaurant({
    name: body.name,
    address: body.address,
    phone: body.phone,
    cuisineType: body.cuisineType as CuisineType,
    minimumOrder: body.minimumOrder,
    deliveryFee: body.deliveryFee,
    location: body.location,
  });

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json(
    {
      id: result.restaurant!.id.value,
      name: result.restaurant!.name,
      status: result.restaurant!.status,
    },
    201
  );
});

app.get('/restaurants/search', async (c) => {
  const latitude = parseFloat(c.req.query('latitude') || '0');
  const longitude = parseFloat(c.req.query('longitude') || '0');
  const radiusKm = parseFloat(c.req.query('radiusKm') || '5');
  const cuisineType = c.req.query('cuisineType') as CuisineType | undefined;

  const restaurants = await restaurantService.searchRestaurants({
    latitude,
    longitude,
    radiusKm,
    cuisineType,
  });

  return c.json(
    restaurants.map((r) => ({
      id: r.id.value,
      name: r.name,
      cuisineType: r.cuisineType,
      rating: r.rating,
      deliveryFee: r.deliveryFee.amount,
    }))
  );
});

app.get('/restaurants/:id', async (c) => {
  const id = c.req.param('id');
  const restaurant = await restaurantService.getRestaurantById(id);

  if (!restaurant) {
    return c.json({ error: 'Restaurant not found' }, 404);
  }

  return c.json({
    id: restaurant.id.value,
    name: restaurant.name,
    cuisineType: restaurant.cuisineType,
    status: restaurant.status,
    rating: restaurant.rating,
  });
});

// ============================================================
// Customer Routes
// ============================================================
app.post('/customers', async (c) => {
  const body = await c.req.json();
  const result = await customerService.registerCustomer({
    name: body.name,
    email: body.email,
    phone: body.phone,
    password: body.password,
  });

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json(
    {
      id: result.customer!.id.value,
      name: result.customer!.name,
      email: result.customer!.email,
    },
    201
  );
});

app.get('/customers/:id', async (c) => {
  const id = c.req.param('id');
  const customer = await customerService.getCustomerProfile(id);

  if (!customer) {
    return c.json({ error: 'Customer not found' }, 404);
  }

  return c.json({
    id: customer.id.value,
    name: customer.name,
    email: customer.email,
    phone: customer.phone,
    addresses: customer.addresses.map((a) => ({
      id: a.id.value,
      label: a.label,
      isDefault: a.isDefault,
    })),
  });
});

app.post('/customers/:id/addresses', async (c) => {
  const id = c.req.param('id');
  const body = await c.req.json();
  const result = await customerService.addDeliveryAddress(id, body);

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json({ success: true });
});

// ============================================================
// Order Routes
// ============================================================
app.post('/orders', async (c) => {
  const body = await c.req.json();
  const result = await orderService.placeOrder({
    customerId: body.customerId,
    restaurantId: body.restaurantId,
    items: body.items,
    deliveryAddress: body.deliveryAddress,
  });

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json(
    {
      id: result.order!.id.value,
      status: result.order!.status,
      total: result.order!.total.amount,
    },
    201
  );
});

app.get('/orders/:id', async (c) => {
  const id = c.req.param('id');
  const order = await orderService.getOrderById(id);

  if (!order) {
    return c.json({ error: 'Order not found' }, 404);
  }

  return c.json({
    id: order.id.value,
    status: order.status,
    total: order.total.amount,
    placedAt: order.placedAt,
  });
});

app.post('/orders/:id/cancel', async (c) => {
  const id = c.req.param('id');
  const body = await c.req.json();
  const result = await orderService.cancelOrder(id, body.reason);

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json({ success: true });
});

app.get('/customers/:id/orders', async (c) => {
  const id = c.req.param('id');
  const orders = await orderService.getOrderHistory(id);

  return c.json(
    orders.map((o) => ({
      id: o.id.value,
      status: o.status,
      total: o.total.amount,
      placedAt: o.placedAt,
    }))
  );
});

// ============================================================
// Driver Routes
// ============================================================
app.post('/drivers', async (c) => {
  const body = await c.req.json();
  
  try {
    const driver = Driver.create({
      name: body.name,
      phone: body.phone,
      vehicleType: body.vehicleType as VehicleType,
      license: body.license,
    });

    await driverRepo.save(driver);

    return c.json(
      {
        id: driver.id.value,
        name: driver.name,
        status: driver.status,
        vehicleType: driver.vehicleType,
      },
      201
    );
  } catch (error) {
    return c.json(
      { error: error instanceof Error ? error.message : 'Registration failed' },
      400
    );
  }
});

app.put('/drivers/:id/location', async (c) => {
  const id = c.req.param('id');
  const body = await c.req.json();
  const result = await deliveryService.updateDriverLocation(
    id,
    body.latitude,
    body.longitude
  );

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json({ success: true });
});

app.put('/drivers/:id/status', async (c) => {
  const id = c.req.param('id');
  const body = await c.req.json();

  try {
    const driver = await driverRepo.findById(new DriverId(id));
    if (!driver) {
      return c.json({ error: 'Driver not found' }, 404);
    }

    if (body.status === 'AVAILABLE') {
      driver.goOnline();
    } else if (body.status === 'OFFLINE') {
      driver.goOffline();
    }

    await driverRepo.save(driver);
    return c.json({ success: true });
  } catch (error) {
    return c.json(
      { error: error instanceof Error ? error.message : 'Status update failed' },
      400
    );
  }
});

// ============================================================
// Delivery Routes
// ============================================================
app.post('/deliveries/assign', async (c) => {
  const body = await c.req.json();
  const result = await deliveryService.assignDelivery({
    orderId: body.orderId,
    pickupLocation: body.pickupLocation,
    deliveryLocation: body.deliveryLocation,
  });

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json(
    {
      id: result.delivery!.id.value,
      status: result.delivery!.status,
      estimatedArrival: result.delivery!.estimatedArrival,
    },
    201
  );
});

app.post('/deliveries/:id/complete', async (c) => {
  const id = c.req.param('id');
  const result = await deliveryService.completeDelivery(id);

  if (!result.success) {
    return c.json({ error: result.error }, 400);
  }

  return c.json({ success: true });
});

app.get('/orders/:id/delivery', async (c) => {
  const id = c.req.param('id');
  const delivery = await deliveryService.getDeliveryByOrderId(id);

  if (!delivery) {
    return c.json({ error: 'Delivery not found' }, 404);
  }

  return c.json({
    id: delivery.id.value,
    status: delivery.status,
    estimatedArrival: delivery.estimatedArrival,
  });
});

export default app;
