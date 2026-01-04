/**
 * REST API Tests
 * @task TSK-DLV-022, TSK-DLV-023, TSK-DLV-024, TSK-DLV-025, TSK-DLV-026
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { app } from '../../src/api/app';

describe('REST API', () => {
  // ============================================================
  // Restaurant Endpoints
  // ============================================================
  describe('Restaurant Endpoints', () => {
    describe('POST /restaurants', () => {
      it('should register new restaurant', async () => {
        const response = await app.request('/restaurants', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            name: 'Test Restaurant',
            address: { street: '123 Main St', city: 'Tokyo', postalCode: '100-0001' },
            phone: '03-1234-5678',
            cuisineType: 'JAPANESE',
            minimumOrder: 500,
            deliveryFee: 300,
          }),
        });

        expect(response.status).toBe(201);
        const data = await response.json();
        expect(data.name).toBe('Test Restaurant');
      });
    });

    describe('GET /restaurants/search', () => {
      it('should search restaurants by location', async () => {
        // First create a restaurant
        await app.request('/restaurants', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            name: 'Tokyo Ramen',
            address: { street: '123 Main St', city: 'Tokyo', postalCode: '100-0001' },
            phone: '03-1234-5678',
            cuisineType: 'JAPANESE',
            minimumOrder: 500,
            deliveryFee: 300,
            location: { latitude: 35.6762, longitude: 139.6503 },
          }),
        });

        const response = await app.request(
          '/restaurants/search?latitude=35.6762&longitude=139.6503&radiusKm=5',
          { method: 'GET' }
        );

        expect(response.status).toBe(200);
        const data = await response.json();
        expect(Array.isArray(data)).toBe(true);
      });
    });
  });

  // ============================================================
  // Customer Endpoints
  // ============================================================
  describe('Customer Endpoints', () => {
    describe('POST /customers', () => {
      it('should register new customer', async () => {
        const response = await app.request('/customers', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            name: 'John Doe',
            email: 'john@example.com',
            phone: '090-1234-5678',
          }),
        });

        expect(response.status).toBe(201);
        const data = await response.json();
        expect(data.name).toBe('John Doe');
      });
    });

    describe('GET /customers/:id', () => {
      it('should get customer profile', async () => {
        // Create customer first
        const createResponse = await app.request('/customers', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            name: 'Jane Doe',
            email: 'jane@example.com',
            phone: '090-9876-5432',
          }),
        });
        const created = await createResponse.json();

        const response = await app.request(`/customers/${created.id}`, {
          method: 'GET',
        });

        expect(response.status).toBe(200);
        const data = await response.json();
        expect(data.email).toBe('jane@example.com');
      });
    });
  });

  // ============================================================
  // Order Endpoints
  // ============================================================
  describe('Order Endpoints', () => {
    let customerId: string;
    let restaurantId: string;

    beforeEach(async () => {
      // Create test customer
      const customerRes = await app.request('/customers', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          name: 'Order Test Customer',
          email: `test-${Date.now()}@example.com`,
          phone: '090-1234-5678',
        }),
      });
      const customer = await customerRes.json();
      customerId = customer.id;

      // Create test restaurant
      const restaurantRes = await app.request('/restaurants', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          name: 'Order Test Restaurant',
          address: { street: '123 Main St', city: 'Tokyo', postalCode: '100-0001' },
          phone: '03-1234-5678',
          cuisineType: 'JAPANESE',
          minimumOrder: 500,
          deliveryFee: 300,
        }),
      });
      const restaurant = await restaurantRes.json();
      restaurantId = restaurant.id;
    });

    describe('POST /orders', () => {
      it('should place new order', async () => {
        const response = await app.request('/orders', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            customerId,
            restaurantId,
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
          }),
        });

        expect(response.status).toBe(201);
        const data = await response.json();
        expect(data.id).toBeDefined();
      });
    });

    describe('POST /orders/:id/cancel', () => {
      it('should cancel pending order', async () => {
        // Create order first
        const createResponse = await app.request('/orders', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            customerId,
            restaurantId,
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
          }),
        });
        const order = await createResponse.json();

        const response = await app.request(`/orders/${order.id}/cancel`, {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ reason: 'Changed my mind' }),
        });

        expect(response.status).toBe(200);
      });
    });
  });

  // ============================================================
  // Delivery Endpoints
  // ============================================================
  describe('Delivery Endpoints', () => {
    describe('POST /drivers', () => {
      it('should register new driver', async () => {
        const response = await app.request('/drivers', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            name: 'Driver One',
            phone: '090-1111-2222',
            vehicleType: 'MOTORCYCLE',
            license: 'DRV-12345',
          }),
        });

        expect(response.status).toBe(201);
        const data = await response.json();
        expect(data.name).toBe('Driver One');
      });
    });

    describe('PUT /drivers/:id/location', () => {
      it('should update driver location', async () => {
        // Create driver first
        const createResponse = await app.request('/drivers', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            name: 'Driver Two',
            phone: '090-2222-3333',
            vehicleType: 'BICYCLE',
            license: 'DRV-67890',
          }),
        });
        const driver = await createResponse.json();

        const response = await app.request(`/drivers/${driver.id}/location`, {
          method: 'PUT',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ latitude: 35.68, longitude: 139.66 }),
        });

        expect(response.status).toBe(200);
      });
    });
  });

  // ============================================================
  // Health Check
  // ============================================================
  describe('Health Check', () => {
    it('should return healthy status', async () => {
      const response = await app.request('/health', { method: 'GET' });
      expect(response.status).toBe(200);
      const data = await response.json();
      expect(data.status).toBe('healthy');
    });
  });
});
