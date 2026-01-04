# Food Delivery System - Design Document

> **Document ID**: DES-DELIVERY-001  
> **Version**: 1.0.0  
> **Date**: 2024-01-15  
> **Requirements**: REQ-DELIVERY-001  
> **Status**: APPROVED

## 1. Overview

### 1.1 Architecture Style
- **Pattern**: Domain-Driven Design (DDD) with Hexagonal Architecture
- **Communication**: REST API (sync), Event-driven (async notifications)
- **Database**: Event Sourcing for orders, CRUD for master data

### 1.2 C4 Context Diagram

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  Customer   │     │  Restaurant │     │   Driver    │
│    App      │     │    App      │     │    App      │
└──────┬──────┘     └──────┬──────┘     └──────┬──────┘
       │                   │                   │
       └─────────┬─────────┴─────────┬─────────┘
                 │                   │
                 ▼                   ▼
        ┌────────────────────────────────────┐
        │     Food Delivery Platform         │
        │    ┌────────────────────────┐      │
        │    │      API Gateway       │      │
        │    └───────────┬────────────┘      │
        │                │                   │
        │    ┌───────────┴────────────┐      │
        │    │    Application Core    │      │
        │    └────────────────────────┘      │
        └────────────────────────────────────┘
                 │                   │
        ┌────────┴─────┐    ┌───────┴────────┐
        │   Payment    │    │  Notification  │
        │   Gateway    │    │    Service     │
        └──────────────┘    └────────────────┘
```

---

## 2. Domain Model (C4 Component Level)

### 2.1 Bounded Contexts

| Context | Aggregates | Description |
|---------|-----------|-------------|
| Restaurant | Restaurant, Menu | Restaurant and menu management |
| Order | Order, OrderItem | Order lifecycle |
| Customer | Customer, Address | Customer management |
| Delivery | Driver, Delivery | Driver and delivery tracking |
| Payment | Payment, Refund | Payment processing |

---

## 3. Domain Entities

### 3.1 Restaurant Context

#### Restaurant (Aggregate Root)
```typescript
class RestaurantId extends ValueObject<string> {}

enum RestaurantStatus {
  PENDING = 'PENDING',
  ACTIVE = 'ACTIVE',
  SUSPENDED = 'SUSPENDED',
  CLOSED = 'CLOSED'
}

interface Restaurant {
  id: RestaurantId;
  name: string;
  address: Address;
  phone: string;
  cuisineType: CuisineType;
  operatingHours: OperatingHours[];
  minimumOrder: Money;
  deliveryFee: Money;
  rating: number;
  status: RestaurantStatus;
  
  // Methods
  isOpen(): boolean;
  canAcceptOrder(amount: Money): boolean;
  updateStatus(status: RestaurantStatus): void;
}
```

#### MenuItem (Entity)
```typescript
class MenuItemId extends ValueObject<string> {}

interface MenuItem {
  id: MenuItemId;
  restaurantId: RestaurantId;
  name: string;
  description: string;
  price: Money;
  category: string;
  isAvailable: boolean;
  customizations: Customization[];
  
  // Methods
  calculatePrice(selectedOptions: CustomizationOption[]): Money;
  markUnavailable(): void;
  markAvailable(): void;
}
```

### 3.2 Order Context

#### Order (Aggregate Root)
```typescript
class OrderId extends ValueObject<string> {}

enum OrderStatus {
  PLACED = 'PLACED',
  ACCEPTED = 'ACCEPTED',
  PREPARING = 'PREPARING',
  READY = 'READY',
  PICKED_UP = 'PICKED_UP',
  DELIVERED = 'DELIVERED',
  CANCELLED = 'CANCELLED'
}

interface Order {
  id: OrderId;
  customerId: CustomerId;
  restaurantId: RestaurantId;
  items: OrderItem[];
  deliveryAddress: Address;
  subtotal: Money;
  deliveryFee: Money;
  tax: Money;
  total: Money;
  status: OrderStatus;
  placedAt: Date;
  estimatedDeliveryTime?: Date;
  
  // Methods
  accept(): void;
  startPreparing(): void;
  markReady(): void;
  cancel(reason: string): void;
  canBeCancelledByCustomer(): boolean;
}
```

#### OrderItem (Value Object)
```typescript
interface OrderItem {
  menuItemId: MenuItemId;
  name: string;
  quantity: number;
  unitPrice: Money;
  customizations: string[];
  totalPrice: Money;
}
```

### 3.3 Customer Context

#### Customer (Aggregate Root)
```typescript
class CustomerId extends ValueObject<string> {}

interface Customer {
  id: CustomerId;
  name: string;
  email: string;
  phone: string;
  addresses: DeliveryAddress[];
  
  // Methods
  addAddress(address: DeliveryAddress): void;
  setDefaultAddress(addressId: AddressId): void;
}
```

#### DeliveryAddress (Entity)
```typescript
class AddressId extends ValueObject<string> {}

interface DeliveryAddress {
  id: AddressId;
  label: string; // Home, Work, etc.
  street: string;
  city: string;
  postalCode: string;
  latitude: number;
  longitude: number;
  instructions?: string;
  isDefault: boolean;
}
```

### 3.4 Delivery Context

#### Driver (Aggregate Root)
```typescript
class DriverId extends ValueObject<string> {}

enum DriverStatus {
  OFFLINE = 'OFFLINE',
  AVAILABLE = 'AVAILABLE',
  ON_DELIVERY = 'ON_DELIVERY'
}

enum VehicleType {
  BICYCLE = 'BICYCLE',
  MOTORCYCLE = 'MOTORCYCLE',
  CAR = 'CAR'
}

interface Driver {
  id: DriverId;
  name: string;
  phone: string;
  vehicleType: VehicleType;
  license: string;
  status: DriverStatus;
  currentLocation?: GeoLocation;
  rating: number;
  
  // Methods
  goOnline(): void;
  goOffline(): void;
  startDelivery(orderId: OrderId): void;
  completeDelivery(): void;
  updateLocation(location: GeoLocation): void;
}
```

#### Delivery (Aggregate Root)
```typescript
class DeliveryId extends ValueObject<string> {}

enum DeliveryStatus {
  ASSIGNED = 'ASSIGNED',
  PICKED_UP = 'PICKED_UP',
  IN_TRANSIT = 'IN_TRANSIT',
  DELIVERED = 'DELIVERED'
}

interface Delivery {
  id: DeliveryId;
  orderId: OrderId;
  driverId: DriverId;
  pickupLocation: GeoLocation;
  deliveryLocation: GeoLocation;
  status: DeliveryStatus;
  estimatedArrival: Date;
  actualArrival?: Date;
  
  // Methods
  pickup(): void;
  updateETA(eta: Date): void;
  complete(): void;
}
```

### 3.5 Payment Context

#### Payment (Aggregate Root)
```typescript
class PaymentId extends ValueObject<string> {}

enum PaymentStatus {
  PENDING = 'PENDING',
  COMPLETED = 'COMPLETED',
  FAILED = 'FAILED',
  REFUNDED = 'REFUNDED'
}

enum PaymentMethod {
  CREDIT_CARD = 'CREDIT_CARD',
  DEBIT_CARD = 'DEBIT_CARD',
  CASH = 'CASH'
}

interface Payment {
  id: PaymentId;
  orderId: OrderId;
  amount: Money;
  method: PaymentMethod;
  status: PaymentStatus;
  transactionId?: string;
  processedAt?: Date;
  
  // Methods
  process(): void;
  refund(reason: string): void;
}
```

---

## 4. Value Objects

### 4.1 Money
```typescript
class Money {
  constructor(
    readonly amount: number,
    readonly currency: string = 'JPY'
  ) {
    if (amount < 0) throw new Error('Amount cannot be negative');
  }
  
  add(other: Money): Money;
  subtract(other: Money): Money;
  multiply(factor: number): Money;
  equals(other: Money): boolean;
}
```

### 4.2 GeoLocation
```typescript
class GeoLocation {
  constructor(
    readonly latitude: number,
    readonly longitude: number
  ) {
    if (latitude < -90 || latitude > 90) throw new Error('Invalid latitude');
    if (longitude < -180 || longitude > 180) throw new Error('Invalid longitude');
  }
  
  distanceTo(other: GeoLocation): number; // Returns km
}
```

### 4.3 OperatingHours
```typescript
interface OperatingHours {
  dayOfWeek: DayOfWeek;
  openTime: string;  // "09:00"
  closeTime: string; // "22:00"
}
```

---

## 5. Domain Services

### 5.1 OrderService
```typescript
class OrderService {
  createOrder(
    customer: Customer,
    restaurant: Restaurant,
    items: OrderItem[],
    deliveryAddress: DeliveryAddress
  ): Result<Order>;
  
  acceptOrder(order: Order, restaurant: Restaurant): Result<void>;
  cancelOrder(order: Order, reason: string): Result<void>;
}
```

### 5.2 DeliveryService
```typescript
class DeliveryService {
  assignDriver(
    order: Order,
    availableDrivers: Driver[],
    restaurantLocation: GeoLocation
  ): Result<Delivery>;
  
  updateDriverLocation(driver: Driver, location: GeoLocation): void;
  completeDelivery(delivery: Delivery): void;
}
```

### 5.3 PaymentService
```typescript
class PaymentService {
  processPayment(order: Order, method: PaymentMethod): Result<Payment>;
  refundPayment(payment: Payment, reason: string): Result<void>;
}
```

---

## 6. Application Services

### 6.1 OrderApplicationService
- placeOrder(customerId, restaurantId, items, addressId, paymentMethod)
- acceptOrder(orderId)
- cancelOrder(orderId, reason)
- getOrderStatus(orderId)
- getCustomerOrders(customerId)

### 6.2 RestaurantApplicationService
- registerRestaurant(data)
- updateMenu(restaurantId, items)
- updateStatus(restaurantId, status)
- searchRestaurants(criteria)

### 6.3 DeliveryApplicationService
- assignDelivery(orderId)
- updateDriverLocation(driverId, location)
- completeDelivery(deliveryId)
- trackDelivery(orderId)

---

## 7. Repository Interfaces

```typescript
interface RestaurantRepository {
  save(restaurant: Restaurant): Promise<void>;
  findById(id: RestaurantId): Promise<Restaurant | null>;
  findByLocation(location: GeoLocation, radiusKm: number): Promise<Restaurant[]>;
  search(criteria: RestaurantSearchCriteria): Promise<Restaurant[]>;
}

interface OrderRepository {
  save(order: Order): Promise<void>;
  findById(id: OrderId): Promise<Order | null>;
  findByCustomerId(customerId: CustomerId): Promise<Order[]>;
  findPendingOrders(): Promise<Order[]>;
}

interface DriverRepository {
  save(driver: Driver): Promise<void>;
  findById(id: DriverId): Promise<Driver | null>;
  findAvailableNear(location: GeoLocation, radiusKm: number): Promise<Driver[]>;
}
```

---

## 8. API Endpoints

| Method | Endpoint | Description |
|--------|----------|-------------|
| POST | /api/restaurants | Register restaurant |
| GET | /api/restaurants | Search restaurants |
| PUT | /api/restaurants/:id/menu | Update menu |
| POST | /api/orders | Place order |
| GET | /api/orders/:id | Get order status |
| PUT | /api/orders/:id/accept | Accept order |
| DELETE | /api/orders/:id | Cancel order |
| POST | /api/customers | Register customer |
| POST | /api/drivers | Register driver |
| PUT | /api/drivers/:id/location | Update location |
| GET | /api/deliveries/:orderId | Track delivery |

---

## 9. Events

| Event | Trigger | Subscribers |
|-------|---------|-------------|
| OrderPlaced | New order | Restaurant, Payment |
| OrderAccepted | Restaurant accepts | Customer, Delivery |
| OrderReady | Food ready | Delivery |
| DeliveryAssigned | Driver assigned | Customer, Driver |
| DeliveryCompleted | Order delivered | Customer, Restaurant |
| PaymentProcessed | Payment success | Order |

---

## 10. Traceability

| Design | Requirements |
|--------|--------------|
| DES-RES-001 | REQ-RES-001, REQ-RES-002 |
| DES-MENU-001 | REQ-MENU-001, REQ-MENU-002 |
| DES-ORD-001 | REQ-ORD-001, REQ-ORD-002 |
| DES-CUST-001 | REQ-CUST-001, REQ-CUST-002 |
| DES-DRV-001 | REQ-DRV-001, REQ-DRV-002 |

---

**Document History**

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2024-01-15 | MUSUBIX | Initial design |
