/**
 * Driver and Delivery Entities
 * @design DES-DELIVERY-001 §3.4
 * @task TSK-DLV-006
 */

import { GeoLocation } from '../shared';
import { OrderId } from '../order';

// ============================================================
// Driver ID
// ============================================================
export class DriverId {
  constructor(public readonly value: string) {}

  static generate(): DriverId {
    return new DriverId(`drv-${crypto.randomUUID()}`);
  }

  equals(other: DriverId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Driver Enums
// ============================================================
export enum DriverStatus {
  OFFLINE = 'OFFLINE',
  AVAILABLE = 'AVAILABLE',
  ON_DELIVERY = 'ON_DELIVERY',
}

export enum VehicleType {
  BICYCLE = 'BICYCLE',
  MOTORCYCLE = 'MOTORCYCLE',
  CAR = 'CAR',
}

// ============================================================
// Driver Entity
// ============================================================
export interface CreateDriverProps {
  name: string;
  phone: string;
  vehicleType: VehicleType;
  license: string;
}

export class Driver {
  private _status: DriverStatus = DriverStatus.OFFLINE;
  private _currentLocation?: GeoLocation;
  private _rating: number = 5.0;
  private _ratingCount: number = 0;
  private _currentOrderId?: OrderId;

  private constructor(
    public readonly id: DriverId,
    private _name: string,
    private _phone: string,
    private _vehicleType: VehicleType,
    private _license: string
  ) {}

  static create(props: CreateDriverProps): Driver {
    if (!props.name || props.name.trim().length === 0) {
      throw new Error('Name is required');
    }
    if (!props.phone || props.phone.trim().length === 0) {
      throw new Error('Phone is required');
    }
    if (!props.license || props.license.trim().length === 0) {
      throw new Error('License is required');
    }

    return new Driver(
      DriverId.generate(),
      props.name.trim(),
      props.phone.trim(),
      props.vehicleType,
      props.license.trim()
    );
  }

  // Getters
  get name(): string {
    return this._name;
  }
  get phone(): string {
    return this._phone;
  }
  get vehicleType(): VehicleType {
    return this._vehicleType;
  }
  get license(): string {
    return this._license;
  }
  get status(): DriverStatus {
    return this._status;
  }
  get currentLocation(): GeoLocation | undefined {
    return this._currentLocation;
  }
  get rating(): number {
    return this._rating;
  }
  get currentOrderId(): OrderId | undefined {
    return this._currentOrderId;
  }

  // Status transitions
  goOnline(): void {
    if (this._status === DriverStatus.ON_DELIVERY) {
      throw new Error('Cannot go online while on delivery');
    }
    this._status = DriverStatus.AVAILABLE;
  }

  goOffline(): void {
    if (this._status === DriverStatus.ON_DELIVERY) {
      throw new Error('Cannot go offline while on delivery');
    }
    this._status = DriverStatus.OFFLINE;
  }

  startDelivery(orderId: OrderId): void {
    if (this._status !== DriverStatus.AVAILABLE) {
      throw new Error('Driver must be available to start delivery');
    }
    this._status = DriverStatus.ON_DELIVERY;
    this._currentOrderId = orderId;
  }

  completeDelivery(): void {
    if (this._status !== DriverStatus.ON_DELIVERY) {
      throw new Error('Driver is not on delivery');
    }
    this._status = DriverStatus.AVAILABLE;
    this._currentOrderId = undefined;
  }

  // Location
  updateLocation(location: GeoLocation): void {
    this._currentLocation = location;
  }

  // Rating
  updateRating(newRating: number): void {
    if (newRating < 1 || newRating > 5) {
      throw new Error('Rating must be between 1 and 5');
    }
    const totalRating = this._rating * this._ratingCount + newRating;
    this._ratingCount += 1;
    this._rating = Math.round((totalRating / this._ratingCount) * 10) / 10;
  }

  isAvailable(): boolean {
    return this._status === DriverStatus.AVAILABLE;
  }
}

// ============================================================
// Delivery ID
// ============================================================
export class DeliveryId {
  constructor(public readonly value: string) {}

  static generate(): DeliveryId {
    return new DeliveryId(`del-${crypto.randomUUID()}`);
  }

  equals(other: DeliveryId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Delivery Status
// ============================================================
export enum DeliveryStatus {
  ASSIGNED = 'ASSIGNED',
  PICKED_UP = 'PICKED_UP',
  IN_TRANSIT = 'IN_TRANSIT',
  DELIVERED = 'DELIVERED',
}

// ============================================================
// Delivery Entity
// ============================================================
export interface CreateDeliveryProps {
  orderId: OrderId;
  driverId: DriverId;
  pickupLocation: GeoLocation;
  deliveryLocation: GeoLocation;
  estimatedArrival: Date;
}

export class Delivery {
  private _status: DeliveryStatus = DeliveryStatus.ASSIGNED;
  private _actualPickupTime?: Date;
  private _actualDeliveryTime?: Date;

  private constructor(
    public readonly id: DeliveryId,
    public readonly orderId: OrderId,
    public readonly driverId: DriverId,
    public readonly pickupLocation: GeoLocation,
    public readonly deliveryLocation: GeoLocation,
    private _estimatedArrival: Date,
    public readonly assignedAt: Date
  ) {}

  static create(props: CreateDeliveryProps): Delivery {
    return new Delivery(
      DeliveryId.generate(),
      props.orderId,
      props.driverId,
      props.pickupLocation,
      props.deliveryLocation,
      props.estimatedArrival,
      new Date()
    );
  }

  // Getters
  get status(): DeliveryStatus {
    return this._status;
  }
  get estimatedArrival(): Date {
    return this._estimatedArrival;
  }
  get actualPickupTime(): Date | undefined {
    return this._actualPickupTime;
  }
  get actualDeliveryTime(): Date | undefined {
    return this._actualDeliveryTime;
  }

  // Status transitions
  pickup(): void {
    if (this._status !== DeliveryStatus.ASSIGNED) {
      throw new Error('Invalid status for pickup');
    }
    this._status = DeliveryStatus.PICKED_UP;
    this._actualPickupTime = new Date();
  }

  startTransit(): void {
    if (this._status !== DeliveryStatus.PICKED_UP) {
      throw new Error('Invalid status for transit');
    }
    this._status = DeliveryStatus.IN_TRANSIT;
  }

  complete(): void {
    if (
      this._status !== DeliveryStatus.PICKED_UP &&
      this._status !== DeliveryStatus.IN_TRANSIT
    ) {
      throw new Error('Invalid status for completion');
    }
    this._status = DeliveryStatus.DELIVERED;
    this._actualDeliveryTime = new Date();
  }

  // ETA update
  updateETA(eta: Date): void {
    this._estimatedArrival = eta;
  }
}
