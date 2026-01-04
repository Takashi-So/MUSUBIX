/**
 * Restaurant Entity
 * @design DES-DELIVERY-001 §3.1
 * @task TSK-DLV-002
 */

import { Money, GeoLocation, Address, OperatingHours, DayOfWeek } from '../shared';

// ============================================================
// Restaurant ID
// ============================================================
export class RestaurantId {
  constructor(public readonly value: string) {}

  static generate(): RestaurantId {
    return new RestaurantId(`res-${crypto.randomUUID()}`);
  }

  equals(other: RestaurantId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Enums
// ============================================================
export enum RestaurantStatus {
  PENDING = 'PENDING',
  ACTIVE = 'ACTIVE',
  SUSPENDED = 'SUSPENDED',
  CLOSED = 'CLOSED',
}

export enum CuisineType {
  JAPANESE = 'JAPANESE',
  CHINESE = 'CHINESE',
  KOREAN = 'KOREAN',
  ITALIAN = 'ITALIAN',
  FRENCH = 'FRENCH',
  AMERICAN = 'AMERICAN',
  INDIAN = 'INDIAN',
  THAI = 'THAI',
  VIETNAMESE = 'VIETNAMESE',
  OTHER = 'OTHER',
}

// ============================================================
// Restaurant Entity
// ============================================================
export interface CreateRestaurantProps {
  name: string;
  address: Address;
  location: GeoLocation;
  phone: string;
  cuisineType: CuisineType;
  minimumOrder: Money;
  deliveryFee: Money;
  operatingHours: OperatingHours[];
}

export class Restaurant {
  private _status: RestaurantStatus = RestaurantStatus.PENDING;
  private _rating: number = 0;
  private _ratingCount: number = 0;

  private constructor(
    public readonly id: RestaurantId,
    private _name: string,
    private _address: Address,
    private _location: GeoLocation,
    private _phone: string,
    private _cuisineType: CuisineType,
    private _minimumOrder: Money,
    private _deliveryFee: Money,
    private _operatingHours: OperatingHours[]
  ) {}

  static create(props: CreateRestaurantProps): Restaurant {
    if (!props.name || props.name.trim().length === 0) {
      throw new Error('Name is required');
    }
    if (props.name.trim().length < 2) {
      throw new Error('Name must be at least 2 characters');
    }

    return new Restaurant(
      RestaurantId.generate(),
      props.name.trim(),
      props.address,
      props.location,
      props.phone,
      props.cuisineType,
      props.minimumOrder,
      props.deliveryFee,
      props.operatingHours
    );
  }

  // Getters
  get name(): string {
    return this._name;
  }
  get address(): Address {
    return this._address;
  }
  get location(): GeoLocation {
    return this._location;
  }
  get phone(): string {
    return this._phone;
  }
  get cuisineType(): CuisineType {
    return this._cuisineType;
  }
  get minimumOrder(): Money {
    return this._minimumOrder;
  }
  get deliveryFee(): Money {
    return this._deliveryFee;
  }
  get operatingHours(): OperatingHours[] {
    return [...this._operatingHours];
  }
  get status(): RestaurantStatus {
    return this._status;
  }
  get rating(): number {
    return this._rating;
  }

  // Status transitions
  activate(): void {
    this._status = RestaurantStatus.ACTIVE;
  }

  suspend(): void {
    this._status = RestaurantStatus.SUSPENDED;
  }

  close(): void {
    this._status = RestaurantStatus.CLOSED;
  }

  // Business logic
  isOpenAt(datetime: Date): boolean {
    if (this._status !== RestaurantStatus.ACTIVE) {
      return false;
    }

    const dayOfWeek = datetime.getDay() as DayOfWeek;
    const time = datetime.toTimeString().substring(0, 5); // HH:MM

    const todayHours = this._operatingHours.find((h) => h.dayOfWeek === dayOfWeek);
    if (!todayHours) {
      return false;
    }

    return todayHours.isOpenAt(time);
  }

  canAcceptOrder(orderAmount: Money): boolean {
    if (this._status !== RestaurantStatus.ACTIVE) {
      return false;
    }
    return orderAmount.isGreaterThanOrEqual(this._minimumOrder);
  }

  updateRating(newRating: number): void {
    if (newRating < 0 || newRating > 5) {
      throw new Error('Rating must be between 0 and 5');
    }
    // Simple average update
    const totalRating = this._rating * this._ratingCount + newRating;
    this._ratingCount += 1;
    this._rating = Math.round((totalRating / this._ratingCount) * 10) / 10;
  }

  updateDeliveryFee(fee: Money): void {
    this._deliveryFee = fee;
  }

  updateMinimumOrder(amount: Money): void {
    this._minimumOrder = amount;
  }
}
