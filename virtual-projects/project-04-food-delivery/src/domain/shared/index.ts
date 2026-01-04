/**
 * Shared Value Objects
 * @design DES-DELIVERY-001 §4
 * @task TSK-DLV-001
 */

// ============================================================
// Money Value Object
// ============================================================
export class Money {
  constructor(
    public readonly amount: number,
    public readonly currency: string = 'JPY'
  ) {
    if (amount < 0) {
      throw new Error('Amount cannot be negative');
    }
  }

  add(other: Money): Money {
    if (this.currency !== other.currency) {
      throw new Error('Currency mismatch');
    }
    return new Money(this.amount + other.amount, this.currency);
  }

  subtract(other: Money): Money {
    if (this.currency !== other.currency) {
      throw new Error('Currency mismatch');
    }
    return new Money(this.amount - other.amount, this.currency);
  }

  multiply(factor: number): Money {
    return new Money(Math.round(this.amount * factor), this.currency);
  }

  equals(other: Money): boolean {
    return this.amount === other.amount && this.currency === other.currency;
  }

  isGreaterThan(other: Money): boolean {
    if (this.currency !== other.currency) {
      throw new Error('Currency mismatch');
    }
    return this.amount > other.amount;
  }

  isGreaterThanOrEqual(other: Money): boolean {
    if (this.currency !== other.currency) {
      throw new Error('Currency mismatch');
    }
    return this.amount >= other.amount;
  }

  toString(): string {
    return `${this.currency} ${this.amount.toLocaleString()}`;
  }
}

// ============================================================
// GeoLocation Value Object
// ============================================================
export class GeoLocation {
  constructor(
    public readonly latitude: number,
    public readonly longitude: number
  ) {
    if (latitude < -90 || latitude > 90) {
      throw new Error('Invalid latitude');
    }
    if (longitude < -180 || longitude > 180) {
      throw new Error('Invalid longitude');
    }
  }

  /**
   * Calculate distance to another location using Haversine formula
   * @returns Distance in kilometers
   */
  distanceTo(other: GeoLocation): number {
    const R = 6371; // Earth's radius in km
    const dLat = this.toRad(other.latitude - this.latitude);
    const dLon = this.toRad(other.longitude - this.longitude);
    
    const a =
      Math.sin(dLat / 2) * Math.sin(dLat / 2) +
      Math.cos(this.toRad(this.latitude)) *
        Math.cos(this.toRad(other.latitude)) *
        Math.sin(dLon / 2) *
        Math.sin(dLon / 2);
    
    const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
    return R * c;
  }

  private toRad(deg: number): number {
    return deg * (Math.PI / 180);
  }

  equals(other: GeoLocation): boolean {
    return this.latitude === other.latitude && this.longitude === other.longitude;
  }
}

// ============================================================
// Operating Hours Value Object
// ============================================================
export enum DayOfWeek {
  SUNDAY = 0,
  MONDAY = 1,
  TUESDAY = 2,
  WEDNESDAY = 3,
  THURSDAY = 4,
  FRIDAY = 5,
  SATURDAY = 6,
}

export class OperatingHours {
  constructor(
    public readonly dayOfWeek: DayOfWeek,
    public readonly openTime: string,
    public readonly closeTime: string
  ) {
    const timeRegex = /^([01][0-9]|2[0-3]):[0-5][0-9]$/;
    
    if (!timeRegex.test(openTime) || !timeRegex.test(closeTime)) {
      throw new Error('Invalid time format. Use HH:MM');
    }
    
    if (openTime >= closeTime) {
      throw new Error('Close time must be after open time');
    }
  }

  isOpenAt(time: string): boolean {
    return time >= this.openTime && time < this.closeTime;
  }
}

// ============================================================
// Address Value Object
// ============================================================
export class Address {
  constructor(
    public readonly street: string,
    public readonly city: string,
    public readonly postalCode: string,
    public readonly country: string = 'Japan'
  ) {
    if (!street || street.trim().length === 0) {
      throw new Error('Street is required');
    }
    if (!city || city.trim().length === 0) {
      throw new Error('City is required');
    }
  }

  toString(): string {
    return `${this.postalCode} ${this.city} ${this.street}`;
  }

  equals(other: Address): boolean {
    return (
      this.street === other.street &&
      this.city === other.city &&
      this.postalCode === other.postalCode
    );
  }
}
