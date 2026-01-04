/**
 * Customer Entity
 * @design DES-DELIVERY-001 §3.3
 * @task TSK-DLV-005
 */

import { GeoLocation } from '../shared';

// ============================================================
// Customer ID
// ============================================================
export class CustomerId {
  constructor(public readonly value: string) {}

  static generate(): CustomerId {
    return new CustomerId(`cust-${crypto.randomUUID()}`);
  }

  equals(other: CustomerId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Address ID
// ============================================================
export class AddressId {
  constructor(public readonly value: string) {}

  static generate(): AddressId {
    return new AddressId(`addr-${crypto.randomUUID()}`);
  }

  equals(other: AddressId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Delivery Address Entity
// ============================================================
export interface CreateDeliveryAddressProps {
  label: string;
  street: string;
  city: string;
  postalCode: string;
  location: GeoLocation;
  instructions?: string;
}

export class DeliveryAddress {
  private _isDefault: boolean = false;

  private constructor(
    public readonly id: AddressId,
    private _label: string,
    private _street: string,
    private _city: string,
    private _postalCode: string,
    private _location: GeoLocation,
    private _instructions?: string
  ) {}

  static create(props: CreateDeliveryAddressProps): DeliveryAddress {
    if (!props.label || props.label.trim().length === 0) {
      throw new Error('Label is required');
    }
    if (!props.street || props.street.trim().length === 0) {
      throw new Error('Street is required');
    }

    return new DeliveryAddress(
      AddressId.generate(),
      props.label.trim(),
      props.street.trim(),
      props.city.trim(),
      props.postalCode.trim(),
      props.location,
      props.instructions?.trim()
    );
  }

  // Getters
  get label(): string {
    return this._label;
  }
  get street(): string {
    return this._street;
  }
  get city(): string {
    return this._city;
  }
  get postalCode(): string {
    return this._postalCode;
  }
  get location(): GeoLocation {
    return this._location;
  }
  get instructions(): string | undefined {
    return this._instructions;
  }
  get isDefault(): boolean {
    return this._isDefault;
  }

  setAsDefault(): void {
    this._isDefault = true;
  }

  unsetDefault(): void {
    this._isDefault = false;
  }
}

// ============================================================
// Customer Entity
// ============================================================
export interface CreateCustomerProps {
  name: string;
  email: string;
  phone: string;
  password?: string;
}

export class Customer {
  private _addresses: DeliveryAddress[] = [];

  private constructor(
    public readonly id: CustomerId,
    private _name: string,
    private _email: string,
    private _phone: string,
    private _passwordHash?: string
  ) {}

  static create(props: CreateCustomerProps): Customer {
    if (!props.name || props.name.trim().length === 0) {
      throw new Error('Name is required');
    }
    if (!props.email || !props.email.includes('@')) {
      throw new Error('Valid email is required');
    }
    if (!props.phone || props.phone.trim().length === 0) {
      throw new Error('Phone is required');
    }

    return new Customer(
      CustomerId.generate(),
      props.name.trim(),
      props.email.toLowerCase().trim(),
      props.phone.trim(),
      props.password // In real app, hash this
    );
  }

  // Getters
  get name(): string {
    return this._name;
  }
  get email(): string {
    return this._email;
  }
  get phone(): string {
    return this._phone;
  }
  get addresses(): DeliveryAddress[] {
    return [...this._addresses];
  }

  // Address management
  addAddress(address: DeliveryAddress): void {
    if (this._addresses.length === 0) {
      address.setAsDefault();
    }
    this._addresses.push(address);
  }

  setDefaultAddress(addressId: AddressId): void {
    const address = this._addresses.find((a) => a.id.equals(addressId));
    if (!address) {
      throw new Error('Address not found');
    }

    this._addresses.forEach((a) => a.unsetDefault());
    address.setAsDefault();
  }

  getDefaultAddress(): DeliveryAddress | undefined {
    return this._addresses.find((a) => a.isDefault);
  }

  removeAddress(addressId: AddressId): void {
    const index = this._addresses.findIndex((a) => a.id.equals(addressId));
    if (index === -1) {
      throw new Error('Address not found');
    }

    const wasDefault = this._addresses[index].isDefault;
    this._addresses.splice(index, 1);

    // If removed address was default, set first remaining as default
    if (wasDefault && this._addresses.length > 0) {
      this._addresses[0].setAsDefault();
    }
  }

  // Updates
  updatePhone(phone: string): void {
    if (!phone || phone.trim().length === 0) {
      throw new Error('Phone is required');
    }
    this._phone = phone.trim();
  }

  updateName(name: string): void {
    if (!name || name.trim().length === 0) {
      throw new Error('Name is required');
    }
    this._name = name.trim();
  }
}
