/**
 * MenuItem Entity
 * @design DES-DELIVERY-001 §3.1
 * @task TSK-DLV-003
 */

import { Money } from '../shared';
import { RestaurantId } from './Restaurant';

// ============================================================
// MenuItem ID
// ============================================================
export class MenuItemId {
  constructor(public readonly value: string) {}

  static generate(): MenuItemId {
    return new MenuItemId(`item-${crypto.randomUUID()}`);
  }

  equals(other: MenuItemId): boolean {
    return this.value === other.value;
  }
}

// ============================================================
// Customization
// ============================================================
export interface CustomizationOption {
  name: string;
  priceAdjustment: Money;
}

export interface Customization {
  name: string;
  required: boolean;
  maxSelections: number;
  options: CustomizationOption[];
}

// ============================================================
// MenuItem Entity
// ============================================================
export interface CreateMenuItemProps {
  restaurantId: RestaurantId;
  name: string;
  description: string;
  price: Money;
  category: string;
  customizations?: Customization[];
}

export class MenuItem {
  private _isAvailable: boolean = true;

  private constructor(
    public readonly id: MenuItemId,
    public readonly restaurantId: RestaurantId,
    private _name: string,
    private _description: string,
    private _price: Money,
    private _category: string,
    private _customizations: Customization[]
  ) {}

  static create(props: CreateMenuItemProps): MenuItem {
    if (!props.name || props.name.trim().length < 3) {
      throw new Error('Name must be at least 3 characters');
    }
    if (props.name.length > 100) {
      throw new Error('Name must be at most 100 characters');
    }
    if (props.price.amount <= 0) {
      throw new Error('Price must be greater than 0');
    }
    if (!props.category || props.category.trim().length === 0) {
      throw new Error('Category is required');
    }

    return new MenuItem(
      MenuItemId.generate(),
      props.restaurantId,
      props.name.trim(),
      props.description?.trim() || '',
      props.price,
      props.category.trim(),
      props.customizations || []
    );
  }

  // Getters
  get name(): string {
    return this._name;
  }
  get description(): string {
    return this._description;
  }
  get price(): Money {
    return this._price;
  }
  get category(): string {
    return this._category;
  }
  get isAvailable(): boolean {
    return this._isAvailable;
  }
  get customizations(): Customization[] {
    return [...this._customizations];
  }

  // Availability
  markUnavailable(): void {
    this._isAvailable = false;
  }

  markAvailable(): void {
    this._isAvailable = true;
  }

  // Price calculation with customizations
  calculatePrice(selectedOptions: CustomizationOption[]): Money {
    let total = this._price;
    for (const option of selectedOptions) {
      total = total.add(option.priceAdjustment);
    }
    return total;
  }

  // Updates
  updatePrice(newPrice: Money): void {
    if (newPrice.amount <= 0) {
      throw new Error('Price must be greater than 0');
    }
    this._price = newPrice;
  }

  updateDescription(description: string): void {
    this._description = description.trim();
  }
}
