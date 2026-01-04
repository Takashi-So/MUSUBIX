/**
 * Property Service
 * TSK-020: PropertyService
 * 
 * @see REQ-RENTAL-001 F010-F012
 * @see DES-RENTAL-001 §5.1
 */

import type {
  Property,
  PropertyId,
  OwnerId,
  PropertyOwner,
  PropertyStatus,
  CreatePropertyInput,
  PropertySearchCriteria,
} from '../types/index.js';
import {
  createProperty,
  updateProperty,
  updatePropertyStatus,
  markPropertyAsDeleted,
} from '../entities/Property.js';
import {
  addPropertyToOwner,
  removePropertyFromOwner,
} from '../entities/PropertyOwner.js';
import type { IPropertyRepository } from '../repositories/PropertyRepository.js';
import type { IPropertyOwnerRepository } from '../repositories/PropertyOwnerRepository.js';

/**
 * Property Service
 */
export class PropertyService {
  constructor(
    private propertyRepository: IPropertyRepository,
    private ownerRepository: IPropertyOwnerRepository
  ) {}

  /**
   * 物件を登録
   * @see REQ-RENTAL-001 F010
   */
  async registerProperty(input: CreatePropertyInput): Promise<Property> {
    // Verify owner exists
    const owner = await this.ownerRepository.findById(input.ownerId);
    if (!owner) {
      throw new Error(`Owner with ID ${input.ownerId} not found`);
    }
    if (owner.status !== 'active') {
      throw new Error('Cannot register property for inactive owner');
    }

    // Create property
    const property = createProperty(input);
    await this.propertyRepository.create(property);

    // Add property to owner's list
    const updatedOwner = addPropertyToOwner(owner, property.id);
    await this.ownerRepository.update(updatedOwner);

    return property;
  }

  /**
   * 物件情報を取得
   */
  async getProperty(id: PropertyId): Promise<Property | null> {
    return this.propertyRepository.findById(id);
  }

  /**
   * 物件情報を更新
   * @see REQ-RENTAL-001 F011
   */
  async updateProperty(
    id: PropertyId,
    updates: Partial<Omit<CreatePropertyInput, 'ownerId'>>
  ): Promise<Property> {
    const property = await this.propertyRepository.findById(id);
    if (!property) {
      throw new Error(`Property with ID ${id} not found`);
    }

    const updated = updateProperty(property, updates);
    return this.propertyRepository.update(updated);
  }

  /**
   * 物件の空き状況を更新
   * @see REQ-RENTAL-001 F012
   */
  async updateAvailability(
    id: PropertyId,
    status: PropertyStatus
  ): Promise<Property> {
    const property = await this.propertyRepository.findById(id);
    if (!property) {
      throw new Error(`Property with ID ${id} not found`);
    }

    const updated = updatePropertyStatus(property, status);
    return this.propertyRepository.update(updated);
  }

  /**
   * 物件を検索
   * @see REQ-RENTAL-001 F011
   */
  async searchProperties(criteria: PropertySearchCriteria): Promise<Property[]> {
    return this.propertyRepository.search(criteria);
  }

  /**
   * 空き物件を検索
   */
  async findAvailableProperties(criteria?: Omit<PropertySearchCriteria, 'status'>): Promise<Property[]> {
    return this.propertyRepository.search({
      ...criteria,
      status: 'available',
    });
  }

  /**
   * 物件を削除（論理削除）
   */
  async deleteProperty(id: PropertyId): Promise<boolean> {
    const property = await this.propertyRepository.findById(id);
    if (!property) {
      throw new Error(`Property with ID ${id} not found`);
    }

    // Mark as deleted (under_maintenance)
    const deleted = markPropertyAsDeleted(property);
    await this.propertyRepository.update(deleted);

    // Remove from owner's list
    const owner = await this.ownerRepository.findById(property.ownerId);
    if (owner) {
      const updatedOwner = removePropertyFromOwner(owner, id);
      await this.ownerRepository.update(updatedOwner);
    }

    return true;
  }

  /**
   * オーナーの物件一覧を取得
   */
  async getOwnerProperties(ownerId: OwnerId): Promise<Property[]> {
    return this.propertyRepository.findByOwnerId(ownerId);
  }

  /**
   * 全物件を取得
   */
  async getAllProperties(): Promise<Property[]> {
    return this.propertyRepository.findAll();
  }
}
