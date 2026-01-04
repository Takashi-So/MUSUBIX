/**
 * Customer Application Service
 * @design DES-DELIVERY-001 §7.4
 * @task TSK-DLV-017
 */

import {
  Customer,
  CustomerId,
  DeliveryAddress,
} from '../domain/customer';
import { CustomerRepository } from '../infrastructure/repositories';
import { GeoLocation } from '../domain/shared';

export interface RegisterCustomerCommand {
  name: string;
  email: string;
  phone: string;
  password?: string;
}

export interface AddDeliveryAddressCommand {
  label: string;
  street: string;
  city: string;
  postalCode: string;
  latitude: number;
  longitude: number;
}

export interface RegisterCustomerResult {
  success: boolean;
  customer?: Customer;
  error?: string;
}

export interface AddDeliveryAddressResult {
  success: boolean;
  error?: string;
}

export class CustomerApplicationService {
  constructor(private readonly customerRepo: CustomerRepository) {}

  async registerCustomer(
    command: RegisterCustomerCommand
  ): Promise<RegisterCustomerResult> {
    try {
      // Check if email already exists
      const existing = await this.customerRepo.findByEmail(command.email);
      if (existing) {
        return { success: false, error: 'Email already registered' };
      }

      const customer = Customer.create({
        name: command.name,
        email: command.email,
        phone: command.phone,
        password: command.password,
      });

      await this.customerRepo.save(customer);
      return { success: true, customer };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Registration failed',
      };
    }
  }

  async addDeliveryAddress(
    customerId: string,
    address: AddDeliveryAddressCommand
  ): Promise<AddDeliveryAddressResult> {
    try {
      const customer = await this.customerRepo.findById(
        new CustomerId(customerId)
      );
      if (!customer) {
        return { success: false, error: 'Customer not found' };
      }

      const deliveryAddress = DeliveryAddress.create({
        label: address.label,
        street: address.street,
        city: address.city,
        postalCode: address.postalCode,
        location: new GeoLocation(address.latitude, address.longitude),
      });

      customer.addAddress(deliveryAddress);
      await this.customerRepo.save(customer);
      return { success: true };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Address addition failed',
      };
    }
  }

  async getCustomerProfile(customerId: string): Promise<Customer | undefined> {
    return this.customerRepo.findById(new CustomerId(customerId));
  }

  async getCustomerByEmail(email: string): Promise<Customer | undefined> {
    return this.customerRepo.findByEmail(email);
  }
}
