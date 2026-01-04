/**
 * InMemory Customer Repository
 * @design DES-DELIVERY-001 §6.3
 * @task TSK-DLV-012
 */

import { Customer, CustomerId } from '../../domain/customer';

export interface CustomerRepository {
  save(customer: Customer): Promise<void>;
  findById(id: CustomerId): Promise<Customer | undefined>;
  findByEmail(email: string): Promise<Customer | undefined>;
}

export class InMemoryCustomerRepository implements CustomerRepository {
  private customers: Map<string, Customer> = new Map();

  async save(customer: Customer): Promise<void> {
    this.customers.set(customer.id.value, customer);
  }

  async findById(id: CustomerId): Promise<Customer | undefined> {
    return this.customers.get(id.value);
  }

  async findByEmail(email: string): Promise<Customer | undefined> {
    return Array.from(this.customers.values()).find(
      (customer) => customer.email === email
    );
  }
}
