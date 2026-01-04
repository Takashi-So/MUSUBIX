/**
 * Contract Service
 * TSK-022: ContractService
 * 
 * @see REQ-RENTAL-001 F030-F032
 * @see DES-RENTAL-001 §5.3
 */

import type {
  LeaseContract,
  LeaseContractId,
  PropertyId,
  TenantId,
  CreateContractInput,
  Money,
} from '../types/index.js';
import {
  createLeaseContract,
  activateContract,
  renewContract,
  terminateContract,
  calculateDepositReturn,
  isContractExpired,
} from '../entities/LeaseContract.js';
import {
  generateInitialPayments,
  generateMonthlyPaymentSchedule,
} from '../entities/Payment.js';
import type { IContractRepository } from '../repositories/ContractRepository.js';
import type { IPropertyRepository } from '../repositories/PropertyRepository.js';
import type { ITenantRepository } from '../repositories/TenantRepository.js';
import type { IPaymentRepository } from '../repositories/PaymentRepository.js';
import { updatePropertyStatus } from '../entities/Property.js';
import { updateTenantStatus } from '../entities/Tenant.js';

/**
 * Contract Service
 */
export class ContractService {
  constructor(
    private contractRepository: IContractRepository,
    private propertyRepository: IPropertyRepository,
    private tenantRepository: ITenantRepository,
    private paymentRepository: IPaymentRepository
  ) {}

  /**
   * 契約を作成
   * @see REQ-RENTAL-001 F030
   */
  async createContract(input: CreateContractInput): Promise<LeaseContract> {
    // Verify property exists and is available or reserved
    const property = await this.propertyRepository.findById(input.propertyId);
    if (!property) {
      throw new Error(`Property with ID ${input.propertyId} not found`);
    }
    if (property.status !== 'available' && property.status !== 'reserved') {
      throw new Error('Property is not available for contract');
    }

    // Verify tenant exists
    const tenant = await this.tenantRepository.findById(input.tenantId);
    if (!tenant) {
      throw new Error(`Tenant with ID ${input.tenantId} not found`);
    }

    // Check for existing active contract on property
    const existingContracts = await this.contractRepository.findByPropertyId(input.propertyId);
    const hasActiveContract = existingContracts.some(c => c.status === 'active');
    if (hasActiveContract) {
      throw new Error('Property already has an active contract');
    }

    // Create contract
    const contract = createLeaseContract(input);
    await this.contractRepository.create(contract);

    // Reserve the property
    const reservedProperty = updatePropertyStatus(property, 'reserved');
    await this.propertyRepository.update(reservedProperty);

    return contract;
  }

  /**
   * 契約を取得
   */
  async getContract(id: LeaseContractId): Promise<LeaseContract | null> {
    return this.contractRepository.findById(id);
  }

  /**
   * 契約を有効化（入居開始）
   * @see REQ-RENTAL-001 F030
   */
  async activateContract(id: LeaseContractId): Promise<LeaseContract> {
    const contract = await this.contractRepository.findById(id);
    if (!contract) {
      throw new Error(`Contract with ID ${id} not found`);
    }

    // Activate contract
    const activated = activateContract(contract);
    await this.contractRepository.update(activated);

    // Update property status to occupied
    const property = await this.propertyRepository.findById(contract.propertyId);
    if (property) {
      const occupied = updatePropertyStatus(property, 'occupied');
      await this.propertyRepository.update(occupied);
    }

    // Update tenant status to active
    const tenant = await this.tenantRepository.findById(contract.tenantId);
    if (tenant && tenant.status === 'prospective') {
      const activeTenant = updateTenantStatus(tenant, 'active');
      await this.tenantRepository.update(activeTenant);
    }

    // Generate initial payments
    const initialPayments = generateInitialPayments(
      contract.id,
      contract.tenantId,
      contract.deposit.amount,
      contract.keyMoney.amount,
      contract.monthlyRent.amount,
      contract.maintenanceFee.amount,
      contract.startDate
    );
    await this.paymentRepository.createMany(initialPayments);

    // Generate monthly payment schedule
    const monthlyPayments = generateMonthlyPaymentSchedule(
      contract.id,
      contract.tenantId,
      contract.monthlyRent.amount,
      contract.maintenanceFee.amount,
      contract.startDate,
      contract.endDate
    );
    // Skip first month (already in initial payments)
    const futurePayments = monthlyPayments.filter(
      p => p.dueDate > contract.startDate
    );
    if (futurePayments.length > 0) {
      await this.paymentRepository.createMany(futurePayments);
    }

    return activated;
  }

  /**
   * 契約を更新
   * @see REQ-RENTAL-001 F031
   */
  async renewContract(
    id: LeaseContractId,
    newEndDate: Date,
    newMonthlyRent?: number
  ): Promise<LeaseContract> {
    const contract = await this.contractRepository.findById(id);
    if (!contract) {
      throw new Error(`Contract with ID ${id} not found`);
    }

    // Create renewed contract
    const renewed = renewContract(contract, newEndDate, newMonthlyRent);
    
    // Update old contract status
    const oldContract = { ...contract, status: 'renewed' as const, updatedAt: new Date() };
    await this.contractRepository.update(oldContract);
    
    // Save new contract
    await this.contractRepository.create(renewed);

    // Generate renewal fee payment
    if (contract.renewalFee && contract.renewalFee.amount > 0) {
      const renewalPayment = generateInitialPayments(
        renewed.id,
        renewed.tenantId,
        0,  // no deposit
        0,  // no key money
        contract.renewalFee.amount,  // renewal fee as first month rent placeholder
        0,
        renewed.startDate
      );
      if (renewalPayment.length > 0) {
        await this.paymentRepository.createMany(renewalPayment);
      }
    }

    // Generate new payment schedule
    const monthlyPayments = generateMonthlyPaymentSchedule(
      renewed.id,
      renewed.tenantId,
      renewed.monthlyRent.amount,
      renewed.maintenanceFee.amount,
      renewed.startDate,
      renewed.endDate
    );
    if (monthlyPayments.length > 0) {
      await this.paymentRepository.createMany(monthlyPayments);
    }

    return renewed;
  }

  /**
   * 契約を解約
   * @see REQ-RENTAL-001 F032
   */
  async terminateContract(
    id: LeaseContractId,
    terminationDate?: Date,
    restorationCost?: number
  ): Promise<{ contract: LeaseContract; depositReturn: Money }> {
    const contract = await this.contractRepository.findById(id);
    if (!contract) {
      throw new Error(`Contract with ID ${id} not found`);
    }

    // Terminate contract
    const terminated = terminateContract(contract, terminationDate);
    await this.contractRepository.update(terminated);

    // Update property status to available
    const property = await this.propertyRepository.findById(contract.propertyId);
    if (property) {
      const available = updatePropertyStatus(property, 'available');
      await this.propertyRepository.update(available);
    }

    // Update tenant status to former
    const tenant = await this.tenantRepository.findById(contract.tenantId);
    if (tenant && tenant.status === 'active') {
      const formerTenant = updateTenantStatus(tenant, 'former');
      await this.tenantRepository.update(formerTenant);
    }

    // Calculate deposit return
    const depositReturn = calculateDepositReturn(contract, restorationCost || 0);

    return { contract: terminated, depositReturn };
  }

  /**
   * 期限切れ間近の契約を取得
   * @see REQ-RENTAL-001 F031
   */
  async getExpiringContracts(days: number = 90): Promise<LeaseContract[]> {
    return this.contractRepository.findExpiring(days);
  }

  /**
   * 物件の契約履歴を取得
   */
  async getContractsByProperty(propertyId: PropertyId): Promise<LeaseContract[]> {
    return this.contractRepository.findByPropertyId(propertyId);
  }

  /**
   * 入居者の契約履歴を取得
   */
  async getContractsByTenant(tenantId: TenantId): Promise<LeaseContract[]> {
    return this.contractRepository.findByTenantId(tenantId);
  }

  /**
   * 有効な契約を取得
   */
  async getActiveContracts(): Promise<LeaseContract[]> {
    return this.contractRepository.findByStatus('active');
  }

  /**
   * 期限切れ契約をチェックして更新
   */
  async checkAndUpdateExpiredContracts(): Promise<LeaseContract[]> {
    const activeContracts = await this.contractRepository.findByStatus('active');
    const expiredContracts: LeaseContract[] = [];

    for (const contract of activeContracts) {
      if (isContractExpired(contract)) {
        const expired = { ...contract, status: 'expired' as const, updatedAt: new Date() };
        await this.contractRepository.update(expired);
        expiredContracts.push(expired);
      }
    }

    return expiredContracts;
  }
}
