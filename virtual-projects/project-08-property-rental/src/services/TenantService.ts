/**
 * Tenant Service
 * TSK-021: TenantService
 * 
 * @see REQ-RENTAL-001 F020-F023, F013
 * @see DES-RENTAL-001 §5.2
 */

import type {
  Tenant,
  TenantId,
  Guarantor,
  GuarantorId,
  RentalApplication,
  PropertyId,
  CreateTenantInput,
  SubmitApplicationInput,
} from '../types/index.js';
import {
  createTenant,
  updateTenant,
  assignGuarantor,
  updateTenantStatus,
  deactivateTenant,
  checkIncomeEligibility,
} from '../entities/Tenant.js';
import {
  createGuarantor,
  checkGuarantorEligibility,
  type CreateGuarantorInput,
} from '../entities/Guarantor.js';
import {
  createRentalApplication,
  startScreening,
  addScreeningNotes,
  approveApplication,
  rejectApplication,
} from '../entities/RentalApplication.js';
import type { ITenantRepository } from '../repositories/TenantRepository.js';
import type { IGuarantorRepository } from '../repositories/GuarantorRepository.js';
import type { IApplicationRepository } from '../repositories/ApplicationRepository.js';
import type { IPropertyRepository } from '../repositories/PropertyRepository.js';

/**
 * Tenant Service
 */
export class TenantService {
  constructor(
    private tenantRepository: ITenantRepository,
    private guarantorRepository: IGuarantorRepository,
    private applicationRepository: IApplicationRepository,
    private propertyRepository: IPropertyRepository
  ) {}

  /**
   * 入居者を登録
   * @see REQ-RENTAL-001 F020
   */
  async registerTenant(input: CreateTenantInput): Promise<Tenant> {
    // Check email uniqueness
    const existingTenant = await this.tenantRepository.findByEmail(input.contact.email);
    if (existingTenant) {
      throw new Error(`Tenant with email ${input.contact.email} already exists`);
    }

    const tenant = createTenant(input);
    return this.tenantRepository.create(tenant);
  }

  /**
   * 入居者情報を取得
   */
  async getTenant(id: TenantId): Promise<Tenant | null> {
    return this.tenantRepository.findById(id);
  }

  /**
   * 入居者情報を更新
   * @see REQ-RENTAL-001 F022
   */
  async updateTenant(
    id: TenantId,
    updates: Partial<CreateTenantInput>
  ): Promise<Tenant> {
    const tenant = await this.tenantRepository.findById(id);
    if (!tenant) {
      throw new Error(`Tenant with ID ${id} not found`);
    }

    const updated = updateTenant(tenant, updates);
    return this.tenantRepository.update(updated);
  }

  /**
   * 保証人を追加
   * @see REQ-RENTAL-001 F013, F023
   */
  async addGuarantor(
    tenantId: TenantId,
    guarantorInput: CreateGuarantorInput
  ): Promise<{ tenant: Tenant; guarantor: Guarantor }> {
    const tenant = await this.tenantRepository.findById(tenantId);
    if (!tenant) {
      throw new Error(`Tenant with ID ${tenantId} not found`);
    }

    // Create guarantor
    const guarantor = createGuarantor(guarantorInput);
    await this.guarantorRepository.create(guarantor);

    // Assign to tenant
    const updatedTenant = assignGuarantor(tenant, guarantor.id);
    await this.tenantRepository.update(updatedTenant);

    return { tenant: updatedTenant, guarantor };
  }

  /**
   * 入居申込を提出
   * @see REQ-RENTAL-001 F021
   */
  async submitApplication(input: SubmitApplicationInput): Promise<RentalApplication> {
    // Verify tenant exists
    const tenant = await this.tenantRepository.findById(input.tenantId);
    if (!tenant) {
      throw new Error(`Tenant with ID ${input.tenantId} not found`);
    }

    // Verify property exists and is available
    const property = await this.propertyRepository.findById(input.propertyId);
    if (!property) {
      throw new Error(`Property with ID ${input.propertyId} not found`);
    }
    if (property.status !== 'available') {
      throw new Error('Property is not available for rent');
    }

    // Check for existing pending application
    const hasPending = await this.applicationRepository.hasPendingApplication(
      input.tenantId,
      input.propertyId
    );
    if (hasPending) {
      throw new Error('Tenant already has a pending application for this property');
    }

    const application = createRentalApplication(input);
    return this.applicationRepository.create(application);
  }

  /**
   * 入居審査を実施
   * @see REQ-RENTAL-001 F021
   */
  async screenApplication(
    applicationId: string,
    options?: { autoApprove?: boolean }
  ): Promise<RentalApplication> {
    const application = await this.applicationRepository.findById(applicationId as any);
    if (!application) {
      throw new Error(`Application with ID ${applicationId} not found`);
    }

    // Start screening
    let screened = startScreening(application);
    
    // Get tenant and property for screening
    const tenant = await this.tenantRepository.findById(application.tenantId);
    const property = await this.propertyRepository.findById(application.propertyId);
    
    if (!tenant || !property) {
      throw new Error('Tenant or property not found');
    }

    // Income check
    const incomeCheck = checkIncomeEligibility(tenant, property.monthlyRent.amount);
    screened = addScreeningNotes(
      screened,
      `Income check: ${incomeCheck.eligible ? 'PASS' : 'FAIL'} ` +
      `(ratio: ${incomeCheck.ratio.toFixed(1)}, required: ${incomeCheck.requiredRatio})`
    );

    // Guarantor check (if exists)
    if (tenant.guarantorId) {
      const guarantor = await this.guarantorRepository.findById(tenant.guarantorId);
      if (guarantor) {
        const guarantorCheck = checkGuarantorEligibility(
          guarantor,
          tenant.employment.annualIncome.amount
        );
        screened = addScreeningNotes(
          screened,
          `Guarantor check: ${guarantorCheck.eligible ? 'PASS' : 'FAIL'} ` +
          `${guarantorCheck.reason || ''}`
        );
      }
    }

    // Auto approve/reject based on income check
    if (options?.autoApprove) {
      if (incomeCheck.eligible) {
        screened = approveApplication(screened);
      } else {
        screened = rejectApplication(screened, 'Income requirement not met');
      }
    }

    return this.applicationRepository.update(screened);
  }

  /**
   * 申込を承認
   */
  async approveApplication(applicationId: string): Promise<RentalApplication> {
    const application = await this.applicationRepository.findById(applicationId as any);
    if (!application) {
      throw new Error(`Application with ID ${applicationId} not found`);
    }

    const approved = approveApplication(application);
    
    // Update tenant status to active
    const tenant = await this.tenantRepository.findById(application.tenantId);
    if (tenant && tenant.status === 'prospective') {
      const activeTenant = updateTenantStatus(tenant, 'active');
      await this.tenantRepository.update(activeTenant);
    }

    return this.applicationRepository.update(approved);
  }

  /**
   * 申込を却下
   */
  async rejectApplication(applicationId: string, reason: string): Promise<RentalApplication> {
    const application = await this.applicationRepository.findById(applicationId as any);
    if (!application) {
      throw new Error(`Application with ID ${applicationId} not found`);
    }

    const rejected = rejectApplication(application, reason);
    return this.applicationRepository.update(rejected);
  }

  /**
   * 入居者を非アクティブ化
   */
  async deactivateTenant(id: TenantId): Promise<Tenant> {
    const tenant = await this.tenantRepository.findById(id);
    if (!tenant) {
      throw new Error(`Tenant with ID ${id} not found`);
    }

    const deactivated = deactivateTenant(tenant);
    return this.tenantRepository.update(deactivated);
  }

  /**
   * 申込一覧を取得
   */
  async getApplicationsByTenant(tenantId: TenantId): Promise<RentalApplication[]> {
    return this.applicationRepository.findByTenantId(tenantId);
  }

  /**
   * 物件の申込一覧を取得
   */
  async getApplicationsByProperty(propertyId: PropertyId): Promise<RentalApplication[]> {
    return this.applicationRepository.findByPropertyId(propertyId);
  }

  /**
   * 保証人情報を取得
   */
  async getGuarantor(id: GuarantorId): Promise<Guarantor | null> {
    return this.guarantorRepository.findById(id);
  }
}
