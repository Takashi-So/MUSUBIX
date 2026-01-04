/**
 * Reporting Service
 * TSK-025: ReportingService
 * 
 * @see REQ-RENTAL-001 F060-F063
 * @see DES-RENTAL-001 §5.6, §5.7
 */

import type {
  PropertyId,
  PropertyOwnerId,
  OwnerRevenueReport,
  OccupancyReport,
  PaymentSummary,
  Money,
  PropertyType,
  PropertyStatus,
} from '../types/index.js';
import type { IPropertyRepository } from '../repositories/PropertyRepository.js';
import type { IPropertyOwnerRepository } from '../repositories/PropertyOwnerRepository.js';
import type { IContractRepository } from '../repositories/ContractRepository.js';
import type { IPaymentRepository } from '../repositories/PaymentRepository.js';
import type { IMaintenanceRepository } from '../repositories/MaintenanceRepository.js';

/**
 * Reporting Service
 */
export class ReportingService {
  constructor(
    private propertyRepository: IPropertyRepository,
    private propertyOwnerRepository: IPropertyOwnerRepository,
    private contractRepository: IContractRepository,
    private paymentRepository: IPaymentRepository,
    private maintenanceRepository: IMaintenanceRepository
  ) {}

  /**
   * オーナー収益レポートを生成
   * @see REQ-RENTAL-001 F060
   */
  async generateOwnerRevenueReport(
    ownerId: PropertyOwnerId,
    startDate: Date,
    endDate: Date
  ): Promise<OwnerRevenueReport> {
    const owner = await this.propertyOwnerRepository.findById(ownerId);
    if (!owner) {
      throw new Error(`Property owner with ID ${ownerId} not found`);
    }

    let totalRentIncome = 0;
    let maintenanceCosts = 0;
    const propertyDetails: OwnerRevenueReport['propertyDetails'] = [];

    for (const propertyId of owner.properties) {
      const property = await this.propertyRepository.findById(propertyId);
      if (!property) continue;

      // 契約情報を取得
      const contracts = await this.contractRepository.findByPropertyId(propertyId);
      let propertyRentIncome = 0;

      for (const contract of contracts) {
        // 期間内の支払い情報を取得
        const payments = await this.paymentRepository.findByContractId(contract.id);
        for (const payment of payments) {
          if (
            payment.status === 'paid' &&
            payment.paidDate &&
            payment.paidDate >= startDate &&
            payment.paidDate <= endDate
          ) {
            if (payment.type === 'rent') {
              propertyRentIncome += payment.amount.amount;
            }
          }
        }
      }

      // メンテナンス費用を取得
      const maintenanceRequests = await this.maintenanceRepository.findByPropertyId(propertyId);
      let propertyMaintenanceCosts = 0;
      for (const request of maintenanceRequests) {
        if (
          request.status === 'completed' &&
          request.completedDate &&
          request.completedDate >= startDate &&
          request.completedDate <= endDate &&
          request.actualCost
        ) {
          propertyMaintenanceCosts += request.actualCost.amount;
        }
      }

      totalRentIncome += propertyRentIncome;
      maintenanceCosts += propertyMaintenanceCosts;

      propertyDetails.push({
        propertyId,
        propertyName: property.name,
        rentIncome: { amount: propertyRentIncome, currency: 'JPY' },
        maintenanceCosts: { amount: propertyMaintenanceCosts, currency: 'JPY' },
        netIncome: { amount: propertyRentIncome - propertyMaintenanceCosts, currency: 'JPY' },
      });
    }

    // 管理費（家賃収入の5%と仮定）
    const managementFees = totalRentIncome * 0.05;
    const netIncome = totalRentIncome - maintenanceCosts - managementFees;

    return {
      ownerId,
      ownerName: owner.name,
      period: { startDate, endDate },
      totalRentIncome: { amount: totalRentIncome, currency: 'JPY' },
      maintenanceCosts: { amount: maintenanceCosts, currency: 'JPY' },
      managementFees: { amount: managementFees, currency: 'JPY' },
      netIncome: { amount: netIncome, currency: 'JPY' },
      propertyDetails,
      generatedAt: new Date(),
    };
  }

  /**
   * 稼働率レポートを生成
   * @see REQ-RENTAL-001 F061
   */
  async generateOccupancyReport(
    startDate: Date,
    endDate: Date,
    propertyType?: PropertyType
  ): Promise<OccupancyReport> {
    let properties = await this.propertyRepository.findAll();

    // 物件タイプでフィルタリング
    if (propertyType) {
      properties = properties.filter(p => p.propertyType === propertyType);
    }

    let occupiedCount = 0;
    let availableCount = 0;
    let maintenanceCount = 0;

    const byPropertyType: Record<PropertyType, { occupied: number; total: number }> = {
      apartment: { occupied: 0, total: 0 },
      house: { occupied: 0, total: 0 },
      condo: { occupied: 0, total: 0 },
      studio: { occupied: 0, total: 0 },
      room: { occupied: 0, total: 0 },
    };

    const byLocation: Record<string, { occupied: number; total: number }> = {};

    for (const property of properties) {
      const type = property.propertyType;
      byPropertyType[type].total++;

      // 地域別集計
      const location = `${property.address.prefecture}-${property.address.city}`;
      if (!byLocation[location]) {
        byLocation[location] = { occupied: 0, total: 0 };
      }
      byLocation[location].total++;

      // ステータス別集計
      if (property.status === 'occupied') {
        occupiedCount++;
        byPropertyType[type].occupied++;
        byLocation[location].occupied++;
      } else if (property.status === 'available') {
        availableCount++;
      } else if (property.status === 'maintenance') {
        maintenanceCount++;
      }
    }

    const totalProperties = properties.length;
    const occupancyRate = totalProperties > 0 ? (occupiedCount / totalProperties) * 100 : 0;

    return {
      period: { startDate, endDate },
      totalProperties,
      occupiedProperties: occupiedCount,
      availableProperties: availableCount,
      maintenanceProperties: maintenanceCount,
      occupancyRate: Math.round(occupancyRate * 100) / 100,
      byPropertyType: Object.fromEntries(
        Object.entries(byPropertyType).map(([key, value]) => [
          key,
          {
            ...value,
            occupancyRate: value.total > 0 ? Math.round((value.occupied / value.total) * 10000) / 100 : 0,
          },
        ])
      ),
      byLocation: Object.fromEntries(
        Object.entries(byLocation).map(([key, value]) => [
          key,
          {
            ...value,
            occupancyRate: value.total > 0 ? Math.round((value.occupied / value.total) * 10000) / 100 : 0,
          },
        ])
      ),
      generatedAt: new Date(),
    };
  }

  /**
   * 支払いサマリーレポートを生成
   * @see REQ-RENTAL-001 F062
   */
  async generatePaymentSummary(
    startDate: Date,
    endDate: Date
  ): Promise<PaymentSummary> {
    const allPayments = await this.paymentRepository.findAll();
    
    // 期間内の支払いをフィルタリング
    const periodPayments = allPayments.filter(p => {
      if (p.paidDate) {
        return p.paidDate >= startDate && p.paidDate <= endDate;
      }
      return p.dueDate >= startDate && p.dueDate <= endDate;
    });

    let totalCollected = 0;
    let totalPending = 0;
    let totalOverdue = 0;
    let totalLateFees = 0;

    const byPaymentType: Record<string, Money> = {
      rent: { amount: 0, currency: 'JPY' },
      deposit: { amount: 0, currency: 'JPY' },
      key_money: { amount: 0, currency: 'JPY' },
      commission: { amount: 0, currency: 'JPY' },
      renewal_fee: { amount: 0, currency: 'JPY' },
      other: { amount: 0, currency: 'JPY' },
    };

    for (const payment of periodPayments) {
      if (payment.status === 'paid') {
        totalCollected += payment.amount.amount;
        byPaymentType[payment.type].amount += payment.amount.amount;
      } else if (payment.status === 'pending') {
        totalPending += payment.amount.amount;
      } else if (payment.status === 'overdue') {
        totalOverdue += payment.amount.amount;
        if (payment.lateFee) {
          totalLateFees += payment.lateFee.amount;
        }
      }
    }

    const collectionRate = 
      periodPayments.length > 0
        ? (periodPayments.filter(p => p.status === 'paid').length / periodPayments.length) * 100
        : 0;

    return {
      period: { startDate, endDate },
      totalCollected: { amount: totalCollected, currency: 'JPY' },
      totalPending: { amount: totalPending, currency: 'JPY' },
      totalOverdue: { amount: totalOverdue, currency: 'JPY' },
      totalLateFees: { amount: totalLateFees, currency: 'JPY' },
      collectionRate: Math.round(collectionRate * 100) / 100,
      byPaymentType,
      generatedAt: new Date(),
    };
  }

  /**
   * 監査ログを生成
   * @see REQ-RENTAL-001 F063
   */
  async generateAuditLog(
    startDate: Date,
    endDate: Date,
    entityType?: 'property' | 'contract' | 'payment' | 'maintenance'
  ): Promise<{
    period: { startDate: Date; endDate: Date };
    entries: Array<{
      timestamp: Date;
      entityType: string;
      entityId: string;
      action: string;
      details: string;
    }>;
    generatedAt: Date;
  }> {
    const entries: Array<{
      timestamp: Date;
      entityType: string;
      entityId: string;
      action: string;
      details: string;
    }> = [];

    // 物件の監査ログ
    if (!entityType || entityType === 'property') {
      const properties = await this.propertyRepository.findAll();
      for (const property of properties) {
        if (property.createdAt >= startDate && property.createdAt <= endDate) {
          entries.push({
            timestamp: property.createdAt,
            entityType: 'property',
            entityId: property.id,
            action: 'created',
            details: `Property "${property.name}" registered`,
          });
        }
        if (property.updatedAt >= startDate && property.updatedAt <= endDate && 
            property.updatedAt.getTime() !== property.createdAt.getTime()) {
          entries.push({
            timestamp: property.updatedAt,
            entityType: 'property',
            entityId: property.id,
            action: 'updated',
            details: `Property "${property.name}" updated, status: ${property.status}`,
          });
        }
      }
    }

    // 契約の監査ログ
    if (!entityType || entityType === 'contract') {
      const contracts = await this.contractRepository.findAll();
      for (const contract of contracts) {
        if (contract.createdAt >= startDate && contract.createdAt <= endDate) {
          entries.push({
            timestamp: contract.createdAt,
            entityType: 'contract',
            entityId: contract.id,
            action: 'created',
            details: `Contract created, status: ${contract.status}`,
          });
        }
        if (contract.updatedAt >= startDate && contract.updatedAt <= endDate &&
            contract.updatedAt.getTime() !== contract.createdAt.getTime()) {
          entries.push({
            timestamp: contract.updatedAt,
            entityType: 'contract',
            entityId: contract.id,
            action: 'updated',
            details: `Contract updated, status: ${contract.status}`,
          });
        }
      }
    }

    // 支払いの監査ログ
    if (!entityType || entityType === 'payment') {
      const payments = await this.paymentRepository.findAll();
      for (const payment of payments) {
        if (payment.paidDate && payment.paidDate >= startDate && payment.paidDate <= endDate) {
          entries.push({
            timestamp: payment.paidDate,
            entityType: 'payment',
            entityId: payment.id,
            action: 'paid',
            details: `Payment of ${payment.amount.amount} JPY received`,
          });
        }
      }
    }

    // メンテナンスの監査ログ
    if (!entityType || entityType === 'maintenance') {
      const requests = await this.maintenanceRepository.findAll();
      for (const request of requests) {
        if (request.reportedDate >= startDate && request.reportedDate <= endDate) {
          entries.push({
            timestamp: request.reportedDate,
            entityType: 'maintenance',
            entityId: request.id,
            action: 'reported',
            details: `Maintenance request "${request.title}" reported`,
          });
        }
        if (request.completedDate && 
            request.completedDate >= startDate && 
            request.completedDate <= endDate) {
          entries.push({
            timestamp: request.completedDate,
            entityType: 'maintenance',
            entityId: request.id,
            action: 'completed',
            details: `Maintenance request "${request.title}" completed`,
          });
        }
      }
    }

    // タイムスタンプでソート
    entries.sort((a, b) => a.timestamp.getTime() - b.timestamp.getTime());

    return {
      period: { startDate, endDate },
      entries,
      generatedAt: new Date(),
    };
  }

  /**
   * ダッシュボードサマリーを生成
   */
  async generateDashboardSummary(): Promise<{
    properties: {
      total: number;
      occupied: number;
      available: number;
      maintenance: number;
    };
    contracts: {
      active: number;
      expiringSoon: number;
    };
    payments: {
      pendingCount: number;
      overdueCount: number;
      totalOverdue: Money;
    };
    maintenance: {
      openRequests: number;
      emergencyRequests: number;
    };
    generatedAt: Date;
  }> {
    // 物件サマリー
    const properties = await this.propertyRepository.findAll();
    const propertyStats = {
      total: properties.length,
      occupied: properties.filter(p => p.status === 'occupied').length,
      available: properties.filter(p => p.status === 'available').length,
      maintenance: properties.filter(p => p.status === 'maintenance').length,
    };

    // 契約サマリー
    const contracts = await this.contractRepository.findAll();
    const activeContracts = contracts.filter(c => c.status === 'active');
    const expiringContracts = await this.contractRepository.findExpiring(30);

    // 支払いサマリー
    const overduePayments = await this.paymentRepository.findOverdue();
    const pendingPayments = await this.paymentRepository.findByStatus('pending');
    const totalOverdue = overduePayments.reduce(
      (sum, p) => sum + p.amount.amount + (p.lateFee?.amount || 0),
      0
    );

    // メンテナンスサマリー
    const openRequests = await this.maintenanceRepository.findOpen();
    const emergencyRequests = await this.maintenanceRepository.findByUrgency('emergency');
    const activeEmergencies = emergencyRequests.filter(
      r => r.status !== 'completed' && r.status !== 'cancelled'
    );

    return {
      properties: propertyStats,
      contracts: {
        active: activeContracts.length,
        expiringSoon: expiringContracts.length,
      },
      payments: {
        pendingCount: pendingPayments.length,
        overdueCount: overduePayments.length,
        totalOverdue: { amount: totalOverdue, currency: 'JPY' },
      },
      maintenance: {
        openRequests: openRequests.length,
        emergencyRequests: activeEmergencies.length,
      },
      generatedAt: new Date(),
    };
  }
}
