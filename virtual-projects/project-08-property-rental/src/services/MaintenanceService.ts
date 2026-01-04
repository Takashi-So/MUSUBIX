/**
 * Maintenance Service
 * TSK-024: MaintenanceService
 * 
 * @see REQ-RENTAL-001 F050-F052
 * @see DES-RENTAL-001 §5.5
 */

import type {
  MaintenanceRequest,
  MaintenanceId,
  PropertyId,
  TenantId,
  MaintenanceCategory,
  UrgencyLevel,
  StaffAssignment,
} from '../types/index.js';
import {
  createMaintenanceRequest,
  assignStaff,
  startProgress,
  completeMaintenanceRequest,
  cancelMaintenanceRequest,
} from '../entities/MaintenanceRequest.js';
import type { IMaintenanceRepository } from '../repositories/MaintenanceRepository.js';
import type { IPropertyRepository } from '../repositories/PropertyRepository.js';
import type { ITenantRepository } from '../repositories/TenantRepository.js';

/**
 * Maintenance Service
 */
export class MaintenanceService {
  constructor(
    private maintenanceRepository: IMaintenanceRepository,
    private propertyRepository: IPropertyRepository,
    private tenantRepository: ITenantRepository
  ) {}

  /**
   * メンテナンスリクエストを作成
   * @see REQ-RENTAL-001 F050
   */
  async submitRequest(
    propertyId: PropertyId,
    reportedBy: TenantId,
    category: MaintenanceCategory,
    title: string,
    description: string,
    urgencyLevel: UrgencyLevel = 'normal',
    photos?: string[]
  ): Promise<MaintenanceRequest> {
    // 物件の存在確認
    const property = await this.propertyRepository.findById(propertyId);
    if (!property) {
      throw new Error(`Property with ID ${propertyId} not found`);
    }

    // 報告者の存在確認
    const tenant = await this.tenantRepository.findById(reportedBy);
    if (!tenant) {
      throw new Error(`Tenant with ID ${reportedBy} not found`);
    }

    const request = createMaintenanceRequest(
      propertyId,
      reportedBy,
      category,
      title,
      description,
      urgencyLevel,
      photos
    );

    return this.maintenanceRepository.create(request);
  }

  /**
   * メンテナンスリクエストを取得
   */
  async getRequest(id: MaintenanceId): Promise<MaintenanceRequest | null> {
    return this.maintenanceRepository.findById(id);
  }

  /**
   * 物件のメンテナンスリクエスト一覧を取得
   */
  async getRequestsByProperty(propertyId: PropertyId): Promise<MaintenanceRequest[]> {
    return this.maintenanceRepository.findByPropertyId(propertyId);
  }

  /**
   * 入居者が報告したリクエスト一覧を取得
   */
  async getRequestsByTenant(tenantId: TenantId): Promise<MaintenanceRequest[]> {
    return this.maintenanceRepository.findByReporter(tenantId);
  }

  /**
   * 未対応のリクエスト一覧を取得
   * @see REQ-RENTAL-001 F051
   */
  async getOpenRequests(): Promise<MaintenanceRequest[]> {
    return this.maintenanceRepository.findOpen();
  }

  /**
   * 緊急度別にリクエストを取得
   */
  async getRequestsByUrgency(urgencyLevel: UrgencyLevel): Promise<MaintenanceRequest[]> {
    return this.maintenanceRepository.findByUrgency(urgencyLevel);
  }

  /**
   * スタッフをアサイン
   * @see REQ-RENTAL-001 F051
   */
  async assignStaff(
    requestId: MaintenanceId,
    staff: StaffAssignment
  ): Promise<MaintenanceRequest> {
    const request = await this.maintenanceRepository.findById(requestId);
    if (!request) {
      throw new Error(`Maintenance request with ID ${requestId} not found`);
    }

    if (request.status === 'completed' || request.status === 'cancelled') {
      throw new Error('Cannot assign staff to completed or cancelled request');
    }

    const assigned = assignStaff(request, staff);
    return this.maintenanceRepository.update(assigned);
  }

  /**
   * 作業を開始
   */
  async startWork(requestId: MaintenanceId): Promise<MaintenanceRequest> {
    const request = await this.maintenanceRepository.findById(requestId);
    if (!request) {
      throw new Error(`Maintenance request with ID ${requestId} not found`);
    }

    if (request.status !== 'assigned') {
      throw new Error('Can only start work on assigned requests');
    }

    const started = startProgress(request);
    return this.maintenanceRepository.update(started);
  }

  /**
   * 作業を完了
   * @see REQ-RENTAL-001 F052
   */
  async completeRequest(
    requestId: MaintenanceId,
    completionNotes: string,
    actualCost?: { amount: number; currency: string }
  ): Promise<MaintenanceRequest> {
    const request = await this.maintenanceRepository.findById(requestId);
    if (!request) {
      throw new Error(`Maintenance request with ID ${requestId} not found`);
    }

    if (request.status !== 'in_progress') {
      throw new Error('Can only complete requests that are in progress');
    }

    const completed = completeMaintenanceRequest(
      request,
      completionNotes,
      actualCost ? { amount: actualCost.amount, currency: 'JPY' } : undefined
    );
    return this.maintenanceRepository.update(completed);
  }

  /**
   * リクエストをキャンセル
   */
  async cancelRequest(
    requestId: MaintenanceId,
    reason: string
  ): Promise<MaintenanceRequest> {
    const request = await this.maintenanceRepository.findById(requestId);
    if (!request) {
      throw new Error(`Maintenance request with ID ${requestId} not found`);
    }

    if (request.status === 'completed' || request.status === 'cancelled') {
      throw new Error('Cannot cancel completed or already cancelled request');
    }

    const cancelled = cancelMaintenanceRequest(request, reason);
    return this.maintenanceRepository.update(cancelled);
  }

  /**
   * メンテナンス統計を取得
   * @see REQ-RENTAL-001 F052
   */
  async getMaintenanceStats(propertyId?: PropertyId): Promise<{
    totalRequests: number;
    openRequests: number;
    completedRequests: number;
    averageResolutionTime: number; // in hours
    requestsByCategory: Record<MaintenanceCategory, number>;
    requestsByUrgency: Record<UrgencyLevel, number>;
  }> {
    let requests: MaintenanceRequest[];
    
    if (propertyId) {
      requests = await this.maintenanceRepository.findByPropertyId(propertyId);
    } else {
      requests = await this.maintenanceRepository.findAll();
    }

    const stats = {
      totalRequests: requests.length,
      openRequests: 0,
      completedRequests: 0,
      averageResolutionTime: 0,
      requestsByCategory: {} as Record<MaintenanceCategory, number>,
      requestsByUrgency: {} as Record<UrgencyLevel, number>,
    };

    let totalResolutionTime = 0;
    let completedCount = 0;

    for (const request of requests) {
      // ステータス別カウント
      if (request.status === 'completed') {
        stats.completedRequests++;
        if (request.completedDate) {
          const resolutionTime = request.completedDate.getTime() - request.reportedDate.getTime();
          totalResolutionTime += resolutionTime;
          completedCount++;
        }
      } else if (request.status !== 'cancelled') {
        stats.openRequests++;
      }

      // カテゴリ別カウント
      stats.requestsByCategory[request.category] = 
        (stats.requestsByCategory[request.category] || 0) + 1;

      // 緊急度別カウント
      stats.requestsByUrgency[request.urgencyLevel] = 
        (stats.requestsByUrgency[request.urgencyLevel] || 0) + 1;
    }

    // 平均解決時間（時間単位）
    if (completedCount > 0) {
      stats.averageResolutionTime = totalResolutionTime / completedCount / (1000 * 60 * 60);
    }

    return stats;
  }

  /**
   * 緊急リクエストを取得
   */
  async getEmergencyRequests(): Promise<MaintenanceRequest[]> {
    const urgentRequests = await this.maintenanceRepository.findByUrgency('emergency');
    return urgentRequests.filter(r => r.status !== 'completed' && r.status !== 'cancelled');
  }

  /**
   * アサイン待ちリクエストを取得
   */
  async getPendingAssignment(): Promise<MaintenanceRequest[]> {
    const openRequests = await this.maintenanceRepository.findOpen();
    return openRequests.filter(r => r.status === 'reported');
  }
}
