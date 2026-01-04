/**
 * Property Rental Management System - Type Definitions
 * TSK-003: Type Definitions
 * 
 * @module types
 * @see DES-RENTAL-001 §4.1-4.2
 */

// ============================================
// ID Types
// ============================================

/** Property ID format: PROP-YYYYMMDD-NNN */
export type PropertyId = `PROP-${string}`;

/** Owner ID format: OWN-YYYYMMDD-NNN */
export type OwnerId = `OWN-${string}`;

/** Tenant ID format: TEN-YYYYMMDD-NNN */
export type TenantId = `TEN-${string}`;

/** Guarantor ID format: GUA-YYYYMMDD-NNN */
export type GuarantorId = `GUA-${string}`;

/** Lease Contract ID format: LEASE-YYYYMMDD-NNN */
export type LeaseContractId = `LEASE-${string}`;

/** Payment ID format: PAY-YYYYMMDD-NNN */
export type PaymentId = `PAY-${string}`;

/** Maintenance Request ID format: MNT-YYYYMMDD-NNN */
export type MaintenanceRequestId = `MNT-${string}`;

/** Rental Application ID format: APP-YYYYMMDD-NNN */
export type RentalApplicationId = `APP-${string}`;

// ============================================
// Enum Types
// ============================================

/** Property types */
export type PropertyType = 
  | 'apartment'      // アパート
  | 'mansion'        // マンション
  | 'house'          // 一戸建て
  | 'office'         // オフィス
  | 'store';         // 店舗

/** Property availability status */
export type PropertyStatus = 
  | 'available'      // 空室
  | 'occupied'       // 入居中
  | 'under_maintenance'  // メンテナンス中
  | 'reserved';      // 予約済み

/** Property owner type */
export type OwnerType = 'individual' | 'corporation';

/** Owner status */
export type OwnerStatus = 'active' | 'inactive';

/** Tenant status */
export type TenantStatus = 
  | 'active'         // 入居中
  | 'prospective'    // 申込中
  | 'former';        // 退去済み

/** Guarantor relationship type */
export type RelationshipType = 
  | 'parent'         // 親
  | 'sibling'        // 兄弟姉妹
  | 'relative'       // 親戚
  | 'employer'       // 勤務先
  | 'guarantor_company';  // 保証会社

/** Lease contract status */
export type ContractStatus = 
  | 'draft'          // 下書き
  | 'active'         // 契約中
  | 'renewed'        // 更新済み
  | 'terminated'     // 解約
  | 'expired';       // 期限切れ

/** Payment type */
export type PaymentType = 
  | 'rent'           // 家賃
  | 'deposit'        // 敷金
  | 'key_money'      // 礼金
  | 'maintenance_fee'  // 管理費
  | 'renewal_fee'    // 更新料
  | 'late_fee';      // 遅延損害金

/** Payment method */
export type PaymentMethod = 
  | 'bank_transfer'  // 銀行振込
  | 'credit_card'    // クレジットカード
  | 'direct_debit'   // 口座振替
  | 'cash';          // 現金

/** Payment status */
export type PaymentStatus = 
  | 'pending'        // 未払い
  | 'paid'           // 支払済み
  | 'overdue'        // 延滞
  | 'cancelled';     // キャンセル

/** Maintenance request urgency */
export type UrgencyLevel = 
  | 'low'            // 低
  | 'medium'         // 中
  | 'high'           // 高
  | 'emergency';     // 緊急

/** Maintenance request status */
export type MaintenanceStatus = 
  | 'submitted'      // 申請済み
  | 'assigned'       // 担当者割当済み
  | 'in_progress'    // 対応中
  | 'completed'      // 完了
  | 'cancelled';     // キャンセル

/** Rental application status */
export type ApplicationStatus = 
  | 'submitted'      // 申請済み
  | 'screening'      // 審査中
  | 'approved'       // 承認
  | 'rejected'       // 却下
  | 'withdrawn';     // 取り下げ

/** Bank account type */
export type BankAccountType = 'ordinary' | 'checking';  // 普通 | 当座

// ============================================
// Value Objects
// ============================================

/**
 * Japanese address with furigana
 * @see DES-RENTAL-001 §4.2
 */
export interface Address {
  postalCode: string;      // 〒xxx-xxxx
  prefecture: string;      // 都道府県
  city: string;            // 市区町村
  street: string;          // 町名・番地
  building?: string;       // 建物名・部屋番号
}

/**
 * Person name with furigana (Japanese)
 * @see DES-RENTAL-001 §4.2
 */
export interface PersonName {
  firstName: string;       // 名
  lastName: string;        // 姓
  firstNameKana: string;   // 名（カナ）
  lastNameKana: string;    // 姓（カナ）
}

/**
 * Contact information
 * @see DES-RENTAL-001 §4.2
 */
export interface ContactInfo {
  phone: string;           // 電話番号
  email: string;           // メールアドレス
  address?: Address;       // 住所（オプション）
}

/**
 * Monetary value with currency
 * @see DES-RENTAL-001 §4.2
 */
export interface Money {
  amount: number;          // 金額
  currency: string;        // 通貨コード (JPY)
}

/**
 * Employment information
 * @see DES-RENTAL-001 §4.2
 */
export interface EmploymentInfo {
  companyName: string;           // 会社名
  position: string;              // 役職
  annualIncome: Money;           // 年収
  employmentType: string;        // 雇用形態 (正社員, 契約社員, etc.)
  yearsEmployed: number;         // 勤続年数
  companyPhone?: string;         // 会社電話番号
}

/**
 * Identification document
 * @see DES-RENTAL-001 §4.2
 */
export interface Identification {
  type: string;            // 証明書種別 (運転免許証, パスポート, etc.)
  number: string;          // 番号（暗号化）
  issuedDate: Date;        // 発行日
  expiryDate?: Date;       // 有効期限
}

/**
 * Bank account information
 * @see DES-RENTAL-001 §4.1.8
 */
export interface BankAccount {
  bankName: string;        // 銀行名
  branchName: string;      // 支店名
  accountType: BankAccountType;  // 口座種別
  accountNumber: string;   // 口座番号（暗号化）
  accountHolder: string;   // 口座名義
}

/**
 * Emergency contact
 * @see DES-RENTAL-001 §4.2
 */
export interface EmergencyContact {
  name: PersonName;
  relationship: string;
  phone: string;
  address?: Address;
}

// ============================================
// Entity Interfaces
// ============================================

/**
 * Property entity
 * @see REQ-RENTAL-001 F010-F012
 * @see DES-RENTAL-001 §4.1.1
 */
export interface Property {
  id: PropertyId;
  ownerId: OwnerId;
  address: Address;
  propertyType: PropertyType;
  sizeSqm: number;              // 面積（㎡）
  monthlyRent: Money;           // 月額家賃
  deposit: Money;               // 敷金
  keyMoney: Money;              // 礼金
  maintenanceFee: Money;        // 管理費
  amenities: string[];          // 設備
  status: PropertyStatus;
  photos: string[];             // 写真URL
  description?: string;         // 説明
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Property owner entity
 * @see DES-RENTAL-001 §4.1.8
 */
export interface PropertyOwner {
  id: OwnerId;
  name: PersonName;
  ownerType: OwnerType;
  contact: ContactInfo;
  bankAccount?: BankAccount;
  taxId?: string;              // 法人番号 or マイナンバー（暗号化）
  properties: PropertyId[];
  status: OwnerStatus;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Tenant entity
 * @see REQ-RENTAL-001 F020-F023
 * @see DES-RENTAL-001 §4.1.2
 */
export interface Tenant {
  id: TenantId;
  name: PersonName;
  contact: ContactInfo;
  identification: Identification;
  employment: EmploymentInfo;
  emergencyContact: EmergencyContact;
  guarantorId?: GuarantorId;
  status: TenantStatus;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Guarantor entity
 * @see REQ-RENTAL-001 F013
 * @see DES-RENTAL-001 §4.1.3
 */
export interface Guarantor {
  id: GuarantorId;
  name: PersonName;
  contact: ContactInfo;
  relationship: RelationshipType;
  employment?: EmploymentInfo;
  identification?: Identification;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Lease contract entity
 * @see REQ-RENTAL-001 F030-F032
 * @see DES-RENTAL-001 §4.1.4
 */
export interface LeaseContract {
  id: LeaseContractId;
  propertyId: PropertyId;
  tenantId: TenantId;
  guarantorId?: GuarantorId;
  startDate: Date;
  endDate: Date;
  monthlyRent: Money;
  deposit: Money;
  keyMoney: Money;
  maintenanceFee: Money;
  renewalFee?: Money;
  status: ContractStatus;
  specialTerms?: string;        // 特約事項
  renewedFromId?: LeaseContractId;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Payment entity
 * @see REQ-RENTAL-001 F040-F043
 * @see DES-RENTAL-001 §4.1.5
 */
export interface Payment {
  id: PaymentId;
  contractId: LeaseContractId;
  tenantId: TenantId;
  amount: Money;
  paymentType: PaymentType;
  paymentMethod?: PaymentMethod;
  dueDate: Date;
  paidDate?: Date;
  status: PaymentStatus;
  lateFee?: Money;
  receiptNumber?: string;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Maintenance request entity
 * @see REQ-RENTAL-001 F060-F062
 * @see DES-RENTAL-001 §4.1.6
 */
export interface MaintenanceRequest {
  id: MaintenanceRequestId;
  propertyId: PropertyId;
  tenantId: TenantId;
  title: string;
  description: string;
  urgency: UrgencyLevel;
  status: MaintenanceStatus;
  assignedTo?: string;
  scheduledDate?: Date;
  completedDate?: Date;
  cost?: Money;
  photos: string[];
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Rental application entity
 * @see REQ-RENTAL-001 F021
 * @see DES-RENTAL-001 §4.1.7
 */
export interface RentalApplication {
  id: RentalApplicationId;
  propertyId: PropertyId;
  tenantId: TenantId;
  desiredMoveInDate: Date;
  status: ApplicationStatus;
  screeningNotes?: string;
  rejectionReason?: string;
  createdAt: Date;
  updatedAt: Date;
}

// ============================================
// DTO Types (for service layer)
// ============================================

/** Create property input */
export interface CreatePropertyInput {
  ownerId: OwnerId;
  address: Address;
  propertyType: PropertyType;
  sizeSqm: number;
  monthlyRent: number;
  deposit: number;
  keyMoney: number;
  maintenanceFee: number;
  amenities?: string[];
  photos?: string[];
  description?: string;
}

/** Property search criteria */
export interface PropertySearchCriteria {
  prefecture?: string;
  city?: string;
  propertyType?: PropertyType;
  minRent?: number;
  maxRent?: number;
  minSize?: number;
  maxSize?: number;
  amenities?: string[];
  status?: PropertyStatus;
}

/** Create tenant input */
export interface CreateTenantInput {
  name: PersonName;
  contact: ContactInfo;
  identification: Identification;
  employment: EmploymentInfo;
  emergencyContact: EmergencyContact;
}

/** Create contract input */
export interface CreateContractInput {
  propertyId: PropertyId;
  tenantId: TenantId;
  guarantorId?: GuarantorId;
  startDate: Date;
  endDate: Date;
  monthlyRent: number;
  deposit: number;
  keyMoney: number;
  maintenanceFee: number;
  renewalFee?: number;
  specialTerms?: string;
}

/** Record payment input */
export interface RecordPaymentInput {
  contractId: LeaseContractId;
  tenantId: TenantId;
  amount: number;
  paymentType: PaymentType;
  paymentMethod: PaymentMethod;
  dueDate: Date;
  paidDate?: Date;
}

/** Submit maintenance request input */
export interface SubmitMaintenanceInput {
  propertyId: PropertyId;
  tenantId: TenantId;
  title: string;
  description: string;
  urgency: UrgencyLevel;
  photos?: string[];
}

/** Submit rental application input */
export interface SubmitApplicationInput {
  propertyId: PropertyId;
  tenantId: TenantId;
  desiredMoveInDate: Date;
}

// ============================================
// Report Types
// ============================================

/** Owner revenue report */
export interface OwnerRevenueReport {
  ownerId: OwnerId;
  period: { from: Date; to: Date };
  totalRevenue: Money;
  propertyBreakdown: Array<{
    propertyId: PropertyId;
    address: Address;
    revenue: Money;
    occupancyRate: number;
  }>;
  generatedAt: Date;
}

/** Occupancy report */
export interface OccupancyReport {
  period: { from: Date; to: Date };
  totalProperties: number;
  occupiedProperties: number;
  vacantProperties: number;
  occupancyRate: number;
  byPropertyType: Record<PropertyType, {
    total: number;
    occupied: number;
    rate: number;
  }>;
  generatedAt: Date;
}

/** Payment summary report */
export interface PaymentSummaryReport {
  period: { from: Date; to: Date };
  totalReceived: Money;
  totalPending: Money;
  totalOverdue: Money;
  paymentsByType: Record<PaymentType, Money>;
  overdueContracts: Array<{
    contractId: LeaseContractId;
    tenantId: TenantId;
    overdueAmount: Money;
    daysPastDue: number;
  }>;
  generatedAt: Date;
}

/** Maintenance summary report */
export interface MaintenanceSummaryReport {
  period: { from: Date; to: Date };
  totalRequests: number;
  completedRequests: number;
  pendingRequests: number;
  byUrgency: Record<UrgencyLevel, number>;
  averageResolutionDays: number;
  totalCost: Money;
  generatedAt: Date;
}
