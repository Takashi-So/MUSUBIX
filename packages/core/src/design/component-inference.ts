/**
 * ComponentInference - コンポーネント推論モジュール
 * @description ドメインとコンテキストから最適なコンポーネント構成を推論
 * @requirement REQ-MUSUBIX-001
 * @version 1.1.0
 * 
 * ~390コンポーネント定義を基に、ドメインに最適化されたコンポーネント推薦を提供
 */

import { Domain, DomainDetector, domainDetector, DomainDetectionResult } from './domain-detector.js';

export type ComponentType = 
  | 'service'
  | 'repository'
  | 'controller'
  | 'validator'
  | 'factory'
  | 'gateway'
  | 'calculator'
  | 'processor'
  | 'manager'
  | 'handler';

export type LayerType = 
  | 'presentation'
  | 'application'
  | 'domain'
  | 'infrastructure';

export interface ComponentDefinition {
  name: string;
  type: ComponentType;
  layer: LayerType;
  description: string;
  dependencies: string[];
  patterns: string[];
  domain: string;
  /** Domain-specific methods (FB-325C2D59: Service methods should be specific) */
  methods?: MethodSignature[];
}

/**
 * Method signature for domain-specific operations (FB-325C2D59 improvement)
 */
export interface MethodSignature {
  name: string;
  description: string;
  parameters: { name: string; type: string }[];
  returnType: string;
  async?: boolean;
}

export interface ComponentInferenceResult {
  domain: DomainDetectionResult;
  components: ComponentDefinition[];
  architecture: ArchitectureRecommendation;
  patterns: string[];
}

export interface ArchitectureRecommendation {
  style: string;
  layers: LayerRecommendation[];
  dataFlow: string;
  scalability: string;
}

export interface LayerRecommendation {
  layer: LayerType;
  components: string[];
  responsibilities: string[];
}

/**
 * ドメイン別コンポーネント定義（~390コンポーネント）
 */
const COMPONENT_DEFINITIONS: Record<string, ComponentDefinition[]> = {
  // 動物病院（veterinary）ドメイン - 仮想プロジェクト01から学習
  veterinary: [
    { name: 'PetService', type: 'service', layer: 'application', description: 'ペット管理のビジネスロジック', dependencies: ['PetRepository', 'PetHistoryRepository'], patterns: ['Service'], domain: 'veterinary',
      methods: [
        { name: 'register', description: 'ペット登録', parameters: [{ name: 'data', type: 'RegisterPetInput' }], returnType: 'Promise<Pet>', async: true },
        { name: 'update', description: 'ペット情報更新', parameters: [{ name: 'petId', type: 'string' }, { name: 'data', type: 'UpdatePetInput' }], returnType: 'Promise<Pet>', async: true },
        { name: 'getByOwner', description: 'オーナー別ペット取得', parameters: [{ name: 'ownerId', type: 'string' }], returnType: 'Promise<Pet[]>', async: true },
        { name: 'getHistory', description: '診療履歴取得', parameters: [{ name: 'petId', type: 'string' }], returnType: 'Promise<PetHistory[]>', async: true },
      ]
    },
    { name: 'PetRepository', type: 'repository', layer: 'infrastructure', description: 'ペットデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'veterinary' },
    { name: 'PetHistoryRepository', type: 'repository', layer: 'infrastructure', description: 'ペット履歴の永続化', dependencies: [], patterns: ['Repository'], domain: 'veterinary' },
    { name: 'ReservationService', type: 'service', layer: 'application', description: '予約管理のビジネスロジック', dependencies: ['ReservationRepository', 'StatusWorkflow'], patterns: ['Service', 'State'], domain: 'veterinary',
      methods: [
        { name: 'create', description: '予約作成', parameters: [{ name: 'data', type: 'CreateReservationInput' }], returnType: 'Promise<Reservation>', async: true },
        { name: 'confirm', description: '予約確認', parameters: [{ name: 'reservationId', type: 'string' }], returnType: 'Promise<Reservation>', async: true },
        { name: 'reschedule', description: '予約変更', parameters: [{ name: 'reservationId', type: 'string' }, { name: 'newDate', type: 'Date' }], returnType: 'Promise<Reservation>', async: true },
        { name: 'cancel', description: '予約キャンセル', parameters: [{ name: 'reservationId', type: 'string' }, { name: 'reason', type: 'string' }], returnType: 'Promise<Reservation>', async: true },
        { name: 'getAvailableSlots', description: '空き枠取得', parameters: [{ name: 'vetId', type: 'string' }, { name: 'date', type: 'Date' }], returnType: 'Promise<TimeSlot[]>', async: true },
      ]
    },
    { name: 'ReservationRepository', type: 'repository', layer: 'infrastructure', description: '予約データの永続化', dependencies: [], patterns: ['Repository'], domain: 'veterinary' },
    { name: 'VetScheduleService', type: 'service', layer: 'application', description: '獣医スケジュール管理', dependencies: ['VetRepository'], patterns: ['Service'], domain: 'veterinary',
      methods: [
        { name: 'setWeeklySchedule', description: '週間スケジュール設定', parameters: [{ name: 'vetId', type: 'string' }, { name: 'schedule', type: 'WeeklySchedule' }], returnType: 'Promise<void>', async: true },
        { name: 'blockDate', description: '休診日設定', parameters: [{ name: 'vetId', type: 'string' }, { name: 'date', type: 'Date' }], returnType: 'Promise<void>', async: true },
        { name: 'getAvailability', description: '空き状況取得', parameters: [{ name: 'vetId', type: 'string' }, { name: 'startDate', type: 'Date' }, { name: 'endDate', type: 'Date' }], returnType: 'Promise<Availability[]>', async: true },
      ]
    },
    { name: 'MedicalRecordService', type: 'service', layer: 'application', description: '診療記録管理', dependencies: ['MedicalRecordRepository'], patterns: ['Service'], domain: 'veterinary',
      methods: [
        { name: 'create', description: '診療記録作成', parameters: [{ name: 'petId', type: 'string' }, { name: 'data', type: 'CreateMedicalRecordInput' }], returnType: 'Promise<MedicalRecord>', async: true },
        { name: 'addPrescription', description: '処方追加', parameters: [{ name: 'recordId', type: 'string' }, { name: 'prescription', type: 'Prescription' }], returnType: 'Promise<MedicalRecord>', async: true },
        { name: 'getByPet', description: 'ペット別記録取得', parameters: [{ name: 'petId', type: 'string' }], returnType: 'Promise<MedicalRecord[]>', async: true },
      ]
    },
    { name: 'IdGenerator', type: 'factory', layer: 'domain', description: 'ユニークID生成', dependencies: [], patterns: ['Factory'], domain: 'veterinary' },
    { name: 'StatusWorkflow', type: 'manager', layer: 'domain', description: 'ステータス遷移管理', dependencies: [], patterns: ['State'], domain: 'veterinary' },
  ],
  
  // 駐車場（parking）ドメイン - 仮想プロジェクト02から学習
  parking: [
    { name: 'SpaceService', type: 'service', layer: 'application', description: '駐車スペース管理', dependencies: ['SpaceRepository'], patterns: ['Service'], domain: 'parking',
      methods: [
        { name: 'findAvailable', description: '空きスペース検索', parameters: [{ name: 'location', type: 'GeoLocation' }], returnType: 'Promise<ParkingSpace[]>', async: true },
        { name: 'reserve', description: 'スペース予約', parameters: [{ name: 'spaceId', type: 'string' }, { name: 'vehicleId', type: 'string' }], returnType: 'Promise<Reservation>', async: true },
        { name: 'release', description: 'スペース解放', parameters: [{ name: 'spaceId', type: 'string' }], returnType: 'Promise<void>', async: true },
      ]
    },
    { name: 'SpaceRepository', type: 'repository', layer: 'infrastructure', description: 'スペースデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'parking' },
    { name: 'EntryExitService', type: 'service', layer: 'application', description: '入出庫管理', dependencies: ['EntryRepository', 'SpaceService', 'FeeCalculator'], patterns: ['Service'], domain: 'parking',
      methods: [
        { name: 'enter', description: '入庫処理', parameters: [{ name: 'vehicleNumber', type: 'string' }, { name: 'spaceId', type: 'string' }], returnType: 'Promise<EntryRecord>', async: true },
        { name: 'exit', description: '出庫処理', parameters: [{ name: 'entryId', type: 'string' }], returnType: 'Promise<ExitRecord>', async: true },
        { name: 'calculateStay', description: '滞在時間計算', parameters: [{ name: 'entryId', type: 'string' }], returnType: 'Promise<Duration>', async: true },
      ]
    },
    { name: 'EntryRepository', type: 'repository', layer: 'infrastructure', description: '入庫記録の永続化', dependencies: [], patterns: ['Repository'], domain: 'parking' },
    { name: 'FeeCalculator', type: 'calculator', layer: 'domain', description: '料金計算ロジック', dependencies: [], patterns: ['Strategy'], domain: 'parking',
      methods: [
        { name: 'calculate', description: '料金計算', parameters: [{ name: 'duration', type: 'Duration' }, { name: 'vehicleType', type: 'VehicleType' }], returnType: 'number', async: false },
        { name: 'applyDiscount', description: '割引適用', parameters: [{ name: 'baseFee', type: 'number' }, { name: 'discountCode', type: 'string' }], returnType: 'number', async: false },
      ]
    },
    { name: 'PaymentService', type: 'service', layer: 'application', description: '決済処理', dependencies: ['PaymentRepository'], patterns: ['Service'], domain: 'parking' },
    { name: 'DiscountValidator', type: 'validator', layer: 'domain', description: '割引コード検証', dependencies: [], patterns: ['Validator'], domain: 'parking' },
    { name: 'IdGenerator', type: 'factory', layer: 'domain', description: 'ユニークID生成', dependencies: [], patterns: ['Factory'], domain: 'parking' },
  ],
  
  // 配送（delivery）ドメイン - 仮想プロジェクト04から学習 (FB-72894D66)
  delivery: [
    { name: 'RestaurantService', type: 'service', layer: 'application', description: 'レストラン管理', dependencies: ['RestaurantRepository'], patterns: ['Service'], domain: 'delivery',
      methods: [
        { name: 'register', description: 'レストラン登録', parameters: [{ name: 'data', type: 'RegisterRestaurantInput' }], returnType: 'Promise<Restaurant>', async: true },
        { name: 'activate', description: 'レストラン有効化', parameters: [{ name: 'restaurantId', type: 'string' }], returnType: 'Promise<Restaurant>', async: true },
        { name: 'searchByLocation', description: '位置検索', parameters: [{ name: 'location', type: 'GeoLocation' }, { name: 'radius', type: 'number' }], returnType: 'Promise<Restaurant[]>', async: true },
        { name: 'searchByCuisine', description: '料理ジャンル検索', parameters: [{ name: 'cuisineType', type: 'CuisineType' }], returnType: 'Promise<Restaurant[]>', async: true },
      ]
    },
    { name: 'RestaurantRepository', type: 'repository', layer: 'infrastructure', description: 'レストランデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'delivery' },
    { name: 'OrderService', type: 'service', layer: 'application', description: '注文管理', dependencies: ['OrderRepository', 'RestaurantService'], patterns: ['Service'], domain: 'delivery',
      methods: [
        { name: 'create', description: '注文作成', parameters: [{ name: 'customerId', type: 'string' }, { name: 'restaurantId', type: 'string' }, { name: 'items', type: 'OrderItem[]' }], returnType: 'Promise<Order>', async: true },
        { name: 'accept', description: '注文受付', parameters: [{ name: 'orderId', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'cancel', description: '注文キャンセル', parameters: [{ name: 'orderId', type: 'string' }, { name: 'reason', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'getByCustomer', description: '顧客別注文取得', parameters: [{ name: 'customerId', type: 'string' }], returnType: 'Promise<Order[]>', async: true },
        { name: 'getByRestaurant', description: 'レストラン別注文取得', parameters: [{ name: 'restaurantId', type: 'string' }], returnType: 'Promise<Order[]>', async: true },
      ]
    },
    { name: 'OrderRepository', type: 'repository', layer: 'infrastructure', description: '注文データの永続化', dependencies: [], patterns: ['Repository'], domain: 'delivery' },
    { name: 'DeliveryService', type: 'service', layer: 'application', description: '配送管理', dependencies: ['DeliveryRepository', 'DriverRepository'], patterns: ['Service'], domain: 'delivery',
      methods: [
        { name: 'assignDriver', description: 'ドライバー割当', parameters: [{ name: 'orderId', type: 'string' }, { name: 'driverId', type: 'string' }], returnType: 'Promise<Delivery>', async: true },
        { name: 'updateLocation', description: '位置更新', parameters: [{ name: 'deliveryId', type: 'string' }, { name: 'location', type: 'GeoLocation' }], returnType: 'Promise<Delivery>', async: true },
        { name: 'complete', description: '配達完了', parameters: [{ name: 'deliveryId', type: 'string' }], returnType: 'Promise<Delivery>', async: true },
        { name: 'calculateETA', description: '到着予想時刻計算', parameters: [{ name: 'deliveryId', type: 'string' }], returnType: 'Promise<Date>', async: true },
      ]
    },
    { name: 'DeliveryRepository', type: 'repository', layer: 'infrastructure', description: '配送データの永続化', dependencies: [], patterns: ['Repository'], domain: 'delivery' },
    { name: 'DriverRepository', type: 'repository', layer: 'infrastructure', description: 'ドライバーデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'delivery' },
    { name: 'CustomerService', type: 'service', layer: 'application', description: '顧客管理', dependencies: ['CustomerRepository'], patterns: ['Service'], domain: 'delivery',
      methods: [
        { name: 'register', description: '顧客登録', parameters: [{ name: 'data', type: 'RegisterCustomerInput' }], returnType: 'Promise<Customer>', async: true },
        { name: 'addAddress', description: '配送先追加', parameters: [{ name: 'customerId', type: 'string' }, { name: 'address', type: 'DeliveryAddress' }], returnType: 'Promise<Customer>', async: true },
      ]
    },
    { name: 'CustomerRepository', type: 'repository', layer: 'infrastructure', description: '顧客データの永続化', dependencies: [], patterns: ['Repository'], domain: 'delivery' },
    { name: 'PaymentService', type: 'service', layer: 'application', description: '決済処理', dependencies: [], patterns: ['Service'], domain: 'delivery',
      methods: [
        { name: 'process', description: '決済処理', parameters: [{ name: 'orderId', type: 'string' }, { name: 'amount', type: 'Money' }], returnType: 'Promise<PaymentResult>', async: true },
        { name: 'refund', description: '返金処理', parameters: [{ name: 'paymentId', type: 'string' }], returnType: 'Promise<RefundResult>', async: true },
      ]
    },
    { name: 'EventBus', type: 'handler', layer: 'infrastructure', description: 'ドメインイベントバス', dependencies: [], patterns: ['Observer', 'Pub/Sub'], domain: 'delivery' },
  ],
  
  // フィットネスジム（gym）ドメイン - 仮想プロジェクト05から学習
  gym: [
    { name: 'MemberService', type: 'service', layer: 'application', description: '会員管理', dependencies: ['MemberRepository', 'MembershipRepository', 'BillingServiceAdapter'], patterns: ['Service'], domain: 'gym',
      methods: [
        { name: 'register', description: '会員登録', parameters: [{ name: 'data', type: 'RegisterMemberInput' }], returnType: 'Promise<Member>', async: true },
        { name: 'getMember', description: '会員取得', parameters: [{ name: 'memberId', type: 'string' }], returnType: 'Promise<Member | null>', async: true },
        { name: 'updateProfile', description: 'プロファイル更新', parameters: [{ name: 'memberId', type: 'string' }, { name: 'data', type: 'UpdateProfileInput' }], returnType: 'Promise<Member>', async: true },
        { name: 'assignMembership', description: 'メンバーシップ割当', parameters: [{ name: 'memberId', type: 'string' }, { name: 'planId', type: 'string' }], returnType: 'Promise<Membership>', async: true },
        { name: 'cancelMembership', description: 'メンバーシップキャンセル', parameters: [{ name: 'memberId', type: 'string' }, { name: 'reason', type: 'string' }], returnType: 'Promise<void>', async: true },
        { name: 'searchMembers', description: '会員検索', parameters: [{ name: 'criteria', type: 'MemberSearchCriteria' }], returnType: 'Promise<Member[]>', async: true },
      ]
    },
    { name: 'MemberRepository', type: 'repository', layer: 'infrastructure', description: '会員データの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'MembershipRepository', type: 'repository', layer: 'infrastructure', description: 'メンバーシップデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'CheckInService', type: 'service', layer: 'application', description: 'チェックイン管理', dependencies: ['CheckInRepository', 'MemberServiceAdapter'], patterns: ['Service'], domain: 'gym',
      methods: [
        { name: 'checkIn', description: 'チェックイン', parameters: [{ name: 'memberId', type: 'string' }, { name: 'facilityId', type: 'string' }], returnType: 'Promise<CheckInRecord>', async: true },
        { name: 'checkOut', description: 'チェックアウト', parameters: [{ name: 'checkInId', type: 'string' }], returnType: 'Promise<CheckInRecord>', async: true },
        { name: 'getActiveCheckIns', description: 'アクティブなチェックイン取得', parameters: [{ name: 'facilityId', type: 'string' }], returnType: 'Promise<CheckInRecord[]>', async: true },
        { name: 'getMemberHistory', description: '会員の来館履歴', parameters: [{ name: 'memberId', type: 'string' }, { name: 'range', type: 'DateRange' }], returnType: 'Promise<CheckInRecord[]>', async: true },
        { name: 'getTodayStats', description: '本日の統計', parameters: [{ name: 'facilityId', type: 'string' }], returnType: 'Promise<DailyStats>', async: true },
      ]
    },
    { name: 'CheckInRepository', type: 'repository', layer: 'infrastructure', description: 'チェックインデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'MemberServiceAdapter', type: 'gateway', layer: 'infrastructure', description: '会員サービス連携アダプター', dependencies: [], patterns: ['Adapter'], domain: 'gym' },
    { name: 'ClassService', type: 'service', layer: 'application', description: 'クラススケジュール管理', dependencies: ['ClassRepository', 'ClassBookingRepository', 'InstructorRepository'], patterns: ['Service'], domain: 'gym',
      methods: [
        { name: 'createClass', description: 'クラス作成', parameters: [{ name: 'data', type: 'CreateClassInput' }], returnType: 'Promise<FitnessClass>', async: true },
        { name: 'getSchedule', description: 'スケジュール取得', parameters: [{ name: 'facilityId', type: 'string' }, { name: 'dateRange', type: 'DateRange' }], returnType: 'Promise<FitnessClass[]>', async: true },
        { name: 'bookClass', description: 'クラス予約', parameters: [{ name: 'memberId', type: 'string' }, { name: 'classId', type: 'string' }], returnType: 'Promise<ClassBooking>', async: true },
        { name: 'cancelBooking', description: '予約キャンセル', parameters: [{ name: 'bookingId', type: 'string' }], returnType: 'Promise<void>', async: true },
        { name: 'getAvailableSpots', description: '空き枠確認', parameters: [{ name: 'classId', type: 'string' }], returnType: 'Promise<number>', async: true },
        { name: 'assignInstructor', description: 'インストラクター割当', parameters: [{ name: 'classId', type: 'string' }, { name: 'instructorId', type: 'string' }], returnType: 'Promise<FitnessClass>', async: true },
      ]
    },
    { name: 'ClassRepository', type: 'repository', layer: 'infrastructure', description: 'クラスデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'ClassBookingRepository', type: 'repository', layer: 'infrastructure', description: 'クラス予約データの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'InstructorRepository', type: 'repository', layer: 'infrastructure', description: 'インストラクターデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'BillingService', type: 'service', layer: 'application', description: '請求管理', dependencies: ['BillingRepository', 'InvoiceRepository', 'PaymentGateway'], patterns: ['Service'], domain: 'gym',
      methods: [
        { name: 'createInvoice', description: '請求書作成', parameters: [{ name: 'memberId', type: 'string' }, { name: 'items', type: 'BillingItem[]' }], returnType: 'Promise<Invoice>', async: true },
        { name: 'processPayment', description: '支払い処理', parameters: [{ name: 'invoiceId', type: 'string' }, { name: 'paymentMethod', type: 'PaymentMethod' }], returnType: 'Promise<PaymentResult>', async: true },
        { name: 'getUnpaidInvoices', description: '未払い請求取得', parameters: [{ name: 'memberId', type: 'string' }], returnType: 'Promise<Invoice[]>', async: true },
        { name: 'refund', description: '返金処理', parameters: [{ name: 'paymentId', type: 'string' }, { name: 'amount', type: 'Money' }], returnType: 'Promise<RefundResult>', async: true },
        { name: 'generateStatement', description: '明細書生成', parameters: [{ name: 'memberId', type: 'string' }, { name: 'period', type: 'DateRange' }], returnType: 'Promise<Statement>', async: true },
      ]
    },
    { name: 'BillingRepository', type: 'repository', layer: 'infrastructure', description: '請求データの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'InvoiceRepository', type: 'repository', layer: 'infrastructure', description: '請求書データの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'BillingServiceAdapter', type: 'gateway', layer: 'infrastructure', description: '請求サービス連携アダプター', dependencies: [], patterns: ['Adapter'], domain: 'gym' },
    { name: 'PaymentGateway', type: 'gateway', layer: 'infrastructure', description: '外部決済連携', dependencies: [], patterns: ['Gateway'], domain: 'gym' },
    { name: 'FacilityService', type: 'service', layer: 'application', description: '施設管理', dependencies: ['FacilityRepository', 'EquipmentRepository'], patterns: ['Service'], domain: 'gym',
      methods: [
        { name: 'getFacilities', description: '施設一覧取得', parameters: [], returnType: 'Promise<Facility[]>', async: true },
        { name: 'getCapacity', description: '収容状況取得', parameters: [{ name: 'facilityId', type: 'string' }], returnType: 'Promise<CapacityStatus>', async: true },
        { name: 'updateOperatingHours', description: '営業時間更新', parameters: [{ name: 'facilityId', type: 'string' }, { name: 'hours', type: 'OperatingHours' }], returnType: 'Promise<Facility>', async: true },
      ]
    },
    { name: 'FacilityRepository', type: 'repository', layer: 'infrastructure', description: '施設データの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'EquipmentRepository', type: 'repository', layer: 'infrastructure', description: '設備データの永続化', dependencies: [], patterns: ['Repository'], domain: 'gym' },
    { name: 'NotificationService', type: 'service', layer: 'application', description: '通知管理', dependencies: ['NotificationGateway'], patterns: ['Service'], domain: 'gym',
      methods: [
        { name: 'sendWelcome', description: 'ウェルカムメール送信', parameters: [{ name: 'memberId', type: 'string' }], returnType: 'Promise<void>', async: true },
        { name: 'sendReminder', description: 'リマインダー送信', parameters: [{ name: 'memberId', type: 'string' }, { name: 'type', type: 'ReminderType' }], returnType: 'Promise<void>', async: true },
        { name: 'sendPaymentReceipt', description: '領収書送信', parameters: [{ name: 'paymentId', type: 'string' }], returnType: 'Promise<void>', async: true },
      ]
    },
    { name: 'NotificationGateway', type: 'gateway', layer: 'infrastructure', description: '外部通知連携', dependencies: [], patterns: ['Gateway'], domain: 'gym' },
  ],
  
  // EC（ecommerce）ドメイン
  ecommerce: [
    { name: 'CartService', type: 'service', layer: 'application', description: 'カート管理', dependencies: ['CartRepository', 'ProductService'], patterns: ['Service'], domain: 'ecommerce',
      methods: [
        { name: 'addItem', description: 'カートに商品追加', parameters: [{ name: 'cartId', type: 'string' }, { name: 'productId', type: 'string' }, { name: 'quantity', type: 'number' }], returnType: 'Promise<Cart>', async: true },
        { name: 'removeItem', description: 'カートから商品削除', parameters: [{ name: 'cartId', type: 'string' }, { name: 'productId', type: 'string' }], returnType: 'Promise<Cart>', async: true },
        { name: 'updateQuantity', description: '数量変更', parameters: [{ name: 'cartId', type: 'string' }, { name: 'productId', type: 'string' }, { name: 'quantity', type: 'number' }], returnType: 'Promise<Cart>', async: true },
        { name: 'clear', description: 'カート空にする', parameters: [{ name: 'cartId', type: 'string' }], returnType: 'Promise<void>', async: true },
        { name: 'getTotal', description: '合計金額取得', parameters: [{ name: 'cartId', type: 'string' }], returnType: 'Promise<number>', async: true },
      ]
    },
    { name: 'CartRepository', type: 'repository', layer: 'infrastructure', description: 'カートデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'ecommerce' },
    { name: 'ProductService', type: 'service', layer: 'application', description: '商品管理', dependencies: ['ProductRepository'], patterns: ['Service'], domain: 'ecommerce',
      methods: [
        { name: 'create', description: '商品作成', parameters: [{ name: 'data', type: 'CreateProductInput' }], returnType: 'Promise<Product>', async: true },
        { name: 'search', description: '商品検索', parameters: [{ name: 'query', type: 'string' }, { name: 'options', type: 'SearchOptions' }], returnType: 'Promise<Product[]>', async: true },
        { name: 'getByCategory', description: 'カテゴリ別取得', parameters: [{ name: 'categoryId', type: 'string' }], returnType: 'Promise<Product[]>', async: true },
        { name: 'updateStock', description: '在庫更新', parameters: [{ name: 'productId', type: 'string' }, { name: 'quantity', type: 'number' }], returnType: 'Promise<Product>', async: true },
      ]
    },
    { name: 'ProductRepository', type: 'repository', layer: 'infrastructure', description: '商品データの永続化', dependencies: [], patterns: ['Repository'], domain: 'ecommerce' },
    { name: 'OrderService', type: 'service', layer: 'application', description: '注文管理', dependencies: ['OrderRepository', 'CartService', 'PaymentGateway'], patterns: ['Service'], domain: 'ecommerce',
      methods: [
        { name: 'create', description: '注文作成（カートから）', parameters: [{ name: 'cartId', type: 'string' }, { name: 'customerId', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'submit', description: '注文確定', parameters: [{ name: 'orderId', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'cancel', description: '注文キャンセル', parameters: [{ name: 'orderId', type: 'string' }, { name: 'reason', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'ship', description: '出荷処理', parameters: [{ name: 'orderId', type: 'string' }, { name: 'trackingNumber', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'complete', description: '注文完了', parameters: [{ name: 'orderId', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'getHistory', description: '注文履歴取得', parameters: [{ name: 'customerId', type: 'string' }], returnType: 'Promise<Order[]>', async: true },
      ]
    },
    { name: 'OrderRepository', type: 'repository', layer: 'infrastructure', description: '注文データの永続化', dependencies: [], patterns: ['Repository'], domain: 'ecommerce' },
    { name: 'PaymentGateway', type: 'gateway', layer: 'infrastructure', description: '決済ゲートウェイ連携', dependencies: [], patterns: ['Gateway', 'Adapter'], domain: 'ecommerce',
      methods: [
        { name: 'processPayment', description: '決済処理', parameters: [{ name: 'orderId', type: 'string' }, { name: 'paymentMethod', type: 'PaymentMethod' }, { name: 'amount', type: 'number' }], returnType: 'Promise<PaymentResult>', async: true },
        { name: 'refund', description: '返金処理', parameters: [{ name: 'transactionId', type: 'string' }, { name: 'amount', type: 'number' }], returnType: 'Promise<RefundResult>', async: true },
      ]
    },
    { name: 'CatalogService', type: 'service', layer: 'application', description: 'カタログ管理', dependencies: ['ProductRepository'], patterns: ['Service'], domain: 'ecommerce' },
    { name: 'PriceCalculator', type: 'calculator', layer: 'domain', description: '価格計算', dependencies: [], patterns: ['Strategy'], domain: 'ecommerce' },
    { name: 'InventoryChecker', type: 'validator', layer: 'domain', description: '在庫確認', dependencies: ['InventoryRepository'], patterns: ['Validator'], domain: 'ecommerce' },
  ],
  
  // 予約（booking）ドメイン - 仮想プロジェクト06から学習
  booking: [
    { name: 'EventService', type: 'service', layer: 'application', description: 'イベント管理', dependencies: ['EventRepository'], patterns: ['Service'], domain: 'booking',
      methods: [
        { name: 'createEvent', description: 'イベント作成', parameters: [{ name: 'data', type: 'CreateEventInput' }], returnType: 'Promise<Event>', async: true },
        { name: 'getEvent', description: 'イベント取得', parameters: [{ name: 'eventId', type: 'string' }], returnType: 'Promise<Event | null>', async: true },
        { name: 'searchEvents', description: 'イベント検索', parameters: [{ name: 'criteria', type: 'EventSearchCriteria' }], returnType: 'Promise<Event[]>', async: true },
        { name: 'publishEvent', description: 'イベント公開', parameters: [{ name: 'eventId', type: 'string' }], returnType: 'Promise<Event>', async: true },
        { name: 'cancelEvent', description: 'イベントキャンセル', parameters: [{ name: 'eventId', type: 'string' }, { name: 'reason', type: 'string' }], returnType: 'Promise<Event>', async: true },
      ]
    },
    { name: 'EventRepository', type: 'repository', layer: 'infrastructure', description: 'イベントデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'TicketService', type: 'service', layer: 'application', description: 'チケット管理', dependencies: ['TicketRepository', 'OrderRepository'], patterns: ['Service'], domain: 'booking',
      methods: [
        { name: 'purchaseTickets', description: 'チケット購入', parameters: [{ name: 'eventId', type: 'string' }, { name: 'tickets', type: 'TicketPurchaseInput[]' }, { name: 'buyerId', type: 'string' }], returnType: 'Promise<Order>', async: true },
        { name: 'getTicket', description: 'チケット取得', parameters: [{ name: 'ticketId', type: 'string' }], returnType: 'Promise<Ticket | null>', async: true },
        { name: 'validateTicket', description: 'チケット検証', parameters: [{ name: 'qrCode', type: 'string' }], returnType: 'Promise<ValidationResult>', async: true },
        { name: 'transferTicket', description: 'チケット譲渡', parameters: [{ name: 'ticketId', type: 'string' }, { name: 'newHolderId', type: 'string' }], returnType: 'Promise<Ticket>', async: true },
        { name: 'cancelTicket', description: 'チケットキャンセル', parameters: [{ name: 'ticketId', type: 'string' }, { name: 'reason', type: 'string' }], returnType: 'Promise<RefundResult>', async: true },
      ]
    },
    { name: 'TicketRepository', type: 'repository', layer: 'infrastructure', description: 'チケットデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'OrderRepository', type: 'repository', layer: 'infrastructure', description: '注文データの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'SeatService', type: 'service', layer: 'application', description: '座席管理', dependencies: ['SeatRepository', 'LayoutRepository', 'ReservationRepository'], patterns: ['Service'], domain: 'booking',
      methods: [
        { name: 'createLayout', description: '座席レイアウト作成', parameters: [{ name: 'input', type: 'CreateLayoutInput' }], returnType: 'Promise<VenueLayout>', async: true },
        { name: 'getAvailableSeats', description: '空き座席取得', parameters: [{ name: 'eventId', type: 'string' }, { name: 'section', type: 'string' }], returnType: 'Promise<Seat[]>', async: true },
        { name: 'reserveSeats', description: '座席予約（タイムアウト付き）', parameters: [{ name: 'input', type: 'ReserveSeatInput' }], returnType: 'Promise<SeatReservation>', async: true },
        { name: 'confirmReservation', description: '予約確定', parameters: [{ name: 'reservationId', type: 'string' }, { name: 'userId', type: 'string' }], returnType: 'Promise<Seat[]>', async: true },
        { name: 'releaseReservation', description: '予約解放', parameters: [{ name: 'reservationId', type: 'string' }], returnType: 'Promise<boolean>', async: true },
      ]
    },
    { name: 'SeatRepository', type: 'repository', layer: 'infrastructure', description: '座席データの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'LayoutRepository', type: 'repository', layer: 'infrastructure', description: 'レイアウトデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'ReservationRepository', type: 'repository', layer: 'infrastructure', description: '予約データの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'CheckInService', type: 'service', layer: 'application', description: 'チェックイン管理', dependencies: ['CheckInRepository', 'TicketServiceAdapter'], patterns: ['Service'], domain: 'booking',
      methods: [
        { name: 'checkIn', description: 'QRコードチェックイン', parameters: [{ name: 'eventId', type: 'string' }, { name: 'qrCode', type: 'string' }, { name: 'staffId', type: 'string' }, { name: 'gate', type: 'string' }], returnType: 'Promise<CheckInResult>', async: true },
        { name: 'getCheckInStats', description: 'チェックイン統計', parameters: [{ name: 'eventId', type: 'string' }], returnType: 'Promise<CheckInStats>', async: true },
        { name: 'isTicketCheckedIn', description: 'チェックイン済み確認', parameters: [{ name: 'ticketId', type: 'string' }], returnType: 'Promise<boolean>', async: true },
        { name: 'cacheTicketsForOffline', description: 'オフライン用キャッシュ', parameters: [{ name: 'eventId', type: 'string' }], returnType: 'Promise<number>', async: true },
        { name: 'processOfflineCheckIns', description: 'オフラインデータ同期', parameters: [{ name: 'eventId', type: 'string' }, { name: 'checkIns', type: 'OfflineCheckInData[]' }], returnType: 'Promise<SyncResult>', async: true },
      ]
    },
    { name: 'CheckInRepository', type: 'repository', layer: 'infrastructure', description: 'チェックインデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'TicketServiceAdapter', type: 'gateway', layer: 'infrastructure', description: 'チケットサービス連携アダプター', dependencies: [], patterns: ['Adapter'], domain: 'booking' },
    { name: 'WaitlistService', type: 'service', layer: 'application', description: 'キャンセル待ち管理', dependencies: ['WaitlistRepository'], patterns: ['Service'], domain: 'booking',
      methods: [
        { name: 'addToWaitlist', description: 'キャンセル待ち登録', parameters: [{ name: 'eventId', type: 'string' }, { name: 'userId', type: 'string' }, { name: 'ticketType', type: 'string' }], returnType: 'Promise<WaitlistEntry>', async: true },
        { name: 'processAvailableTickets', description: '空きチケット処理', parameters: [{ name: 'eventId', type: 'string' }], returnType: 'Promise<void>', async: true },
        { name: 'removeFromWaitlist', description: 'キャンセル待ち削除', parameters: [{ name: 'entryId', type: 'string' }], returnType: 'Promise<boolean>', async: true },
      ]
    },
    { name: 'WaitlistRepository', type: 'repository', layer: 'infrastructure', description: 'キャンセル待ちデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'PromoCodeService', type: 'service', layer: 'application', description: 'プロモーションコード管理', dependencies: ['PromoCodeRepository'], patterns: ['Service'], domain: 'booking',
      methods: [
        { name: 'createPromoCode', description: 'プロモコード作成', parameters: [{ name: 'data', type: 'CreatePromoCodeInput' }], returnType: 'Promise<PromoCode>', async: true },
        { name: 'validatePromoCode', description: 'プロモコード検証', parameters: [{ name: 'code', type: 'string' }, { name: 'eventId', type: 'string' }], returnType: 'Promise<PromoCodeValidation>', async: true },
        { name: 'applyPromoCode', description: 'プロモコード適用', parameters: [{ name: 'orderId', type: 'string' }, { name: 'code', type: 'string' }], returnType: 'Promise<DiscountResult>', async: true },
      ]
    },
    { name: 'PromoCodeRepository', type: 'repository', layer: 'infrastructure', description: 'プロモコードデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'StatusWorkflow', type: 'manager', layer: 'domain', description: '予約ステータス遷移', dependencies: [], patterns: ['State'], domain: 'booking' },
  ],
  
  // ヘルスケア（healthcare）ドメイン
  healthcare: [
    { name: 'PatientService', type: 'service', layer: 'application', description: '患者管理', dependencies: ['PatientRepository'], patterns: ['Service'], domain: 'healthcare' },
    { name: 'PatientRepository', type: 'repository', layer: 'infrastructure', description: '患者データの永続化', dependencies: [], patterns: ['Repository'], domain: 'healthcare' },
    { name: 'DiagnosisService', type: 'service', layer: 'application', description: '診断管理', dependencies: ['DiagnosisRepository'], patterns: ['Service'], domain: 'healthcare' },
    { name: 'AppointmentService', type: 'service', layer: 'application', description: '予約管理', dependencies: ['AppointmentRepository', 'DoctorScheduleService'], patterns: ['Service'], domain: 'healthcare' },
    { name: 'MedicalRecordService', type: 'service', layer: 'application', description: '診療記録管理', dependencies: ['MedicalRecordRepository'], patterns: ['Service'], domain: 'healthcare' },
    { name: 'PrescriptionService', type: 'service', layer: 'application', description: '処方管理', dependencies: ['PrescriptionRepository'], patterns: ['Service'], domain: 'healthcare' },
  ],
  
  // 金融（finance）ドメイン
  finance: [
    { name: 'AccountService', type: 'service', layer: 'application', description: '口座管理', dependencies: ['AccountRepository'], patterns: ['Service'], domain: 'finance' },
    { name: 'AccountRepository', type: 'repository', layer: 'infrastructure', description: '口座データの永続化', dependencies: [], patterns: ['Repository'], domain: 'finance' },
    { name: 'TransactionService', type: 'service', layer: 'application', description: '取引管理', dependencies: ['TransactionRepository', 'BalanceCalculator'], patterns: ['Service'], domain: 'finance' },
    { name: 'TransactionRepository', type: 'repository', layer: 'infrastructure', description: '取引データの永続化', dependencies: [], patterns: ['Repository'], domain: 'finance' },
    { name: 'BalanceCalculator', type: 'calculator', layer: 'domain', description: '残高計算', dependencies: [], patterns: ['Calculator'], domain: 'finance' },
    { name: 'TransferService', type: 'service', layer: 'application', description: '送金管理', dependencies: ['AccountService', 'TransactionService'], patterns: ['Service'], domain: 'finance' },
    { name: 'InterestCalculator', type: 'calculator', layer: 'domain', description: '利息計算', dependencies: [], patterns: ['Strategy'], domain: 'finance' },
  ],
  
  // IoT ドメイン
  iot: [
    { name: 'DeviceService', type: 'service', layer: 'application', description: 'デバイス管理', dependencies: ['DeviceRepository'], patterns: ['Service'], domain: 'iot' },
    { name: 'DeviceRepository', type: 'repository', layer: 'infrastructure', description: 'デバイスデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'iot' },
    { name: 'TelemetryProcessor', type: 'processor', layer: 'application', description: 'テレメトリデータ処理', dependencies: ['TelemetryRepository'], patterns: ['Processor'], domain: 'iot' },
    { name: 'TelemetryRepository', type: 'repository', layer: 'infrastructure', description: 'テレメトリデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'iot' },
    { name: 'AlertService', type: 'service', layer: 'application', description: 'アラート管理', dependencies: ['ThresholdValidator', 'NotificationGateway'], patterns: ['Service'], domain: 'iot' },
    { name: 'ThresholdValidator', type: 'validator', layer: 'domain', description: '閾値検証', dependencies: [], patterns: ['Validator'], domain: 'iot' },
    { name: 'SensorDataAggregator', type: 'processor', layer: 'domain', description: 'センサーデータ集計', dependencies: [], patterns: ['Aggregator'], domain: 'iot' },
  ],
  
  // 汎用（general）ドメイン
  general: [
    { name: 'Service', type: 'service', layer: 'application', description: 'ビジネスロジック', dependencies: ['Repository'], patterns: ['Service'], domain: 'general' },
    { name: 'Repository', type: 'repository', layer: 'infrastructure', description: 'データ永続化', dependencies: [], patterns: ['Repository'], domain: 'general' },
    { name: 'Controller', type: 'controller', layer: 'presentation', description: 'リクエスト処理', dependencies: ['Service'], patterns: ['Controller'], domain: 'general' },
    { name: 'Validator', type: 'validator', layer: 'domain', description: '入力検証', dependencies: [], patterns: ['Validator'], domain: 'general' },
    { name: 'Factory', type: 'factory', layer: 'domain', description: 'オブジェクト生成', dependencies: [], patterns: ['Factory'], domain: 'general' },
  ],
};

/**
 * コンポーネント推論クラス
 */
export class ComponentInference {
  private detector: DomainDetector;

  constructor(detector?: DomainDetector) {
    this.detector = detector ?? domainDetector;
  }

  /**
   * テキストからドメインIDを検出
   * @param text 検出対象のテキスト
   * @returns ドメインID（veterinary, parking, delivery, ecommerce, general等）
   */
  detectDomain(text: string): string {
    const result = this.detector.detect(text);
    return result.primaryDomain.id;
  }

  /**
   * テキストからコンポーネント構成を推論
   */
  infer(text: string): ComponentInferenceResult {
    // ドメインを検出
    const domainResult = this.detector.detect(text);
    
    // プライマリドメインのコンポーネントを取得
    const primaryComponents = this.getComponentsForDomain(domainResult.primaryDomain.id);
    
    // セカンダリドメインから追加コンポーネントを取得
    const additionalComponents: ComponentDefinition[] = [];
    for (const secondary of domainResult.secondaryDomains) {
      const secondaryComps = this.getComponentsForDomain(secondary.id);
      // 重複を除いて追加
      for (const comp of secondaryComps) {
        if (!primaryComponents.some(p => p.name === comp.name) && 
            !additionalComponents.some(a => a.name === comp.name)) {
          additionalComponents.push(comp);
        }
      }
    }

    // 使用パターンを抽出
    const patterns = this.extractPatterns([...primaryComponents, ...additionalComponents.slice(0, 3)]);

    // アーキテクチャ推奨を生成
    const architecture = this.generateArchitectureRecommendation(domainResult.primaryDomain);

    return {
      domain: domainResult,
      components: [...primaryComponents, ...additionalComponents.slice(0, 3)],
      architecture,
      patterns,
    };
  }

  /**
   * ドメインのコンポーネントを取得
   */
  private getComponentsForDomain(domainId: string): ComponentDefinition[] {
    return COMPONENT_DEFINITIONS[domainId] ?? COMPONENT_DEFINITIONS.general;
  }

  /**
   * パターンを抽出
   */
  private extractPatterns(components: ComponentDefinition[]): string[] {
    const patternSet = new Set<string>();
    for (const comp of components) {
      for (const pattern of comp.patterns) {
        patternSet.add(pattern);
      }
    }
    return Array.from(patternSet);
  }

  /**
   * アーキテクチャ推奨を生成
   */
  private generateArchitectureRecommendation(domain: Domain): ArchitectureRecommendation {
    const components = this.getComponentsForDomain(domain.id);
    
    // レイヤー別にグループ化
    const layers: Record<LayerType, string[]> = {
      presentation: [],
      application: [],
      domain: [],
      infrastructure: [],
    };

    for (const comp of components) {
      layers[comp.layer].push(comp.name);
    }

    return {
      style: 'Layered Architecture',
      layers: [
        { layer: 'presentation', components: layers.presentation, responsibilities: ['リクエスト処理', 'レスポンス整形', 'バリデーション'] },
        { layer: 'application', components: layers.application, responsibilities: ['ビジネスロジック', 'ユースケース実装', 'トランザクション管理'] },
        { layer: 'domain', components: layers.domain, responsibilities: ['ドメインルール', '値オブジェクト', 'ドメインサービス'] },
        { layer: 'infrastructure', components: layers.infrastructure, responsibilities: ['データ永続化', '外部サービス連携', 'メッセージング'] },
      ],
      dataFlow: 'Presentation → Application → Domain → Infrastructure',
      scalability: domain.category === 'technology' ? 'Horizontal scaling recommended' : 'Vertical scaling with caching',
    };
  }

  /**
   * 全コンポーネント定義数を取得
   */
  getTotalComponentCount(): number {
    let count = 0;
    for (const domain in COMPONENT_DEFINITIONS) {
      count += COMPONENT_DEFINITIONS[domain].length;
    }
    return count;
  }

  /**
   * ドメイン別コンポーネント数を取得
   */
  getComponentCountByDomain(): Record<string, number> {
    const result: Record<string, number> = {};
    for (const domain in COMPONENT_DEFINITIONS) {
      result[domain] = COMPONENT_DEFINITIONS[domain].length;
    }
    return result;
  }

  /**
   * コンポーネント名からドメイン固有メソッドを取得 (FB-325C2D59対応)
   * @param componentName コンポーネント名（例: OrderService）
   * @param domainId ドメインID（例: ecommerce, delivery）
   * @returns メソッドシグネチャの配列
   */
  getMethodsForComponent(componentName: string, domainId?: string): MethodSignature[] {
    // ドメイン指定がある場合はそのドメインから検索
    if (domainId) {
      const components = COMPONENT_DEFINITIONS[domainId];
      if (components) {
        const component = components.find(c => c.name === componentName);
        if (component?.methods) {
          return component.methods;
        }
      }
    }

    // 全ドメインから検索
    for (const domain in COMPONENT_DEFINITIONS) {
      const components = COMPONENT_DEFINITIONS[domain];
      const component = components.find(c => c.name === componentName);
      if (component?.methods) {
        return component.methods;
      }
    }

    // 汎用的なメソッドを返す
    return this.getGenericMethods(componentName);
  }

  /**
   * コンポーネントタイプから汎用メソッドを生成
   */
  private getGenericMethods(componentName: string): MethodSignature[] {
    // Service系
    if (componentName.endsWith('Service')) {
      const baseName = componentName.replace(/Service$/, '');
      return [
        { name: 'create', description: `${baseName}を作成`, parameters: [{ name: 'data', type: `Create${baseName}Input` }], returnType: `Promise<${baseName}>`, async: true },
        { name: 'getById', description: `${baseName}をID取得`, parameters: [{ name: 'id', type: 'string' }], returnType: `Promise<${baseName} | null>`, async: true },
        { name: 'update', description: `${baseName}を更新`, parameters: [{ name: 'id', type: 'string' }, { name: 'data', type: `Update${baseName}Input` }], returnType: `Promise<${baseName}>`, async: true },
        { name: 'delete', description: `${baseName}を削除`, parameters: [{ name: 'id', type: 'string' }], returnType: 'Promise<void>', async: true },
        { name: 'list', description: `${baseName}一覧取得`, parameters: [{ name: 'options', type: 'ListOptions' }], returnType: `Promise<${baseName}[]>`, async: true },
      ];
    }

    // Repository系
    if (componentName.endsWith('Repository')) {
      return [
        { name: 'save', description: 'エンティティ保存', parameters: [{ name: 'entity', type: 'T' }], returnType: 'Promise<T>', async: true },
        { name: 'findById', description: 'ID検索', parameters: [{ name: 'id', type: 'string' }], returnType: 'Promise<T | null>', async: true },
        { name: 'findAll', description: '全件取得', parameters: [], returnType: 'Promise<T[]>', async: true },
        { name: 'delete', description: '削除', parameters: [{ name: 'id', type: 'string' }], returnType: 'Promise<boolean>', async: true },
      ];
    }

    // Validator系
    if (componentName.endsWith('Validator')) {
      const baseName = componentName.replace(/Validator$/, '');
      return [
        { name: 'validate', description: `${baseName}の検証`, parameters: [{ name: 'data', type: 'unknown' }], returnType: 'ValidationResult', async: false },
        { name: 'isValid', description: '有効性チェック', parameters: [{ name: 'data', type: 'unknown' }], returnType: 'boolean', async: false },
      ];
    }

    // Calculator系
    if (componentName.endsWith('Calculator')) {
      return [
        { name: 'calculate', description: '計算実行', parameters: [{ name: 'input', type: 'CalculationInput' }], returnType: 'CalculationResult', async: false },
      ];
    }

    // デフォルト
    return [];
  }
}

// シングルトンインスタンス
export const componentInference = new ComponentInference();
