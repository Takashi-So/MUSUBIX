/**
 * DomainDetector - ドメイン自動検出モジュール
 * @description 要件や設計からドメインを自動検出し、最適なコンポーネントを推薦
 * @requirement REQ-MUSUBIX-001
 * @version 1.1.0
 * 
 * 60ドメイン対応:
 * - ビジネス系: ecommerce, finance, crm, hr, marketing
 * - 産業系: manufacturing, logistics, healthcare, agriculture, energy
 * - 技術系: iot, security, ai, analytics, telecom
 * - サービス系: education, travel, restaurant, hotel, etc.
 */

export type DomainCategory = 
  | 'business'
  | 'industry'
  | 'healthcare'
  | 'service'
  | 'technology'
  | 'general';

export interface Domain {
  id: string;
  name: string;
  nameJa: string;
  category: DomainCategory;
  keywords: string[];
  relatedDomains: string[];
}

export interface DomainDetectionResult {
  primaryDomain: Domain;
  secondaryDomains: Domain[];
  confidence: number;
  matchedKeywords: string[];
  suggestedComponents: string[];
}

/**
 * 60ドメイン定義
 */
export const DOMAINS: Domain[] = [
  // ビジネス系
  { id: 'general', name: 'General', nameJa: '汎用', category: 'general', keywords: ['system', 'application', 'service'], relatedDomains: [] },
  { id: 'ecommerce', name: 'E-Commerce', nameJa: 'EC・通販', category: 'business', keywords: ['cart', 'product', 'order', 'checkout', 'shop', 'store', 'catalog', 'price'], relatedDomains: ['payment', 'inventory', 'delivery'] },
  { id: 'finance', name: 'Finance', nameJa: '金融', category: 'business', keywords: ['account', 'transaction', 'balance', 'transfer', 'bank', 'loan', 'interest', 'deposit'], relatedDomains: ['payment', 'insurance'] },
  { id: 'crm', name: 'CRM', nameJa: '顧客管理', category: 'business', keywords: ['customer', 'lead', 'opportunity', 'contact', 'deal', 'pipeline', 'sales'], relatedDomains: ['marketing', 'analytics'] },
  { id: 'hr', name: 'HR', nameJa: '人事', category: 'business', keywords: ['employee', 'payroll', 'attendance', 'leave', 'recruitment', 'performance', 'salary'], relatedDomains: ['workflow', 'calendar'] },
  { id: 'marketing', name: 'Marketing', nameJa: 'マーケティング', category: 'business', keywords: ['campaign', 'audience', 'conversion', 'analytics', 'segment', 'promotion'], relatedDomains: ['crm', 'analytics'] },
  
  // 産業系
  { id: 'manufacturing', name: 'Manufacturing', nameJa: '製造', category: 'industry', keywords: ['production', 'assembly', 'quality', 'machine', 'factory', 'batch', 'bom'], relatedDomains: ['inventory', 'logistics'] },
  { id: 'logistics', name: 'Logistics', nameJa: '物流', category: 'industry', keywords: ['shipping', 'tracking', 'warehouse', 'route', 'fleet', 'freight', 'cargo'], relatedDomains: ['inventory', 'delivery'] },
  { id: 'agriculture', name: 'Agriculture', nameJa: '農業', category: 'industry', keywords: ['crop', 'harvest', 'farm', 'irrigation', 'soil', 'fertilizer', 'livestock'], relatedDomains: ['iot', 'weather'] },
  { id: 'energy', name: 'Energy', nameJa: 'エネルギー', category: 'industry', keywords: ['power', 'grid', 'consumption', 'meter', 'solar', 'wind', 'electricity'], relatedDomains: ['iot', 'analytics'] },
  
  // ヘルスケア系
  { id: 'healthcare', name: 'Healthcare', nameJa: 'ヘルスケア', category: 'healthcare', keywords: ['patient', 'diagnosis', 'treatment', 'medical', 'clinic', 'doctor', 'hospital'], relatedDomains: ['pharmacy', 'insurance'] },
  { id: 'pharmacy', name: 'Pharmacy', nameJa: '薬局', category: 'healthcare', keywords: ['prescription', 'medicine', 'drug', 'dosage', 'pharmacy', 'medication'], relatedDomains: ['healthcare', 'inventory'] },
  { id: 'veterinary', name: 'Veterinary', nameJa: '動物病院', category: 'healthcare', keywords: ['pet', 'animal', 'veterinarian', 'vaccination', 'vet', 'breed', 'owner', 'examination'], relatedDomains: ['booking', 'healthcare'] },
  
  // 技術系
  { id: 'iot', name: 'IoT', nameJa: 'IoT', category: 'technology', keywords: ['sensor', 'device', 'telemetry', 'gateway', 'mqtt', 'edge', 'actuator'], relatedDomains: ['analytics', 'notification'] },
  { id: 'security', name: 'Security', nameJa: 'セキュリティ', category: 'technology', keywords: ['authentication', 'authorization', 'token', 'access', 'permission', 'role', 'oauth'], relatedDomains: ['audit'] },
  { id: 'ai', name: 'AI/ML', nameJa: 'AI', category: 'technology', keywords: ['model', 'prediction', 'training', 'inference', 'dataset', 'feature', 'neural'], relatedDomains: ['analytics'] },
  { id: 'analytics', name: 'Analytics', nameJa: '分析', category: 'technology', keywords: ['report', 'dashboard', 'metric', 'kpi', 'chart', 'visualization', 'aggregation'], relatedDomains: ['ai'] },
  { id: 'telecom', name: 'Telecom', nameJa: '通信', category: 'technology', keywords: ['call', 'sms', 'voip', 'subscriber', 'network', 'bandwidth', 'carrier'], relatedDomains: ['notification'] },
  
  // サービス系 - 予約・宿泊
  { id: 'booking', name: 'Booking', nameJa: '予約', category: 'service', keywords: ['reservation', 'appointment', 'schedule', 'slot', 'availability', 'booking', 'calendar'], relatedDomains: ['calendar', 'notification'] },
  { id: 'hotel', name: 'Hotel', nameJa: 'ホテル', category: 'service', keywords: ['room', 'checkin', 'checkout', 'guest', 'housekeeping', 'amenity'], relatedDomains: ['booking', 'payment'] },
  { id: 'travel', name: 'Travel', nameJa: '旅行', category: 'service', keywords: ['trip', 'itinerary', 'destination', 'flight', 'tour', 'package'], relatedDomains: ['booking', 'payment'] },
  
  // サービス系 - 飲食・小売
  { id: 'restaurant', name: 'Restaurant', nameJa: '飲食店', category: 'service', keywords: ['menu', 'table', 'order', 'kitchen', 'dish', 'meal', 'chef'], relatedDomains: ['booking', 'payment', 'inventory'] },
  { id: 'catering', name: 'Catering', nameJa: 'ケータリング', category: 'service', keywords: ['event', 'menu', 'portion', 'delivery', 'banquet'], relatedDomains: ['restaurant', 'booking'] },
  
  // サービス系 - 施設管理
  { id: 'parking', name: 'Parking', nameJa: '駐車場', category: 'service', keywords: ['space', 'entry', 'exit', 'fee', 'plate', 'vehicle', 'lot', 'garage', 'barrier'], relatedDomains: ['payment', 'iot'] },
  { id: 'gym', name: 'Gym', nameJa: 'フィットネス', category: 'service', keywords: ['membership', 'workout', 'trainer', 'equipment', 'class', 'fitness'], relatedDomains: ['booking', 'subscription'] },
  { id: 'library', name: 'Library', nameJa: '図書館', category: 'service', keywords: ['book', 'borrow', 'return', 'catalog', 'member', 'fine', 'shelf'], relatedDomains: ['inventory', 'subscription'] },
  { id: 'museum', name: 'Museum', nameJa: '美術館・博物館', category: 'service', keywords: ['exhibit', 'collection', 'tour', 'artifact', 'gallery', 'visitor'], relatedDomains: ['ticketing', 'booking'] },
  
  // サービス系 - その他サービス
  { id: 'education', name: 'Education', nameJa: '教育', category: 'service', keywords: ['course', 'student', 'teacher', 'lesson', 'grade', 'exam', 'curriculum'], relatedDomains: ['calendar', 'payment'] },
  { id: 'realestate', name: 'Real Estate', nameJa: '不動産', category: 'service', keywords: ['property', 'listing', 'tenant', 'lease', 'rent', 'mortgage'], relatedDomains: ['booking', 'payment'] },
  { id: 'insurance', name: 'Insurance', nameJa: '保険', category: 'service', keywords: ['policy', 'claim', 'premium', 'coverage', 'beneficiary', 'underwriting'], relatedDomains: ['finance', 'healthcare'] },
  { id: 'rental', name: 'Rental', nameJa: 'レンタル', category: 'service', keywords: ['rent', 'return', 'item', 'duration', 'deposit', 'late'], relatedDomains: ['inventory', 'booking'] },
  { id: 'repair', name: 'Repair', nameJa: '修理', category: 'service', keywords: ['repair', 'maintenance', 'part', 'technician', 'warranty', 'diagnostic'], relatedDomains: ['booking', 'inventory'] },
  { id: 'cleaning', name: 'Cleaning', nameJa: '清掃', category: 'service', keywords: ['cleaning', 'schedule', 'staff', 'task', 'checklist', 'inspection'], relatedDomains: ['booking', 'workflow'] },
  { id: 'laundry', name: 'Laundry', nameJa: 'クリーニング', category: 'service', keywords: ['laundry', 'garment', 'pickup', 'delivery', 'stain', 'pressing'], relatedDomains: ['booking', 'delivery'] },
  { id: 'wedding', name: 'Wedding', nameJa: 'ブライダル', category: 'service', keywords: ['wedding', 'ceremony', 'venue', 'guest', 'planner', 'reception'], relatedDomains: ['booking', 'catering'] },
  { id: 'funeral', name: 'Funeral', nameJa: '葬儀', category: 'service', keywords: ['funeral', 'ceremony', 'memorial', 'arrangement', 'cremation'], relatedDomains: ['booking'] },
  
  // インフラ系
  { id: 'inventory', name: 'Inventory', nameJa: '在庫管理', category: 'business', keywords: ['stock', 'sku', 'warehouse', 'inventory', 'reorder', 'quantity'], relatedDomains: ['logistics', 'ecommerce'] },
  { id: 'payment', name: 'Payment', nameJa: '決済', category: 'business', keywords: ['payment', 'transaction', 'refund', 'invoice', 'billing', 'charge'], relatedDomains: ['finance', 'ecommerce'] },
  { id: 'delivery', name: 'Delivery', nameJa: '配送', category: 'service', keywords: ['delivery', 'courier', 'package', 'tracking', 'address', 'dispatch'], relatedDomains: ['logistics', 'ecommerce'] },
  { id: 'notification', name: 'Notification', nameJa: '通知', category: 'technology', keywords: ['notification', 'alert', 'push', 'email', 'sms', 'message'], relatedDomains: ['workflow'] },
  { id: 'calendar', name: 'Calendar', nameJa: 'カレンダー', category: 'technology', keywords: ['event', 'schedule', 'reminder', 'calendar', 'recurring'], relatedDomains: ['booking', 'workflow'] },
  { id: 'workflow', name: 'Workflow', nameJa: 'ワークフロー', category: 'technology', keywords: ['workflow', 'approval', 'step', 'task', 'process', 'state'], relatedDomains: ['notification'] },
  { id: 'document', name: 'Document', nameJa: '文書管理', category: 'technology', keywords: ['document', 'file', 'version', 'folder', 'upload', 'download'], relatedDomains: ['workflow'] },
  { id: 'search', name: 'Search', nameJa: '検索', category: 'technology', keywords: ['search', 'query', 'filter', 'index', 'facet', 'ranking'], relatedDomains: ['analytics'] },
  
  // エンターテイメント・メディア
  { id: 'media', name: 'Media', nameJa: 'メディア', category: 'service', keywords: ['content', 'article', 'publish', 'author', 'editor', 'cms'], relatedDomains: ['social'] },
  { id: 'gaming', name: 'Gaming', nameJa: 'ゲーム', category: 'service', keywords: ['game', 'player', 'score', 'level', 'achievement', 'leaderboard'], relatedDomains: ['social', 'subscription'] },
  { id: 'social', name: 'Social', nameJa: 'SNS', category: 'service', keywords: ['post', 'follow', 'like', 'comment', 'share', 'feed', 'profile'], relatedDomains: ['notification', 'media'] },
  { id: 'chat', name: 'Chat', nameJa: 'チャット', category: 'service', keywords: ['message', 'chat', 'conversation', 'channel', 'thread', 'emoji'], relatedDomains: ['notification', 'social'] },
  { id: 'sports', name: 'Sports', nameJa: 'スポーツ', category: 'service', keywords: ['team', 'match', 'score', 'player', 'league', 'tournament'], relatedDomains: ['booking', 'ticketing'] },
  
  // ビジネス系追加
  { id: 'auction', name: 'Auction', nameJa: 'オークション', category: 'business', keywords: ['bid', 'auction', 'lot', 'reserve', 'winning', 'hammer'], relatedDomains: ['ecommerce', 'payment'] },
  { id: 'subscription', name: 'Subscription', nameJa: 'サブスク', category: 'business', keywords: ['subscription', 'plan', 'renewal', 'cancel', 'billing', 'trial'], relatedDomains: ['payment'] },
  { id: 'marketplace', name: 'Marketplace', nameJa: 'マーケットプレイス', category: 'business', keywords: ['seller', 'buyer', 'listing', 'commission', 'marketplace'], relatedDomains: ['ecommerce', 'payment'] },
  { id: 'project', name: 'Project', nameJa: 'プロジェクト管理', category: 'business', keywords: ['project', 'task', 'milestone', 'sprint', 'backlog', 'kanban'], relatedDomains: ['workflow', 'calendar'] },
  
  // その他
  { id: 'survey', name: 'Survey', nameJa: 'アンケート', category: 'service', keywords: ['survey', 'question', 'response', 'poll', 'feedback', 'form'], relatedDomains: ['analytics'] },
  { id: 'voting', name: 'Voting', nameJa: '投票', category: 'service', keywords: ['vote', 'ballot', 'candidate', 'election', 'poll'], relatedDomains: ['survey'] },
  { id: 'ticketing', name: 'Ticketing', nameJa: 'チケット', category: 'service', keywords: ['ticket', 'seat', 'event', 'venue', 'admission'], relatedDomains: ['booking', 'payment'] },
  { id: 'waste', name: 'Waste', nameJa: '廃棄物', category: 'industry', keywords: ['waste', 'disposal', 'collection', 'bin', 'recycling'], relatedDomains: ['logistics', 'recycling'] },
  { id: 'recycling', name: 'Recycling', nameJa: 'リサイクル', category: 'industry', keywords: ['recycle', 'material', 'sorting', 'recovery', 'reuse'], relatedDomains: ['waste', 'logistics'] },
  { id: 'warehouse', name: 'Warehouse', nameJa: '倉庫', category: 'industry', keywords: ['warehouse', 'storage', 'rack', 'picking', 'packing', 'zone'], relatedDomains: ['inventory', 'logistics'] },
  { id: 'vehicle', name: 'Vehicle', nameJa: '車両管理', category: 'industry', keywords: ['vehicle', 'fleet', 'maintenance', 'fuel', 'driver', 'mileage'], relatedDomains: ['logistics', 'iot'] },
  { id: 'aviation', name: 'Aviation', nameJa: '航空', category: 'industry', keywords: ['flight', 'aircraft', 'runway', 'gate', 'boarding', 'baggage'], relatedDomains: ['travel', 'ticketing'] },
  { id: 'shipping', name: 'Shipping', nameJa: '海運', category: 'industry', keywords: ['ship', 'container', 'port', 'cargo', 'vessel', 'freight'], relatedDomains: ['logistics'] },
];

/**
 * ドメイン検出クラス
 */
export class DomainDetector {
  private domains: Domain[];

  constructor(customDomains?: Domain[]) {
    this.domains = customDomains ?? DOMAINS;
  }

  /**
   * テキストからドメインを検出
   */
  detect(text: string): DomainDetectionResult {
    const normalizedText = text.toLowerCase();
    const scores = new Map<string, { score: number; keywords: string[] }>();

    // 各ドメインのスコアを計算
    for (const domain of this.domains) {
      const matchedKeywords: string[] = [];
      let score = 0;

      for (const keyword of domain.keywords) {
        const regex = new RegExp(`\\b${keyword}\\b`, 'gi');
        const matches = normalizedText.match(regex);
        if (matches) {
          score += matches.length;
          matchedKeywords.push(keyword);
        }
      }

      if (score > 0) {
        scores.set(domain.id, { score, keywords: matchedKeywords });
      }
    }

    // スコアでソート
    const sorted = Array.from(scores.entries())
      .sort((a, b) => b[1].score - a[1].score);

    // 最高スコアのドメインを取得
    if (sorted.length === 0) {
      const generalDomain = this.domains.find(d => d.id === 'general')!;
      return {
        primaryDomain: generalDomain,
        secondaryDomains: [],
        confidence: 0.5,
        matchedKeywords: [],
        suggestedComponents: ['Service', 'Repository', 'Controller'],
      };
    }

    const [primaryId, primaryData] = sorted[0];
    const primaryDomain = this.domains.find(d => d.id === primaryId)!;

    // セカンダリドメインを取得（上位3つまで）
    const secondaryDomains = sorted
      .slice(1, 4)
      .map(([id]) => this.domains.find(d => d.id === id)!)
      .filter(Boolean);

    // 信頼度を計算（キーワードマッチ数に基づく）
    const maxPossibleScore = primaryDomain.keywords.length * 3;
    const confidence = Math.min(0.95, 0.5 + (primaryData.score / maxPossibleScore) * 0.45);

    // 推奨コンポーネントを生成
    const suggestedComponents = this.getSuggestedComponents(primaryDomain);

    return {
      primaryDomain,
      secondaryDomains,
      confidence,
      matchedKeywords: primaryData.keywords,
      suggestedComponents,
    };
  }

  /**
   * ドメインに基づく推奨コンポーネントを取得
   */
  private getSuggestedComponents(domain: Domain): string[] {
    const componentMap: Record<string, string[]> = {
      ecommerce: ['CartService', 'ProductRepository', 'OrderService', 'PaymentGateway', 'CatalogService'],
      finance: ['AccountService', 'TransactionRepository', 'BalanceCalculator', 'TransferService'],
      healthcare: ['PatientRepository', 'DiagnosisService', 'AppointmentService', 'MedicalRecordService'],
      veterinary: ['PetRepository', 'PetService', 'ReservationService', 'MedicalHistoryRepository', 'VetScheduleService'],
      parking: ['SpaceRepository', 'SpaceService', 'EntryExitService', 'FeeCalculator', 'PaymentService'],
      booking: ['ReservationRepository', 'ReservationService', 'AvailabilityChecker', 'SlotManager'],
      hotel: ['RoomRepository', 'RoomService', 'CheckInService', 'CheckOutService', 'GuestService'],
      restaurant: ['MenuRepository', 'OrderService', 'TableService', 'KitchenService', 'ReservationService'],
      inventory: ['StockRepository', 'InventoryService', 'ReorderService', 'StockAlertService'],
      payment: ['PaymentRepository', 'PaymentService', 'RefundService', 'InvoiceGenerator'],
      notification: ['NotificationRepository', 'NotificationService', 'PushService', 'EmailService'],
      workflow: ['WorkflowRepository', 'WorkflowEngine', 'ApprovalService', 'TaskService'],
      iot: ['DeviceRepository', 'DeviceService', 'TelemetryService', 'SensorDataProcessor'],
      security: ['AuthService', 'TokenService', 'PermissionService', 'RoleRepository'],
      crm: ['CustomerRepository', 'CustomerService', 'LeadService', 'OpportunityService'],
      hr: ['EmployeeRepository', 'EmployeeService', 'AttendanceService', 'PayrollService'],
      education: ['CourseRepository', 'CourseService', 'StudentService', 'GradeService', 'EnrollmentService'],
      logistics: ['ShipmentRepository', 'ShipmentService', 'TrackingService', 'RouteOptimizer'],
      general: ['Service', 'Repository', 'Controller', 'Validator'],
    };

    return componentMap[domain.id] ?? componentMap.general;
  }

  /**
   * ドメイン一覧を取得
   */
  getAllDomains(): Domain[] {
    return [...this.domains];
  }

  /**
   * カテゴリでフィルタ
   */
  getDomainsByCategory(category: DomainCategory): Domain[] {
    return this.domains.filter(d => d.category === category);
  }

  /**
   * IDでドメインを取得
   */
  getDomainById(id: string): Domain | undefined {
    return this.domains.find(d => d.id === id);
  }

  /**
   * ドメイン数を取得
   */
  getDomainCount(): number {
    return this.domains.length;
  }
}

// シングルトンインスタンス
export const domainDetector = new DomainDetector();
