/**
 * C4 Model Generator
 *
 * Generates C4 architecture models from requirements content
 * with domain-specific component inference and traceability mapping
 *
 * @packageDocumentation
 * @module cli/commands/design/c4-generator
 */

import type { C4Level, C4Model, C4Element, C4Relationship } from './types.js';
import { detectDomainFromContent, hasKeywordMatch } from './patterns.js';

/**
 * Component inference definition
 */
interface ComponentInference {
  keywords: string[];
  name: string;
  desc: string;
  domain: string;
}

/**
 * Domain-specific component inferences for EARS requirements
 */
const COMPONENT_INFERENCES: ComponentInference[] = [
  // ========================================
  // General/Cross-domain components (always available)
  // ========================================
  { keywords: ['task', 'タスク'], name: 'TaskService', desc: 'Manages task lifecycle and operations', domain: 'general' },
  { keywords: ['notification', 'notify', 'alert', '通知', 'アラート'], name: 'NotificationService', desc: 'Handles user notifications and alerts', domain: 'general' },
  { keywords: ['persist', 'store', 'save', 'storage', '保存', '永続'], name: 'DataRepository', desc: 'Handles data persistence and storage', domain: 'general' },
  { keywords: ['authenticate', 'auth', 'login', '認証', 'ログイン'], name: 'AuthService', desc: 'Manages authentication and authorization', domain: 'general' },
  { keywords: ['priority', '優先', '優先度'], name: 'PriorityManager', desc: 'Manages item prioritization', domain: 'general' },
  { keywords: ['deadline', 'schedule', '期限', 'スケジュール', '予定'], name: 'ScheduleService', desc: 'Manages scheduling and deadlines', domain: 'general' },
  { keywords: ['archive', 'アーカイブ'], name: 'ArchiveService', desc: 'Handles completed item archiving', domain: 'general' },
  { keywords: ['validation', 'validate', 'confirm', '確認', '検証'], name: 'ValidationService', desc: 'Validates user input and actions', domain: 'general' },
  { keywords: ['report', 'レポート', '報告', 'statistics', '統計'], name: 'ReportService', desc: 'Generates reports and statistics', domain: 'general' },
  { keywords: ['search', '検索', 'find', 'query'], name: 'SearchService', desc: 'Handles search and query operations', domain: 'general' },
  { keywords: ['cart', 'カート'], name: 'CartService', desc: 'Manages shopping cart operations', domain: 'ecommerce' },
  { keywords: ['product', 'catalog', '商品', 'カタログ'], name: 'ProductCatalogService', desc: 'Manages product catalog and display', domain: 'ecommerce' },
  { keywords: ['checkout', '購入', '決済'], name: 'CheckoutService', desc: 'Handles checkout and order processing', domain: 'ecommerce' },
  { keywords: ['price', 'total', 'tax', '価格', '計算', 'pricing'], name: 'PricingService', desc: 'Calculates prices, taxes, and totals', domain: 'ecommerce' },
  { keywords: ['stock', 'inventory', '在庫'], name: 'InventoryService', desc: 'Manages product inventory and stock levels', domain: 'general' },
  { keywords: ['coupon', 'discount', '割引', 'クーポン'], name: 'DiscountService', desc: 'Handles coupons and discount codes', domain: 'ecommerce' },
  { keywords: ['order', '注文', 'purchase'], name: 'OrderService', desc: 'Manages customer orders', domain: 'ecommerce' },
  { keywords: ['payment', '支払', 'pay', '決済'], name: 'PaymentService', desc: 'Processes payments', domain: 'general' },

  // ========================================
  // Agriculture domain components
  // ========================================
  { keywords: ['crop', '作物', 'plant', '植物', '栽培'], name: 'CropService', desc: 'Manages crop registration and lifecycle', domain: 'agriculture' },
  { keywords: ['harvest', '収穫', 'yield', '収量'], name: 'HarvestService', desc: 'Tracks harvest data and yield predictions', domain: 'agriculture' },
  { keywords: ['weather', '天気', '気象', 'climate'], name: 'WeatherService', desc: 'Monitors weather conditions and alerts', domain: 'agriculture' },
  { keywords: ['growth', '成長', '生育', 'development'], name: 'GrowthTrackingService', desc: 'Tracks plant growth and development stages', domain: 'agriculture' },
  { keywords: ['equipment', '機器', '農機', 'machinery'], name: 'EquipmentService', desc: 'Manages farm equipment and machinery', domain: 'agriculture' },
  { keywords: ['soil', '土壌', 'field', '圃場'], name: 'FieldManagementService', desc: 'Manages field and soil data', domain: 'agriculture' },
  { keywords: ['irrigation', '灌漑', 'water', '水やり'], name: 'IrrigationService', desc: 'Manages irrigation and watering schedules', domain: 'agriculture' },

  // ========================================
  // Library/Book management components
  // ========================================
  { keywords: ['book', '図書', '本', '書籍'], name: 'BookService', desc: 'Manages book catalog and metadata', domain: 'library' },
  { keywords: ['loan', '貸出', 'borrow', '借りる'], name: 'LoanService', desc: 'Handles book lending and returns', domain: 'library' },
  { keywords: ['member', '会員', 'patron', '利用者'], name: 'MemberService', desc: 'Manages library members and accounts', domain: 'library' },
  { keywords: ['reservation', '予約', 'reserve', 'hold'], name: 'ReservationService', desc: 'Handles reservations and holds', domain: 'general' },
  { keywords: ['catalog', 'カタログ', '目録'], name: 'CatalogService', desc: 'Manages library catalog and collections', domain: 'library' },
  { keywords: ['fine', '延滞料', 'penalty', 'overdue'], name: 'FineService', desc: 'Calculates and tracks late fees', domain: 'library' },

  // ========================================
  // Fitness/Health components
  // ========================================
  { keywords: ['workout', 'exercise', '運動', 'トレーニング', 'ワークアウト'], name: 'WorkoutService', desc: 'Manages workout sessions and exercises', domain: 'fitness' },
  { keywords: ['progress', '進捗', 'achievement', '達成'], name: 'ProgressTrackingService', desc: 'Tracks fitness progress and achievements', domain: 'fitness' },
  { keywords: ['trainer', 'トレーナー', 'coach', 'コーチ'], name: 'TrainerService', desc: 'Manages trainers and coaching sessions', domain: 'fitness' },
  { keywords: ['nutrition', '栄養', 'diet', '食事'], name: 'NutritionService', desc: 'Tracks nutrition and dietary plans', domain: 'fitness' },
  { keywords: ['goal', '目標', 'target'], name: 'GoalService', desc: 'Manages fitness goals and targets', domain: 'fitness' },
  { keywords: ['membership', 'メンバーシップ', 'subscription'], name: 'MembershipService', desc: 'Handles gym memberships and subscriptions', domain: 'fitness' },

  // ========================================
  // Pet care components
  // ========================================
  { keywords: ['pet', 'ペット', '動物'], name: 'PetService', desc: 'Manages pet profiles and information', domain: 'petcare' },
  { keywords: ['veterinary', 'vet', '獣医', '動物病院'], name: 'VeterinaryService', desc: 'Manages veterinary appointments and records', domain: 'petcare' },
  { keywords: ['grooming', 'グルーミング', 'トリミング'], name: 'GroomingService', desc: 'Schedules and tracks grooming services', domain: 'petcare' },
  { keywords: ['vaccination', 'ワクチン', '予防接種'], name: 'VaccinationService', desc: 'Tracks vaccination schedules and records', domain: 'petcare' },
  { keywords: ['feeding', '給餌', 'food', 'フード'], name: 'FeedingService', desc: 'Manages feeding schedules and nutrition', domain: 'petcare' },
  { keywords: ['adoption', '譲渡', '里親'], name: 'AdoptionService', desc: 'Handles pet adoption processes', domain: 'petcare' },

  // ========================================
  // Music/Streaming components
  // ========================================
  { keywords: ['track', 'song', '曲', '楽曲'], name: 'TrackService', desc: 'Manages music tracks and metadata', domain: 'music' },
  { keywords: ['playlist', 'プレイリスト'], name: 'PlaylistService', desc: 'Manages user playlists and collections', domain: 'music' },
  { keywords: ['streaming', 'ストリーミング', 'play', '再生'], name: 'StreamingService', desc: 'Handles audio streaming and playback', domain: 'music' },
  { keywords: ['artist', 'アーティスト', 'musician'], name: 'ArtistService', desc: 'Manages artist profiles and discographies', domain: 'music' },
  { keywords: ['album', 'アルバム'], name: 'AlbumService', desc: 'Manages album metadata and track lists', domain: 'music' },
  { keywords: ['recommendation', 'おすすめ', 'suggest'], name: 'RecommendationService', desc: 'Provides personalized recommendations', domain: 'music' },

  // ========================================
  // Vehicle/Maintenance components
  // ========================================
  { keywords: ['vehicle', '車両', '車', 'car'], name: 'VehicleService', desc: 'Manages vehicle registration and profiles', domain: 'vehicle' },
  { keywords: ['maintenance', 'メンテナンス', '整備'], name: 'MaintenanceService', desc: 'Tracks maintenance schedules and history', domain: 'vehicle' },
  { keywords: ['parts', '部品', 'パーツ'], name: 'PartsService', desc: 'Manages spare parts inventory and orders', domain: 'vehicle' },
  { keywords: ['mileage', '走行距離', 'odometer'], name: 'MileageTrackingService', desc: 'Tracks vehicle mileage and usage', domain: 'vehicle' },
  { keywords: ['repair', '修理', 'fix'], name: 'RepairService', desc: 'Manages repair requests and work orders', domain: 'vehicle' },
  { keywords: ['inspection', '点検', '検査'], name: 'InspectionService', desc: 'Schedules and records vehicle inspections', domain: 'vehicle' },

  // ========================================
  // Event management components
  // ========================================
  { keywords: ['event', 'イベント', '催し'], name: 'EventService', desc: 'Manages events and event details', domain: 'event' },
  { keywords: ['venue', '会場'], name: 'VenueService', desc: 'Manages venues and location bookings', domain: 'event' },
  { keywords: ['ticket', 'チケット', '入場券'], name: 'TicketService', desc: 'Handles ticket sales and management', domain: 'event' },
  { keywords: ['registration', '登録', 'signup', 'rsvp'], name: 'RegistrationService', desc: 'Manages event registrations and RSVPs', domain: 'event' },
  { keywords: ['attendee', '参加者', 'participant'], name: 'AttendeeService', desc: 'Manages attendee information and check-ins', domain: 'event' },
  { keywords: ['speaker', 'スピーカー', '登壇者'], name: 'SpeakerService', desc: 'Manages speakers and presentation schedules', domain: 'event' },

  // ========================================
  // Insurance components
  // ========================================
  { keywords: ['claim', '請求', '保険金請求'], name: 'ClaimService', desc: 'Processes and tracks insurance claims', domain: 'insurance' },
  { keywords: ['policy', '契約', 'ポリシー', '保険'], name: 'PolicyService', desc: 'Manages insurance policies and coverage', domain: 'insurance' },
  { keywords: ['assessment', '査定', '審査', 'evaluation'], name: 'AssessmentService', desc: 'Handles claim assessments and evaluations', domain: 'insurance' },
  { keywords: ['premium', '保険料', 'プレミアム'], name: 'PremiumService', desc: 'Calculates and manages premium payments', domain: 'insurance' },
  { keywords: ['underwriting', '引受'], name: 'UnderwritingService', desc: 'Handles risk assessment and policy approval', domain: 'insurance' },
  { keywords: ['document', '書類', 'ドキュメント'], name: 'DocumentService', desc: 'Manages insurance documents and attachments', domain: 'insurance' },

  // ========================================
  // Recruitment/HR components
  // ========================================
  { keywords: ['candidate', '候補者', 'applicant', '応募者'], name: 'CandidateService', desc: 'Manages candidate profiles and applications', domain: 'recruitment' },
  { keywords: ['job', '求人', 'position', 'ポジション'], name: 'JobService', desc: 'Manages job postings and requirements', domain: 'recruitment' },
  { keywords: ['interview', '面接'], name: 'InterviewService', desc: 'Schedules and tracks interviews', domain: 'recruitment' },
  { keywords: ['resume', '履歴書', 'cv'], name: 'ResumeService', desc: 'Parses and stores resume data', domain: 'recruitment' },
  { keywords: ['offer', 'オファー', '内定'], name: 'OfferService', desc: 'Manages job offers and negotiations', domain: 'recruitment' },
  { keywords: ['onboarding', 'オンボーディング', '入社'], name: 'OnboardingService', desc: 'Handles new hire onboarding processes', domain: 'recruitment' },

  // ========================================
  // Warehouse/Logistics components
  // ========================================
  { keywords: ['warehouse', '倉庫'], name: 'WarehouseService', desc: 'Manages warehouse locations and zones', domain: 'warehouse' },
  { keywords: ['shipment', '出荷', 'shipping', '配送'], name: 'ShipmentService', desc: 'Handles shipment scheduling and tracking', domain: 'warehouse' },
  { keywords: ['picking', 'ピッキング'], name: 'PickingService', desc: 'Manages order picking and fulfillment', domain: 'warehouse' },
  { keywords: ['receiving', '入荷', 'receipt', '受入'], name: 'ReceivingService', desc: 'Handles incoming goods and inventory receipt', domain: 'warehouse' },
  { keywords: ['location', 'ロケーション', 'bin', '棚'], name: 'LocationService', desc: 'Manages storage locations and bin assignments', domain: 'warehouse' },
  { keywords: ['packing', '梱包', 'package'], name: 'PackingService', desc: 'Handles order packing and packaging', domain: 'warehouse' },

  // ========================================
  // Healthcare/Medical components
  // ========================================
  { keywords: ['patient', '患者', 'medical record'], name: 'PatientService', desc: 'Manages patient records and profiles', domain: 'healthcare' },
  { keywords: ['appointment', '予約', 'booking'], name: 'AppointmentService', desc: 'Schedules and manages medical appointments', domain: 'healthcare' },
  { keywords: ['prescription', '処方', 'medication'], name: 'PrescriptionService', desc: 'Manages prescriptions and medications', domain: 'healthcare' },
  { keywords: ['doctor', '医師', 'physician'], name: 'DoctorService', desc: 'Manages doctor profiles and availability', domain: 'healthcare' },
  { keywords: ['diagnosis', '診断', 'treatment'], name: 'DiagnosisService', desc: 'Records diagnoses and treatment plans', domain: 'healthcare' },
  { keywords: ['lab', '検査', 'test result'], name: 'LabService', desc: 'Manages lab tests and results', domain: 'healthcare' },
  { keywords: ['telemedicine', '遠隔医療', 'telehealth'], name: 'TelemedicineService', desc: 'Handles remote consultations', domain: 'healthcare' },

  // ========================================
  // Education/Learning components
  // ========================================
  { keywords: ['student', '学生', 'learner'], name: 'StudentService', desc: 'Manages student profiles and enrollment', domain: 'education' },
  { keywords: ['course', '講座', 'class', 'コース'], name: 'CourseService', desc: 'Manages courses and curricula', domain: 'education' },
  { keywords: ['grade', '成績', 'score'], name: 'GradeService', desc: 'Tracks student grades and assessments', domain: 'education' },
  { keywords: ['enrollment', '入学', 'registration'], name: 'EnrollmentService', desc: 'Handles student enrollment processes', domain: 'education' },
  { keywords: ['assignment', '課題', 'homework'], name: 'AssignmentService', desc: 'Manages assignments and submissions', domain: 'education' },
  { keywords: ['teacher', '教師', 'instructor'], name: 'TeacherService', desc: 'Manages teacher profiles and assignments', domain: 'education' },
  { keywords: ['attendance', '出席', 'presence'], name: 'AttendanceService', desc: 'Tracks student attendance', domain: 'education' },
  { keywords: ['certificate', '証明書', 'diploma'], name: 'CertificateService', desc: 'Issues certificates and diplomas', domain: 'education' },

  // ========================================
  // Restaurant/Food service components
  // ========================================
  { keywords: ['menu', 'メニュー', 'dish'], name: 'MenuService', desc: 'Manages menu items and pricing', domain: 'restaurant' },
  { keywords: ['table', 'テーブル', 'seating'], name: 'TableService', desc: 'Manages table reservations and seating', domain: 'restaurant' },
  { keywords: ['order', '注文', 'food order'], name: 'FoodOrderService', desc: 'Handles food orders and modifications', domain: 'restaurant' },
  { keywords: ['kitchen', '厨房', 'cook'], name: 'KitchenService', desc: 'Manages kitchen operations and display', domain: 'restaurant' },
  { keywords: ['recipe', 'レシピ', 'ingredient'], name: 'RecipeService', desc: 'Manages recipes and ingredients', domain: 'restaurant' },
  { keywords: ['delivery', 'デリバリー', 'takeout'], name: 'DeliveryService', desc: 'Handles delivery and takeout orders', domain: 'restaurant' },

  // ========================================
  // Hotel/Hospitality components
  // ========================================
  { keywords: ['room', '客室', 'suite'], name: 'RoomService', desc: 'Manages room inventory and status', domain: 'hotel' },
  { keywords: ['guest', 'ゲスト', 'visitor'], name: 'GuestService', desc: 'Manages guest profiles and preferences', domain: 'hotel' },
  { keywords: ['check-in', 'チェックイン', 'arrival'], name: 'CheckInService', desc: 'Handles guest check-in processes', domain: 'hotel' },
  { keywords: ['checkout', 'チェックアウト', 'departure'], name: 'CheckoutService', desc: 'Handles guest checkout and billing', domain: 'hotel' },
  { keywords: ['housekeeping', 'ハウスキーピング', 'cleaning'], name: 'HousekeepingService', desc: 'Manages room cleaning schedules', domain: 'hotel' },
  { keywords: ['amenity', 'アメニティ', 'facility'], name: 'AmenityService', desc: 'Manages hotel amenities and services', domain: 'hotel' },
  { keywords: ['concierge', 'コンシェルジュ'], name: 'ConciergeService', desc: 'Handles guest requests and recommendations', domain: 'hotel' },

  // ========================================
  // Banking/Finance components
  // ========================================
  { keywords: ['account', '口座', 'banking'], name: 'AccountService', desc: 'Manages bank accounts and balances', domain: 'banking' },
  { keywords: ['transaction', '取引', 'transfer'], name: 'TransactionService', desc: 'Processes financial transactions', domain: 'banking' },
  { keywords: ['loan', 'ローン', 'lending'], name: 'LoanService', desc: 'Manages loan applications and terms', domain: 'banking' },
  { keywords: ['deposit', '預金', 'savings'], name: 'DepositService', desc: 'Handles deposits and savings accounts', domain: 'banking' },
  { keywords: ['credit', 'クレジット', 'credit score'], name: 'CreditService', desc: 'Evaluates creditworthiness and scores', domain: 'banking' },
  { keywords: ['interest', '利息', 'rate'], name: 'InterestService', desc: 'Calculates interest rates and earnings', domain: 'banking' },
  { keywords: ['ATM', 'atm', '現金'], name: 'ATMService', desc: 'Manages ATM locations and transactions', domain: 'banking' },

  // ========================================
  // Real Estate components
  // ========================================
  { keywords: ['property', '物件', 'real estate'], name: 'PropertyService', desc: 'Manages property listings and details', domain: 'realestate' },
  { keywords: ['tenant', '入居者', 'renter'], name: 'TenantService', desc: 'Manages tenant profiles and agreements', domain: 'realestate' },
  { keywords: ['lease', '賃貸', 'rental'], name: 'LeaseService', desc: 'Handles lease agreements and terms', domain: 'realestate' },
  { keywords: ['listing', 'リスティング', 'posting'], name: 'ListingService', desc: 'Manages property listings and visibility', domain: 'realestate' },
  { keywords: ['showing', '内見', 'viewing'], name: 'ShowingService', desc: 'Schedules property showings', domain: 'realestate' },
  { keywords: ['mortgage', '住宅ローン', 'financing'], name: 'MortgageService', desc: 'Calculates mortgages and financing options', domain: 'realestate' },
  { keywords: ['landlord', '大家', 'owner'], name: 'LandlordService', desc: 'Manages landlord profiles and properties', domain: 'realestate' },

  // ========================================
  // Travel/Tourism components
  // ========================================
  { keywords: ['flight', 'フライト', 'airline'], name: 'FlightService', desc: 'Manages flight bookings and schedules', domain: 'travel' },
  { keywords: ['itinerary', '旅程', 'trip'], name: 'ItineraryService', desc: 'Creates and manages travel itineraries', domain: 'travel' },
  { keywords: ['visa', 'ビザ', 'passport'], name: 'VisaService', desc: 'Handles visa applications and documents', domain: 'travel' },
  { keywords: ['tour', 'ツアー', 'excursion'], name: 'TourService', desc: 'Manages tour packages and bookings', domain: 'travel' },
  { keywords: ['currency', '通貨', 'exchange'], name: 'CurrencyService', desc: 'Handles currency exchange rates', domain: 'travel' },
  { keywords: ['luggage', '荷物', 'baggage'], name: 'LuggageService', desc: 'Tracks luggage and baggage', domain: 'travel' },
  { keywords: ['destination', '目的地', 'location'], name: 'DestinationService', desc: 'Provides destination information', domain: 'travel' },

  // ========================================
  // Manufacturing/Production components
  // ========================================
  { keywords: ['production', '生産', 'manufacturing'], name: 'ProductionService', desc: 'Manages production schedules and output', domain: 'manufacturing' },
  { keywords: ['quality', '品質', 'QC'], name: 'QualityService', desc: 'Handles quality control and inspections', domain: 'manufacturing' },
  { keywords: ['assembly', '組立', 'line'], name: 'AssemblyService', desc: 'Manages assembly line operations', domain: 'manufacturing' },
  { keywords: ['defect', '不良', 'deficiency'], name: 'DefectService', desc: 'Tracks defects and quality issues', domain: 'manufacturing' },
  { keywords: ['material', '資材', 'raw material'], name: 'MaterialService', desc: 'Manages raw materials and supplies', domain: 'manufacturing' },
  { keywords: ['machine', '機械', 'equipment'], name: 'MachineService', desc: 'Tracks machine status and maintenance', domain: 'manufacturing' },
  { keywords: ['shift', 'シフト', 'schedule'], name: 'ShiftService', desc: 'Manages worker shifts and schedules', domain: 'manufacturing' },
  { keywords: ['work order', '作業指示', 'instruction'], name: 'WorkOrderService', desc: 'Creates and tracks work orders', domain: 'manufacturing' },

  // ========================================
  // Logistics/Transportation components
  // ========================================
  { keywords: ['delivery', '配送', 'transport'], name: 'LogisticsDeliveryService', desc: 'Manages delivery schedules and routes', domain: 'logistics' },
  { keywords: ['route', 'ルート', 'path'], name: 'RouteService', desc: 'Optimizes delivery routes', domain: 'logistics' },
  { keywords: ['driver', 'ドライバー', 'carrier'], name: 'DriverService', desc: 'Manages driver profiles and assignments', domain: 'logistics' },
  { keywords: ['freight', '貨物', 'cargo'], name: 'FreightService', desc: 'Handles freight bookings and tracking', domain: 'logistics' },
  { keywords: ['container', 'コンテナ'], name: 'ContainerService', desc: 'Tracks container status and location', domain: 'logistics' },
  { keywords: ['customs', '税関', 'clearance'], name: 'CustomsService', desc: 'Handles customs documentation', domain: 'logistics' },
  { keywords: ['dispatch', '配車', 'assignment'], name: 'DispatchService', desc: 'Manages vehicle dispatch operations', domain: 'logistics' },
  { keywords: ['tracking', '追跡', 'trace'], name: 'TrackingService', desc: 'Provides real-time shipment tracking', domain: 'logistics' },

  // ========================================
  // Game/Entertainment components
  // ========================================
  { keywords: ['player', 'プレイヤー', 'gamer'], name: 'PlayerService', desc: 'Manages player profiles and stats', domain: 'game' },
  { keywords: ['matching', 'マッチング', 'matchmake'], name: 'MatchingService', desc: 'Handles player matchmaking', domain: 'game' },
  { keywords: ['ranking', 'ランキング', 'leaderboard'], name: 'RankingService', desc: 'Manages rankings and leaderboards', domain: 'game' },
  { keywords: ['item', 'アイテム', 'inventory'], name: 'ItemService', desc: 'Manages in-game items and inventory', domain: 'game' },
  { keywords: ['gacha', 'ガチャ', 'loot box'], name: 'GachaService', desc: 'Handles gacha/lottery mechanics', domain: 'game' },
  { keywords: ['guild', 'ギルド', 'clan'], name: 'GuildService', desc: 'Manages guilds and teams', domain: 'game' },
  { keywords: ['quest', 'クエスト', 'mission'], name: 'QuestService', desc: 'Manages quests and missions', domain: 'game' },

  // ========================================
  // Sports/Gym components
  // ========================================
  { keywords: ['member', '会員', 'membership'], name: 'MemberService', desc: 'Manages gym memberships', domain: 'sports' },
  { keywords: ['instructor', 'インストラクター', 'trainer'], name: 'InstructorService', desc: 'Manages trainers and instructors', domain: 'sports' },
  { keywords: ['lesson', 'レッスン', 'class'], name: 'LessonService', desc: 'Schedules fitness classes', domain: 'sports' },
  { keywords: ['equipment', '器具', 'machine'], name: 'EquipmentService', desc: 'Manages gym equipment', domain: 'sports' },
  { keywords: ['schedule', 'スケジュール', 'timetable'], name: 'SportsScheduleService', desc: 'Manages sports schedules', domain: 'sports' },
  { keywords: ['facility', '施設', 'court'], name: 'SportsFacilityService', desc: 'Manages sports facilities', domain: 'sports' },
  { keywords: ['booking', '予約', 'reservation'], name: 'SportsBookingService', desc: 'Handles facility bookings', domain: 'sports' },

  // ========================================
  // Media/Publishing components
  // ========================================
  { keywords: ['article', '記事', 'content'], name: 'ArticleService', desc: 'Manages articles and content', domain: 'media' },
  { keywords: ['editor', '編集', 'editing'], name: 'EditorService', desc: 'Handles content editing workflow', domain: 'media' },
  { keywords: ['writer', 'ライター', 'author'], name: 'WriterService', desc: 'Manages writers and contributors', domain: 'media' },
  { keywords: ['subscription', '購読', 'subscribe'], name: 'SubscriptionService', desc: 'Manages subscriptions', domain: 'media' },
  { keywords: ['advertisement', '広告', 'ad'], name: 'AdService', desc: 'Manages advertising placements', domain: 'media' },

  // ========================================
  // Legal components
  // ========================================
  { keywords: ['case', '案件', 'matter'], name: 'CaseService', desc: 'Manages legal cases and matters', domain: 'legal' },
  { keywords: ['lawsuit', '訴訟', 'litigation'], name: 'LitigationService', desc: 'Tracks litigation proceedings', domain: 'legal' },
  { keywords: ['contract', '契約書', 'agreement'], name: 'ContractService', desc: 'Manages legal contracts', domain: 'legal' },
  { keywords: ['lawyer', '弁護士', 'attorney'], name: 'LawyerService', desc: 'Manages lawyer assignments', domain: 'legal' },
  { keywords: ['billing', '請求', 'fee'], name: 'LegalBillingService', desc: 'Handles legal billing', domain: 'legal' },

  // ========================================
  // Accounting components
  // ========================================
  { keywords: ['journal', '仕訳', 'entry'], name: 'JournalService', desc: 'Manages journal entries', domain: 'accounting' },
  { keywords: ['ledger', '勘定', 'account'], name: 'LedgerService', desc: 'Manages general ledger', domain: 'accounting' },
  { keywords: ['tax', '税務', 'taxation'], name: 'TaxService', desc: 'Handles tax calculations', domain: 'accounting' },
  { keywords: ['expense', '経費', 'reimbursement'], name: 'ExpenseService', desc: 'Manages expense reports', domain: 'accounting' },
  { keywords: ['invoice', '請求書', 'bill'], name: 'InvoiceService', desc: 'Generates and tracks invoices', domain: 'accounting' },
  { keywords: ['budget', '予算', 'fiscal'], name: 'BudgetService', desc: 'Manages budgets and forecasts', domain: 'accounting' },

  // ========================================
  // HR components
  // ========================================
  { keywords: ['employee', '従業員', 'staff'], name: 'EmployeeService', desc: 'Manages employee records', domain: 'hr' },
  { keywords: ['payroll', '給与', 'salary'], name: 'PayrollService', desc: 'Processes payroll', domain: 'hr' },
  { keywords: ['attendance', '勤怠', 'timekeeping'], name: 'AttendanceService', desc: 'Tracks attendance', domain: 'hr' },
  { keywords: ['evaluation', '評価', 'performance'], name: 'EvaluationService', desc: 'Manages performance reviews', domain: 'hr' },
  { keywords: ['training', '研修', 'onboarding'], name: 'TrainingService', desc: 'Manages training programs', domain: 'hr' },
  { keywords: ['leave', '休暇', 'vacation'], name: 'LeaveService', desc: 'Manages leave requests', domain: 'hr' },

  // ========================================
  // CRM/Sales components
  // ========================================
  { keywords: ['lead', 'リード', 'prospect'], name: 'LeadService', desc: 'Manages sales leads', domain: 'crm' },
  { keywords: ['opportunity', '商談', 'deal'], name: 'OpportunityService', desc: 'Tracks sales opportunities', domain: 'crm' },
  { keywords: ['quote', '見積', 'estimate'], name: 'QuoteService', desc: 'Generates sales quotes', domain: 'crm' },
  { keywords: ['pipeline', 'パイプライン', 'funnel'], name: 'PipelineService', desc: 'Manages sales pipeline', domain: 'crm' },
  { keywords: ['followup', 'フォローアップ', 'contact'], name: 'FollowupService', desc: 'Manages customer followups', domain: 'crm' },

  // ========================================
  // Marketing components
  // ========================================
  { keywords: ['campaign', 'キャンペーン', 'promotion'], name: 'CampaignService', desc: 'Manages marketing campaigns', domain: 'marketing' },
  { keywords: ['segment', 'セグメント', 'audience'], name: 'SegmentService', desc: 'Manages audience segments', domain: 'marketing' },
  { keywords: ['conversion', 'コンバージョン', 'goal'], name: 'ConversionService', desc: 'Tracks conversion metrics', domain: 'marketing' },
  { keywords: ['analytics', '分析', 'metrics'], name: 'AnalyticsService', desc: 'Provides marketing analytics', domain: 'marketing' },
  { keywords: ['email', 'メール', 'newsletter'], name: 'EmailMarketingService', desc: 'Manages email campaigns', domain: 'marketing' },
  { keywords: ['content', 'コンテンツ', 'material'], name: 'MarketingContentService', desc: 'Manages marketing content', domain: 'marketing' },
  { keywords: ['lead', 'リード', 'acquisition'], name: 'LeadAcquisitionService', desc: 'Handles lead acquisition', domain: 'marketing' },

  // ========================================
  // Social Media components
  // ========================================
  { keywords: ['post', '投稿', 'content'], name: 'PostService', desc: 'Manages social posts', domain: 'social' },
  { keywords: ['follow', 'フォロー', 'follower'], name: 'FollowService', desc: 'Manages follow relationships', domain: 'social' },
  { keywords: ['like', 'いいね', 'reaction'], name: 'LikeService', desc: 'Handles likes and reactions', domain: 'social' },
  { keywords: ['comment', 'コメント', 'reply'], name: 'CommentService', desc: 'Manages comments', domain: 'social' },
  { keywords: ['timeline', 'タイムライン', 'feed'], name: 'TimelineService', desc: 'Generates user timelines', domain: 'social' },

  // ========================================
  // IoT components
  // ========================================
  { keywords: ['sensor', 'センサー', 'detector'], name: 'SensorService', desc: 'Manages sensor data', domain: 'iot' },
  { keywords: ['device', 'デバイス', 'node'], name: 'DeviceService', desc: 'Manages IoT devices', domain: 'iot' },
  { keywords: ['monitor', '監視', 'watch'], name: 'MonitorService', desc: 'Monitors device status', domain: 'iot' },
  { keywords: ['alert', 'アラート', 'alarm'], name: 'AlertService', desc: 'Handles alerts and notifications', domain: 'iot' },
  { keywords: ['automation', '自動化', 'rule'], name: 'AutomationService', desc: 'Manages automation rules', domain: 'iot' },

  // ========================================
  // Energy components
  // ========================================
  { keywords: ['consumption', '消費', 'usage'], name: 'ConsumptionService', desc: 'Tracks energy consumption', domain: 'energy' },
  { keywords: ['generation', '発電', 'produce'], name: 'GenerationService', desc: 'Manages power generation', domain: 'energy' },
  { keywords: ['grid', 'グリッド', 'network'], name: 'GridService', desc: 'Manages power grid', domain: 'energy' },
  { keywords: ['battery', '蓄電', 'storage'], name: 'BatteryService', desc: 'Manages energy storage', domain: 'energy' },
  { keywords: ['meter', 'メーター', 'reading'], name: 'MeterService', desc: 'Handles meter readings', domain: 'energy' },

  // ========================================
  // Construction components
  // ========================================
  { keywords: ['project', 'プロジェクト', '工事'], name: 'ConstructionProjectService', desc: 'Manages construction projects', domain: 'construction' },
  { keywords: ['site', '現場', 'location'], name: 'SiteService', desc: 'Manages construction sites', domain: 'construction' },
  { keywords: ['contractor', '施工', 'builder'], name: 'ContractorService', desc: 'Manages contractors', domain: 'construction' },
  { keywords: ['safety', '安全', 'incident'], name: 'SafetyService', desc: 'Manages safety compliance', domain: 'construction' },
  { keywords: ['material', '資材', 'supply'], name: 'ConstructionMaterialService', desc: 'Manages construction materials', domain: 'construction' },

  // ========================================
  // Aviation components
  // ========================================
  { keywords: ['boarding', '搭乗', 'gate'], name: 'BoardingService', desc: 'Manages boarding process', domain: 'aviation' },
  { keywords: ['baggage', '手荷物', 'luggage'], name: 'BaggageService', desc: 'Handles baggage tracking', domain: 'aviation' },
  { keywords: ['seat', '座席', 'allocation'], name: 'SeatService', desc: 'Manages seat assignments', domain: 'aviation' },
  { keywords: ['airport', '空港', 'terminal'], name: 'AirportService', desc: 'Manages airport operations', domain: 'aviation' },
  { keywords: ['crew', '乗務員', 'staff'], name: 'CrewService', desc: 'Manages flight crew', domain: 'aviation' },
  { keywords: ['flight', 'フライト', 'aircraft'], name: 'AviationFlightService', desc: 'Manages flight operations', domain: 'aviation' },
  { keywords: ['maintenance', '整備', 'inspection'], name: 'AircraftMaintenanceService', desc: 'Manages aircraft maintenance', domain: 'aviation' },

  // ========================================
  // Shipping components
  // ========================================
  { keywords: ['vessel', '船舶', 'ship'], name: 'VesselService', desc: 'Manages ship fleet', domain: 'shipping' },
  { keywords: ['port', '港', 'harbor'], name: 'PortService', desc: 'Manages port operations', domain: 'shipping' },
  { keywords: ['cargo', '貨物', 'load'], name: 'CargoService', desc: 'Manages cargo handling', domain: 'shipping' },
  { keywords: ['bill of lading', '船荷証券', 'b/l'], name: 'BillOfLadingService', desc: 'Manages shipping documents', domain: 'shipping' },
  { keywords: ['container', 'コンテナ', 'unit'], name: 'ShippingContainerService', desc: 'Manages shipping containers', domain: 'shipping' },
  { keywords: ['schedule', '運航', 'voyage'], name: 'VoyageService', desc: 'Manages voyage schedules', domain: 'shipping' },
  { keywords: ['terminal', 'ターミナル', 'yard'], name: 'TerminalService', desc: 'Manages port terminals', domain: 'shipping' },

  // ========================================
  // Railway components
  // ========================================
  { keywords: ['train', '列車', 'rail'], name: 'TrainService', desc: 'Manages train operations', domain: 'railway' },
  { keywords: ['station', '駅', 'platform'], name: 'StationService', desc: 'Manages station facilities', domain: 'railway' },
  { keywords: ['timetable', 'ダイヤ', 'schedule'], name: 'TimetableService', desc: 'Manages train schedules', domain: 'railway' },
  { keywords: ['pass', '定期', 'commuter'], name: 'PassService', desc: 'Manages commuter passes', domain: 'railway' },
  { keywords: ['fare', '運賃', 'price'], name: 'FareService', desc: 'Calculates fares', domain: 'railway' },

  // ========================================
  // Telecom components
  // ========================================
  { keywords: ['line', '回線', 'connection'], name: 'LineService', desc: 'Manages telecom lines', domain: 'telecom' },
  { keywords: ['plan', 'プラン', 'package'], name: 'PlanService', desc: 'Manages service plans', domain: 'telecom' },
  { keywords: ['sim', 'SIM', 'card'], name: 'SimService', desc: 'Manages SIM cards', domain: 'telecom' },
  { keywords: ['usage', '使用量', 'data'], name: 'UsageService', desc: 'Tracks data usage', domain: 'telecom' },
  { keywords: ['billing', '料金', 'charge'], name: 'TelecomBillingService', desc: 'Manages telecom billing', domain: 'telecom' },
  { keywords: ['network', 'ネットワーク', 'coverage'], name: 'NetworkService', desc: 'Manages network infrastructure', domain: 'telecom' },
  { keywords: ['customer', '顧客', 'subscriber'], name: 'TelecomCustomerService', desc: 'Manages telecom customers', domain: 'telecom' },

  // ========================================
  // Security components
  // ========================================
  { keywords: ['access', 'アクセス', 'permission'], name: 'AccessControlService', desc: 'Manages access control', domain: 'security' },
  { keywords: ['audit', '監査', 'log'], name: 'AuditService', desc: 'Manages audit logs', domain: 'security' },
  { keywords: ['vulnerability', '脆弱性', 'threat'], name: 'VulnerabilityService', desc: 'Tracks vulnerabilities', domain: 'security' },
  { keywords: ['encryption', '暗号化', 'cipher'], name: 'EncryptionService', desc: 'Handles encryption', domain: 'security' },
  { keywords: ['firewall', 'ファイアウォール', 'network security'], name: 'FirewallService', desc: 'Manages firewall rules', domain: 'security' },
  { keywords: ['identity', 'アイデンティティ', 'IAM'], name: 'IdentityService', desc: 'Manages identity and access', domain: 'security' },
  { keywords: ['incident', 'インシデント', 'breach'], name: 'SecurityIncidentService', desc: 'Handles security incidents', domain: 'security' },

  // ========================================
  // Environment components
  // ========================================
  { keywords: ['emission', '排出', 'carbon'], name: 'EmissionService', desc: 'Tracks emissions', domain: 'environment' },
  { keywords: ['recycle', 'リサイクル', 'waste'], name: 'RecycleService', desc: 'Manages recycling', domain: 'environment' },
  { keywords: ['sustainability', 'サステナビリティ', 'esg'], name: 'SustainabilityService', desc: 'Tracks sustainability metrics', domain: 'environment' },
  { keywords: ['pollution', '汚染', 'contamination'], name: 'PollutionService', desc: 'Monitors pollution levels', domain: 'environment' },
  { keywords: ['biodiversity', '生物多様性', 'species'], name: 'BiodiversityService', desc: 'Tracks biodiversity', domain: 'environment' },
  { keywords: ['energy efficiency', '省エネ', 'conservation'], name: 'EnergyEfficiencyService', desc: 'Tracks energy efficiency', domain: 'environment' },
  { keywords: ['water quality', '水質', 'wastewater'], name: 'WaterQualityService', desc: 'Monitors water quality', domain: 'environment' },

  // ========================================
  // AgriTech components
  // ========================================
  { keywords: ['crop', '作物', 'plant'], name: 'CropService', desc: 'Manages crop data', domain: 'agritech' },
  { keywords: ['irrigation', '灌漑', 'water'], name: 'IrrigationService', desc: 'Controls irrigation', domain: 'agritech' },
  { keywords: ['soil', '土壌', 'ground'], name: 'SoilService', desc: 'Monitors soil conditions', domain: 'agritech' },
  { keywords: ['weather', '天候', 'climate'], name: 'WeatherService', desc: 'Provides weather data', domain: 'agritech' },
  { keywords: ['drone', 'ドローン', 'aerial'], name: 'DroneService', desc: 'Manages drone operations', domain: 'agritech' },
  { keywords: ['greenhouse', '温室', 'ハウス'], name: 'GreenhouseService', desc: 'Controls greenhouse environment', domain: 'agritech' },
  { keywords: ['pest', '害虫', 'disease'], name: 'PestControlService', desc: 'Manages pest control', domain: 'agritech' },

  // ========================================
  // Beauty/Salon components
  // ========================================
  { keywords: ['stylist', 'スタイリスト', 'beautician'], name: 'StylistService', desc: 'Manages stylists', domain: 'beauty' },
  { keywords: ['treatment', '施術', 'service'], name: 'TreatmentService', desc: 'Manages treatments', domain: 'beauty' },
  { keywords: ['appointment', 'アポイントメント', 'booking'], name: 'SalonAppointmentService', desc: 'Schedules appointments', domain: 'beauty' },
  { keywords: ['menu', 'メニュー', 'price list'], name: 'BeautyMenuService', desc: 'Manages service menu', domain: 'beauty' },
  { keywords: ['customer', '顧客', 'client'], name: 'BeautyCustomerService', desc: 'Manages customer profiles', domain: 'beauty' },
  { keywords: ['product', '商品', 'retail'], name: 'BeautyProductService', desc: 'Manages retail products', domain: 'beauty' },
  { keywords: ['coupon', 'クーポン', 'discount'], name: 'BeautyCouponService', desc: 'Manages coupons', domain: 'beauty' },

  // ========================================
  // Property Management components
  // ========================================
  { keywords: ['maintenance', '修繕', 'repair'], name: 'MaintenanceService', desc: 'Manages maintenance', domain: 'property' },
  { keywords: ['board', '理事会', 'committee'], name: 'BoardService', desc: 'Manages board meetings', domain: 'property' },
  { keywords: ['common area', '共用部', 'facility'], name: 'FacilityService', desc: 'Manages facilities', domain: 'property' },
  { keywords: ['fee', '管理費', 'dues'], name: 'FeeService', desc: 'Manages fees', domain: 'property' },
  { keywords: ['owner', 'オーナー', 'resident'], name: 'PropertyOwnerService', desc: 'Manages property owners', domain: 'property' },
  { keywords: ['repair fund', '修繕積立', 'reserve'], name: 'RepairFundService', desc: 'Manages repair funds', domain: 'property' },
  { keywords: ['parking', '駐車場', 'parking lot'], name: 'PropertyParkingService', desc: 'Manages parking allocation', domain: 'property' },

  // ========================================
  // Caregiving components
  // ========================================
  { keywords: ['resident', '入居者', 'patient'], name: 'ResidentService', desc: 'Manages residents', domain: 'caregiving' },
  { keywords: ['care plan', 'ケアプラン', 'treatment'], name: 'CarePlanService', desc: 'Manages care plans', domain: 'caregiving' },
  { keywords: ['caregiver', '介護士', 'staff'], name: 'CaregiverService', desc: 'Manages caregivers', domain: 'caregiving' },
  { keywords: ['family', '家族', 'contact'], name: 'FamilyService', desc: 'Manages family contacts', domain: 'caregiving' },
  { keywords: ['meal', '食事', 'nutrition'], name: 'MealService', desc: 'Manages meal plans', domain: 'caregiving' },
  { keywords: ['medication', '服薬', 'medicine'], name: 'CaregivingMedicationService', desc: 'Tracks medication', domain: 'caregiving' },
  { keywords: ['activity', 'アクティビティ', 'recreation'], name: 'ActivityService', desc: 'Manages activities', domain: 'caregiving' },

  // ========================================
  // Childcare components
  // ========================================
  { keywords: ['child', '園児', 'kid'], name: 'ChildService', desc: 'Manages child records', domain: 'childcare' },
  { keywords: ['parent', '保護者', 'guardian'], name: 'ParentService', desc: 'Manages parent info', domain: 'childcare' },
  { keywords: ['diary', '連絡帳', 'communication'], name: 'DiaryService', desc: 'Manages daily reports', domain: 'childcare' },
  { keywords: ['allergy', 'アレルギー', 'health'], name: 'AllergyService', desc: 'Tracks allergies', domain: 'childcare' },
  { keywords: ['pickup', 'お迎え', 'dropoff'], name: 'PickupDropoffService', desc: 'Manages pickup/dropoff', domain: 'childcare' },
  { keywords: ['nap', 'お昼寝', 'sleep'], name: 'NapService', desc: 'Tracks nap schedules', domain: 'childcare' },
  { keywords: ['meal', '給食', 'snack'], name: 'ChildcareMealService', desc: 'Manages meals', domain: 'childcare' },

  // ========================================
  // Archive/Document components
  // ========================================
  { keywords: ['document', '資料', 'file'], name: 'DocumentService', desc: 'Manages documents', domain: 'archive' },
  { keywords: ['metadata', 'メタデータ', 'tag'], name: 'MetadataService', desc: 'Manages metadata', domain: 'archive' },
  { keywords: ['digitization', 'デジタル化', 'scan'], name: 'DigitizationService', desc: 'Handles digitization', domain: 'archive' },
  { keywords: ['preservation', '保存', 'archive'], name: 'PreservationService', desc: 'Manages preservation', domain: 'archive' },
  { keywords: ['classification', '分類', 'category'], name: 'ClassificationService', desc: 'Manages classification', domain: 'archive' },
  { keywords: ['access control', 'アクセス制御', 'permission'], name: 'ArchiveAccessService', desc: 'Controls document access', domain: 'archive' },
  { keywords: ['version', 'バージョン', 'revision'], name: 'VersionService', desc: 'Manages document versions', domain: 'archive' },

  // ========================================
  // Ticketing/Event components
  // ========================================
  { keywords: ['ticket', 'チケット', 'admission'], name: 'TicketService', desc: 'Manages tickets', domain: 'ticketing' },
  { keywords: ['seat', '座席', 'section'], name: 'SeatAllocationService', desc: 'Manages seat allocation', domain: 'ticketing' },
  { keywords: ['performance', '公演', 'show'], name: 'PerformanceService', desc: 'Manages performances', domain: 'ticketing' },
  { keywords: ['entrance', '入場', 'admission'], name: 'EntranceService', desc: 'Handles entrance control', domain: 'ticketing' },
  { keywords: ['qr', 'QR', 'barcode'], name: 'QRService', desc: 'Manages QR codes', domain: 'ticketing' },

  // ========================================
  // Pharmacy components
  // ========================================
  { keywords: ['prescription', '処方箋', 'rx'], name: 'PrescriptionService', desc: 'Manages prescriptions', domain: 'pharmacy' },
  { keywords: ['dispensing', '調剤', 'dispense'], name: 'DispensingService', desc: 'Handles drug dispensing', domain: 'pharmacy' },
  { keywords: ['drug', '薬', 'medication'], name: 'DrugService', desc: 'Manages drug inventory', domain: 'pharmacy' },
  { keywords: ['pharmacist', '薬剤師', 'pharmacy staff'], name: 'PharmacistService', desc: 'Manages pharmacist assignments', domain: 'pharmacy' },
  { keywords: ['dosage', '用量', 'dose'], name: 'DosageService', desc: 'Calculates dosages', domain: 'pharmacy' },
  { keywords: ['refill', '補充', 'renewal'], name: 'RefillService', desc: 'Handles prescription refills', domain: 'pharmacy' },

  // ========================================
  // Veterinary components
  // ========================================
  { keywords: ['animal', '動物', 'pet'], name: 'AnimalService', desc: 'Manages animal records', domain: 'veterinary' },
  { keywords: ['veterinarian', '獣医', 'vet'], name: 'VeterinarianService', desc: 'Manages veterinarian schedules', domain: 'veterinary' },
  { keywords: ['vaccination', 'ワクチン', 'immunization'], name: 'VetVaccinationService', desc: 'Tracks vaccinations', domain: 'veterinary' },
  { keywords: ['diagnosis', '診断', 'examination'], name: 'VetDiagnosisService', desc: 'Records diagnoses', domain: 'veterinary' },
  { keywords: ['treatment', '治療', 'procedure'], name: 'VetTreatmentService', desc: 'Manages treatments', domain: 'veterinary' },

  // ========================================
  // Museum components
  // ========================================
  { keywords: ['exhibit', '展示', 'display'], name: 'ExhibitService', desc: 'Manages exhibits', domain: 'museum' },
  { keywords: ['collection', 'コレクション', 'artifact'], name: 'CollectionService', desc: 'Manages collections', domain: 'museum' },
  { keywords: ['curator', '学芸員', 'conservator'], name: 'CuratorService', desc: 'Manages curators', domain: 'museum' },
  { keywords: ['visitor', '来館者', 'guest'], name: 'MuseumVisitorService', desc: 'Manages visitors', domain: 'museum' },
  { keywords: ['gallery', 'ギャラリー', 'room'], name: 'GalleryService', desc: 'Manages gallery spaces', domain: 'museum' },

  // ========================================
  // Cinema components
  // ========================================
  { keywords: ['movie', '映画', 'film'], name: 'MovieService', desc: 'Manages movies', domain: 'cinema' },
  { keywords: ['screening', '上映', 'show'], name: 'ScreeningService', desc: 'Manages screenings', domain: 'cinema' },
  { keywords: ['theater', 'シアター', 'hall'], name: 'TheaterService', desc: 'Manages theater rooms', domain: 'cinema' },
  { keywords: ['showtime', '上映時間', 'schedule'], name: 'ShowtimeService', desc: 'Manages showtimes', domain: 'cinema' },
  { keywords: ['concession', '売店', 'snack'], name: 'ConcessionService', desc: 'Manages concessions', domain: 'cinema' },

  // ========================================
  // Parking components
  // ========================================
  { keywords: ['space', 'スペース', 'slot'], name: 'ParkingSpaceService', desc: 'Manages parking spaces', domain: 'parking' },
  { keywords: ['gate', 'ゲート', 'barrier'], name: 'GateService', desc: 'Controls gates', domain: 'parking' },
  { keywords: ['fee', '料金', 'rate'], name: 'ParkingFeeService', desc: 'Calculates fees', domain: 'parking' },
  { keywords: ['lot', '駐車場', 'area'], name: 'LotService', desc: 'Manages parking lots', domain: 'parking' },
  { keywords: ['validation', '認証', 'validation'], name: 'ParkingValidationService', desc: 'Validates parking', domain: 'parking' },

  // ========================================
  // Laundry components
  // ========================================
  { keywords: ['garment', '衣類', 'clothes'], name: 'GarmentService', desc: 'Manages garments', domain: 'laundry' },
  { keywords: ['cleaning', 'クリーニング', 'wash'], name: 'CleaningService', desc: 'Handles cleaning', domain: 'laundry' },
  { keywords: ['pickup', '集荷', 'collection'], name: 'PickupService', desc: 'Schedules pickups', domain: 'laundry' },
  { keywords: ['delivery', '配達', 'return'], name: 'LaundryDeliveryService', desc: 'Handles delivery', domain: 'laundry' },
  { keywords: ['stain', 'シミ', 'spot'], name: 'StainService', desc: 'Handles stain removal', domain: 'laundry' },

  // ========================================
  // Rental components
  // ========================================
  { keywords: ['rental', 'レンタル', 'rent'], name: 'RentalService', desc: 'Manages rentals', domain: 'rental' },
  { keywords: ['item', 'アイテム', 'product'], name: 'RentalItemService', desc: 'Manages rental items', domain: 'rental' },
  { keywords: ['return', '返却', 'return'], name: 'ReturnService', desc: 'Handles returns', domain: 'rental' },
  { keywords: ['deposit', '保証金', 'security'], name: 'DepositService', desc: 'Manages deposits', domain: 'rental' },
  { keywords: ['duration', '期間', 'period'], name: 'DurationService', desc: 'Manages rental periods', domain: 'rental' },

  // ========================================
  // Subscription components
  // ========================================
  { keywords: ['plan', 'プラン', 'tier'], name: 'SubscriptionPlanService', desc: 'Manages plans', domain: 'subscription' },
  { keywords: ['billing', '請求', 'charge'], name: 'BillingService', desc: 'Handles billing', domain: 'subscription' },
  { keywords: ['renewal', '更新', 'renew'], name: 'RenewalService', desc: 'Handles renewals', domain: 'subscription' },
  { keywords: ['cancellation', '解約', 'cancel'], name: 'CancellationService', desc: 'Handles cancellations', domain: 'subscription' },
  { keywords: ['upgrade', 'アップグレード', 'downgrade'], name: 'UpgradeService', desc: 'Handles plan changes', domain: 'subscription' },

  // ========================================
  // Crowdfunding components
  // ========================================
  { keywords: ['project', 'プロジェクト', 'campaign'], name: 'CrowdfundingProjectService', desc: 'Manages projects', domain: 'crowdfunding' },
  { keywords: ['backer', '支援者', 'supporter'], name: 'BackerService', desc: 'Manages backers', domain: 'crowdfunding' },
  { keywords: ['pledge', '支援', 'contribution'], name: 'PledgeService', desc: 'Handles pledges', domain: 'crowdfunding' },
  { keywords: ['reward', 'リターン', 'perk'], name: 'RewardService', desc: 'Manages rewards', domain: 'crowdfunding' },
  { keywords: ['funding', '資金', 'goal'], name: 'FundingService', desc: 'Tracks funding progress', domain: 'crowdfunding' },

  // ========================================
  // Auction components
  // ========================================
  { keywords: ['bid', '入札', 'bidding'], name: 'BidService', desc: 'Manages bids', domain: 'auction' },
  { keywords: ['lot', '出品', 'item'], name: 'AuctionLotService', desc: 'Manages auction lots', domain: 'auction' },
  { keywords: ['bidder', '入札者', 'participant'], name: 'BidderService', desc: 'Manages bidders', domain: 'auction' },
  { keywords: ['hammer', '落札', 'winning'], name: 'HammerService', desc: 'Handles winning bids', domain: 'auction' },
  { keywords: ['reserve', '最低価格', 'minimum'], name: 'ReserveService', desc: 'Manages reserve prices', domain: 'auction' },

  // ========================================
  // Wedding components
  // ========================================
  { keywords: ['bride', '花嫁', 'groom'], name: 'CoupleService', desc: 'Manages couple info', domain: 'wedding' },
  { keywords: ['ceremony', '挙式', 'wedding'], name: 'CeremonyService', desc: 'Manages ceremonies', domain: 'wedding' },
  { keywords: ['venue', '会場', 'location'], name: 'WeddingVenueService', desc: 'Manages venues', domain: 'wedding' },
  { keywords: ['guest', 'ゲスト', 'invitation'], name: 'WeddingGuestService', desc: 'Manages guests', domain: 'wedding' },
  { keywords: ['reception', '披露宴', 'party'], name: 'ReceptionService', desc: 'Manages receptions', domain: 'wedding' },

  // ========================================
  // Funeral components
  // ========================================
  { keywords: ['deceased', '故人', 'departed'], name: 'DeceasedService', desc: 'Manages deceased info', domain: 'funeral' },
  { keywords: ['ceremony', '葬儀', 'service'], name: 'FuneralCeremonyService', desc: 'Manages ceremonies', domain: 'funeral' },
  { keywords: ['mourner', '参列者', 'attendee'], name: 'MournerService', desc: 'Manages mourners', domain: 'funeral' },
  { keywords: ['cremation', '火葬', 'burial'], name: 'CremationService', desc: 'Handles cremation/burial', domain: 'funeral' },
  { keywords: ['memorial', '供養', 'remembrance'], name: 'MemorialService', desc: 'Manages memorials', domain: 'funeral' },

  // ========================================
  // Charity components
  // ========================================
  { keywords: ['donation', '寄付', 'contribute'], name: 'DonationService', desc: 'Manages donations', domain: 'charity' },
  { keywords: ['donor', '寄付者', 'giver'], name: 'DonorService', desc: 'Manages donors', domain: 'charity' },
  { keywords: ['beneficiary', '受益者', 'recipient'], name: 'BeneficiaryService', desc: 'Manages beneficiaries', domain: 'charity' },
  { keywords: ['volunteer', 'ボランティア', 'helper'], name: 'VolunteerService', desc: 'Manages volunteers', domain: 'charity' },
  { keywords: ['campaign', 'キャンペーン', 'drive'], name: 'CharityCampaignService', desc: 'Manages campaigns', domain: 'charity' },

  // ========================================
  // Government components
  // ========================================
  { keywords: ['citizen', '市民', 'resident'], name: 'CitizenService', desc: 'Manages citizen records', domain: 'government' },
  { keywords: ['application', '申請', 'request'], name: 'ApplicationService', desc: 'Handles applications', domain: 'government' },
  { keywords: ['permit', '許可', 'license'], name: 'PermitService', desc: 'Manages permits', domain: 'government' },
  { keywords: ['certificate', '証明書', 'document'], name: 'GovCertificateService', desc: 'Issues certificates', domain: 'government' },
  { keywords: ['registration', '届出', 'register'], name: 'GovRegistrationService', desc: 'Handles registrations', domain: 'government' },

  // ========================================
  // Election components
  // ========================================
  { keywords: ['voter', '有権者', 'elector'], name: 'VoterService', desc: 'Manages voters', domain: 'election' },
  { keywords: ['candidate', '候補者', 'nominee'], name: 'ElectionCandidateService', desc: 'Manages candidates', domain: 'election' },
  { keywords: ['ballot', '投票用紙', 'vote'], name: 'BallotService', desc: 'Manages ballots', domain: 'election' },
  { keywords: ['poll', '投票所', 'station'], name: 'PollService', desc: 'Manages polling stations', domain: 'election' },
  { keywords: ['counting', '開票', 'tally'], name: 'CountingService', desc: 'Handles vote counting', domain: 'election' },

  // ========================================
  // Survey components
  // ========================================
  { keywords: ['question', '質問', 'item'], name: 'QuestionService', desc: 'Manages questions', domain: 'survey' },
  { keywords: ['response', '回答', 'answer'], name: 'ResponseService', desc: 'Collects responses', domain: 'survey' },
  { keywords: ['respondent', '回答者', 'participant'], name: 'RespondentService', desc: 'Manages respondents', domain: 'survey' },
  { keywords: ['analysis', '分析', 'result'], name: 'SurveyAnalysisService', desc: 'Analyzes results', domain: 'survey' },
  { keywords: ['questionnaire', 'アンケート', 'form'], name: 'QuestionnaireService', desc: 'Manages questionnaires', domain: 'survey' },

  // ========================================
  // E-learning components
  // ========================================
  { keywords: ['course', 'コース', 'class'], name: 'ElearningCourseService', desc: 'Manages courses', domain: 'elearning' },
  { keywords: ['learner', '受講者', 'student'], name: 'LearnerService', desc: 'Manages learners', domain: 'elearning' },
  { keywords: ['quiz', 'クイズ', 'test'], name: 'QuizService', desc: 'Manages quizzes', domain: 'elearning' },
  { keywords: ['progress', '進捗', 'completion'], name: 'ProgressService', desc: 'Tracks progress', domain: 'elearning' },
  { keywords: ['certificate', '修了証', 'credential'], name: 'ElearningCertificateService', desc: 'Issues certificates', domain: 'elearning' },

  // ========================================
  // News components
  // ========================================
  { keywords: ['article', '記事', 'story'], name: 'NewsArticleService', desc: 'Manages articles', domain: 'news' },
  { keywords: ['reporter', '記者', 'journalist'], name: 'ReporterService', desc: 'Manages reporters', domain: 'news' },
  { keywords: ['headline', '見出し', 'title'], name: 'HeadlineService', desc: 'Manages headlines', domain: 'news' },
  { keywords: ['breaking', '速報', 'urgent'], name: 'BreakingNewsService', desc: 'Handles breaking news', domain: 'news' },
  { keywords: ['category', 'カテゴリ', 'section'], name: 'NewsCategoryService', desc: 'Manages categories', domain: 'news' },

  // ========================================
  // Podcast components
  // ========================================
  { keywords: ['episode', 'エピソード', 'show'], name: 'EpisodeService', desc: 'Manages episodes', domain: 'podcast' },
  { keywords: ['host', 'ホスト', 'presenter'], name: 'HostService', desc: 'Manages hosts', domain: 'podcast' },
  { keywords: ['listener', 'リスナー', 'audience'], name: 'ListenerService', desc: 'Manages listeners', domain: 'podcast' },
  { keywords: ['download', 'ダウンロード', 'stream'], name: 'DownloadService', desc: 'Tracks downloads', domain: 'podcast' },
  { keywords: ['subscribe', '購読', 'follow'], name: 'PodcastSubscribeService', desc: 'Manages subscriptions', domain: 'podcast' },

  // ========================================
  // Streaming components
  // ========================================
  { keywords: ['content', 'コンテンツ', 'media'], name: 'ContentService', desc: 'Manages content', domain: 'streaming' },
  { keywords: ['viewer', '視聴者', 'watcher'], name: 'ViewerService', desc: 'Manages viewers', domain: 'streaming' },
  { keywords: ['channel', 'チャンネル', 'stream'], name: 'ChannelService', desc: 'Manages channels', domain: 'streaming' },
  { keywords: ['live', 'ライブ', 'broadcast'], name: 'LiveService', desc: 'Handles live streams', domain: 'streaming' },
  { keywords: ['vod', 'VOD', 'on-demand'], name: 'VODService', desc: 'Manages VOD content', domain: 'streaming' },
];

/**
 * Domain-specific keyword mappings for traceability
 */
export const DOMAIN_KEYWORD_MAPPINGS: Record<string, string[]> = {
  'crop': ['crop', 'plant', '作物', '栽培', 'field', 'cultivate', 'grow'],
  'harvest': ['harvest', '収穫', 'yield', '収量', 'pick', 'gather'],
  'weather': ['weather', '天気', 'climate', 'temperature', 'rainfall', 'forecast'],
  'growth': ['growth', '成長', '生育', 'stage', 'development', 'mature'],
  'equipment': ['equipment', '機器', '農機', 'machinery', 'tool', 'tractor'],
  'field': ['field', '圃場', 'soil', '土壌', 'land'],
  'irrigation': ['irrigation', '灌漑', 'water', '水やり', 'sprinkler'],
  'book': ['book', '図書', '本', '書籍', 'title', 'isbn', 'author'],
  'loan': ['loan', '貸出', 'borrow', '借りる', 'checkout', 'return'],
  'member': ['member', '会員', 'patron', '利用者', 'card'],
  'reservation': ['reservation', '予約', 'reserve', 'hold', 'queue'],
  'catalog': ['catalog', 'カタログ', '目録', 'collection'],
  'fine': ['fine', '延滞', 'penalty', 'overdue', 'late'],
  'workout': ['workout', 'exercise', '運動', 'トレーニング', 'fitness', 'gym'],
  'progress': ['progress', '進捗', 'achievement', 'milestone', 'goal'],
  'trainer': ['trainer', 'トレーナー', 'coach', 'instructor', 'personal'],
  'nutrition': ['nutrition', '栄養', 'diet', '食事', 'calorie', 'meal'],
  'goal': ['goal', '目標', 'target', 'objective', 'aim'],
  'membership': ['membership', 'メンバーシップ', 'subscription', 'plan'],
  'pet': ['pet', 'ペット', '動物', 'dog', 'cat', 'animal'],
  'veterinary': ['veterinary', 'vet', '獣医', 'clinic', 'checkup'],
  'grooming': ['grooming', 'グルーミング', 'トリミング', 'bath', 'haircut'],
  'vaccination': ['vaccination', 'ワクチン', '予防接種', 'shot', 'immunization'],
  'feeding': ['feeding', '給餌', 'food', 'フード', 'meal'],
  'adoption': ['adoption', '譲渡', '里親', 'adopt', 'rescue'],
  'track': ['track', 'song', '曲', '楽曲', 'audio', 'music'],
  'playlist': ['playlist', 'プレイリスト', 'collection', 'queue'],
  'streaming': ['streaming', 'ストリーミング', 'play', '再生', 'buffer'],
  'artist': ['artist', 'アーティスト', 'musician', 'band', 'singer'],
  'album': ['album', 'アルバム', 'release', 'ep', 'single'],
  'recommendation': ['recommendation', 'おすすめ', 'suggest', 'personalize'],
  'vehicle': ['vehicle', '車両', '車', 'car', 'automobile', 'auto'],
  'maintenance': ['maintenance', 'メンテナンス', '整備', 'service', 'repair'],
  'parts': ['parts', '部品', 'パーツ', 'component', 'spare'],
  'mileage': ['mileage', '走行距離', 'odometer', 'km', 'miles'],
  'repair': ['repair', '修理', 'fix', 'breakdown', 'damage'],
  'inspection': ['inspection', '点検', '検査', 'check', 'examine'],
  'event': ['event', 'イベント', '催し', 'conference', 'meeting', 'seminar'],
  'venue': ['venue', '会場', 'location', '場所', 'room', 'hall'],
  'ticket': ['ticket', 'チケット', '入場', 'admission', 'pass'],
  'registration': ['registration', '登録', 'signup', 'rsvp', 'enroll'],
  'attendee': ['attendee', '参加者', 'participant', 'guest'],
  'speaker': ['speaker', 'スピーカー', '登壇者', 'presenter'],
  'claim': ['claim', '請求', '保険金', 'file', 'submit'],
  'policy': ['policy', '契約', 'ポリシー', '保険', 'coverage', 'insurance'],
  'assessment': ['assessment', '査定', '審査', 'evaluation', 'review'],
  'premium': ['premium', '保険料', 'payment', 'fee', 'cost'],
  'underwriting': ['underwriting', '引受', 'risk', 'approve'],
  'document': ['document', '書類', 'ドキュメント', 'file', 'attachment'],
  'candidate': ['candidate', '候補者', 'applicant', '応募者', 'talent'],
  'job': ['job', '求人', 'position', 'ポジション', 'vacancy', 'opening'],
  'interview': ['interview', '面接', 'screen', 'assessment'],
  'resume': ['resume', '履歴書', 'cv', 'profile', 'experience'],
  'offer': ['offer', 'オファー', '内定', 'proposal', 'contract'],
  'onboarding': ['onboarding', 'オンボーディング', '入社', 'induction'],
  'warehouse': ['warehouse', '倉庫', 'storage', 'facility'],
  'shipment': ['shipment', '出荷', 'shipping', '配送', 'dispatch'],
  'picking': ['picking', 'ピッキング', 'pick', 'fulfill'],
  'receiving': ['receiving', '入荷', 'receipt', '受入', 'inbound'],
  'location': ['location', 'ロケーション', 'bin', '棚', 'zone', 'aisle'],
  'packing': ['packing', '梱包', 'package', 'box', 'wrap'],
  'device': ['device', 'デバイス', '機器', 'sensor', 'センサー', 'actuator'],
  'telemetry': ['telemetry', 'テレメトリ', 'metric', 'メトリック', 'data', 'reading'],
  'alert': ['alert', 'アラート', '警告', 'threshold', 'しきい値', 'trigger'],
  'iot': ['iot', 'internet of things', 'connected', 'smart', 'スマート'],
  'firmware': ['firmware', 'ファームウェア', 'version', 'update', 'ota'],
  'protocol': ['protocol', 'プロトコル', 'mqtt', 'http', 'websocket', 'coap'],
  'gateway': ['gateway', 'ゲートウェイ', 'proxy', 'プロキシ', 'api'],
  'route': ['route', 'ルート', 'routing', 'ルーティング', 'path', 'endpoint'],
  'ratelimit': ['rate', 'limit', 'throttle', 'quota', '制限', 'レートリミット'],
  'circuit': ['circuit', 'サーキット', 'breaker', 'ブレーカー', 'fallback'],
  'cache': ['cache', 'キャッシュ', 'ttl', 'invalidate', 'refresh'],
  'loadbalance': ['load', 'balance', 'ロードバランス', 'distribution', 'round-robin'],
  'notification': ['notify', 'alert', 'message', 'email', 'sms', '通知'],
  'auth': ['auth', 'login', 'user', 'session', 'permission', '認証'],
  'data': ['data', 'store', 'persist', 'save', 'repository', 'database'],
  'validation': ['valid', 'check', 'verify', 'confirm', '検証'],
  'search': ['search', 'find', 'query', 'filter', '検索'],
  'priority': ['priority', '優先', 'urgent', 'important'],
  'schedule': ['schedule', 'deadline', '期限', 'calendar', 'time'],
  'order': ['order', '注文', 'purchase', 'buy'],
  'payment': ['payment', '支払', 'pay', 'transaction', 'charge'],
  'inventory': ['inventory', 'stock', '在庫', 'quantity', 'level'],
};

/**
 * Generate C4 model from content
 */
export function generateC4Model(content: string, level: C4Level): C4Model {
  const elements: C4Element[] = [];
  const relationships: C4Relationship[] = [];
  const seenIds = new Set<string>();

  const isEarsDoc = content.includes('EARS') || content.includes('SHALL') || content.includes('REQ-');

  if (isEarsDoc) {
    const contentLower = content.toLowerCase();

    if (contentLower.includes('user') || contentLower.includes('ユーザー')) {
      elements.push({
        id: 'user',
        name: 'User',
        description: 'System user who interacts with the application',
        type: 'person',
      });
    }

    const detectedDomains = detectDomainFromContent(contentLower);

    for (const inference of COMPONENT_INFERENCES) {
      const isDomainMatch = inference.domain === 'general' || detectedDomains.includes(inference.domain);

      if (isDomainMatch && inference.keywords.some(kw => hasKeywordMatch(content, kw))) {
        const id = inference.name.toLowerCase().replace(/service|manager|repository/gi, '');
        if (!seenIds.has(id)) {
          seenIds.add(id);
          elements.push({
            id,
            name: inference.name,
            description: inference.desc,
            type: level === 'context' ? 'software_system' : level === 'container' ? 'container' : 'component',
            technology: 'TypeScript',
          });
        }
      }
    }

    if (elements.filter(e => e.type !== 'person').length === 0) {
      elements.push({
        id: 'main-service',
        name: 'MainService',
        description: 'Core application service',
        type: level === 'context' ? 'software_system' : 'component',
        technology: 'TypeScript',
      });
    }

    const persons = elements.filter(e => e.type === 'person');
    const services = elements.filter(e => e.type !== 'person');

    for (const person of persons) {
      for (const service of services) {
        if (service.name.includes('Service') || service.name.includes('Manager')) {
          relationships.push({
            source: person.id,
            target: service.id,
            description: 'uses',
          });
        }
      }
    }

    const repository = services.find(s => s.name.includes('Repository'));
    if (repository) {
      for (const service of services) {
        if (service.id !== repository.id && !service.name.includes('Notification')) {
          relationships.push({
            source: service.id,
            target: repository.id,
            description: 'stores data in',
          });
        }
      }
    }

    const notificationService = services.find(s => s.name.includes('Notification'));
    if (notificationService) {
      for (const service of services) {
        if (service.id !== notificationService.id && service.name.includes('Service')) {
          relationships.push({
            source: service.id,
            target: notificationService.id,
            description: 'sends notifications via',
          });
        }
      }
    }
  } else {
    const systemMatches = content.match(/\b(?:system|service|application|component|module)\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];
    const actorMatches = content.match(/\b(?:user|admin|client|actor)\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];

    for (const match of actorMatches) {
      const name = match.split(/\s+/).pop()?.replace(/["']/g, '') || 'Unknown';
      const id = `person-${name.toLowerCase()}`;
      if (!seenIds.has(id)) {
        seenIds.add(id);
        elements.push({
          id,
          name,
          description: `${name} user/actor`,
          type: 'person',
        });
      }
    }

    for (const match of systemMatches) {
      const words = match.split(/\s+/);
      const type = words[0].toLowerCase();
      const name = words.pop()?.replace(/["']/g, '') || 'Unknown';
      const id = `${type}-${name.toLowerCase()}`;
      if (!seenIds.has(id)) {
        seenIds.add(id);
        elements.push({
          id,
          name,
          description: `${name} ${type}`,
          type: level === 'context' ? 'software_system' : level === 'container' ? 'container' : 'component',
        });
      }
    }

    const elementIds = elements.map(e => e.id);
    for (let i = 0; i < elementIds.length - 1; i++) {
      relationships.push({
        source: elementIds[i],
        target: elementIds[i + 1],
        description: 'interacts with',
      });
    }
  }

  return {
    level,
    title: `${level.charAt(0).toUpperCase() + level.slice(1)} Diagram`,
    elements,
    relationships,
  };
}

/**
 * Generate traceability with intelligent requirement-to-element mapping
 */
export function generateTraceability(content: string, model: C4Model): Array<{ requirement: string; designElement: string }> {
  const traceability: Array<{ requirement: string; designElement: string }> = [];

  const reqPattern = /REQ-[A-Z]+-\d+(?:-[A-Z]+)?/g;
  const reqMatches = content.match(reqPattern) || [];
  const uniqueReqs = [...new Set(reqMatches)];

  const elementKeywords: Map<string, string[]> = new Map();

  for (const el of model.elements) {
    const keywords: string[] = [];
    const nameLower = el.name.toLowerCase();
    const descLower = el.description.toLowerCase();

    for (const [domain, domainWords] of Object.entries(DOMAIN_KEYWORD_MAPPINGS)) {
      if (nameLower.includes(domain) || descLower.includes(domain)) {
        keywords.push(...domainWords);
      }
    }

    if (nameLower.includes('service')) keywords.push('service', 'logic', 'business', 'process');
    if (nameLower.includes('repository')) keywords.push('repository', 'data', 'store', 'persist', 'save');
    if (nameLower.includes('manager')) keywords.push('manage', 'control', 'handle');

    const descWords = descLower.split(/[\s,.-]+/).filter(w => w.length > 3);
    keywords.push(...descWords);

    elementKeywords.set(el.id, [...new Set(keywords)]);
  }

  const lines = content.split('\n');
  const reqContextMap: Map<string, string> = new Map();

  for (let i = 0; i < lines.length; i++) {
    for (const req of uniqueReqs) {
      if (lines[i].includes(req)) {
        const context = lines.slice(Math.max(0, i - 3), Math.min(lines.length, i + 4)).join(' ').toLowerCase();
        reqContextMap.set(req, context);
      }
    }
  }

  for (const req of uniqueReqs) {
    const reqContext = reqContextMap.get(req) || req.toLowerCase();
    let bestMatch = model.elements[0]?.id || 'unknown';
    let bestScore = 0;

    for (const [elementId, keywords] of elementKeywords) {
      let score = 0;
      for (const keyword of keywords) {
        if (reqContext.includes(keyword)) {
          score += 1;
        }
      }
      const reqParts = req.toLowerCase().split('-');
      for (const part of reqParts) {
        if (keywords.some(k => k.includes(part) || part.includes(k))) {
          score += 2;
        }
      }

      if (score > bestScore) {
        bestScore = score;
        bestMatch = elementId;
      }
    }

    traceability.push({
      requirement: req,
      designElement: bestMatch,
    });
  }

  return traceability;
}
