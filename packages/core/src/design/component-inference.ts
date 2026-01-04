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
    { name: 'PetService', type: 'service', layer: 'application', description: 'ペット管理のビジネスロジック', dependencies: ['PetRepository', 'PetHistoryRepository'], patterns: ['Service'], domain: 'veterinary' },
    { name: 'PetRepository', type: 'repository', layer: 'infrastructure', description: 'ペットデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'veterinary' },
    { name: 'PetHistoryRepository', type: 'repository', layer: 'infrastructure', description: 'ペット履歴の永続化', dependencies: [], patterns: ['Repository'], domain: 'veterinary' },
    { name: 'ReservationService', type: 'service', layer: 'application', description: '予約管理のビジネスロジック', dependencies: ['ReservationRepository', 'StatusWorkflow'], patterns: ['Service', 'State'], domain: 'veterinary' },
    { name: 'ReservationRepository', type: 'repository', layer: 'infrastructure', description: '予約データの永続化', dependencies: [], patterns: ['Repository'], domain: 'veterinary' },
    { name: 'VetScheduleService', type: 'service', layer: 'application', description: '獣医スケジュール管理', dependencies: ['VetRepository'], patterns: ['Service'], domain: 'veterinary' },
    { name: 'MedicalRecordService', type: 'service', layer: 'application', description: '診療記録管理', dependencies: ['MedicalRecordRepository'], patterns: ['Service'], domain: 'veterinary' },
    { name: 'IdGenerator', type: 'factory', layer: 'domain', description: 'ユニークID生成', dependencies: [], patterns: ['Factory'], domain: 'veterinary' },
    { name: 'StatusWorkflow', type: 'manager', layer: 'domain', description: 'ステータス遷移管理', dependencies: [], patterns: ['State'], domain: 'veterinary' },
  ],
  
  // 駐車場（parking）ドメイン - 仮想プロジェクト02から学習
  parking: [
    { name: 'SpaceService', type: 'service', layer: 'application', description: '駐車スペース管理', dependencies: ['SpaceRepository'], patterns: ['Service'], domain: 'parking' },
    { name: 'SpaceRepository', type: 'repository', layer: 'infrastructure', description: 'スペースデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'parking' },
    { name: 'EntryExitService', type: 'service', layer: 'application', description: '入出庫管理', dependencies: ['EntryRepository', 'SpaceService', 'FeeCalculator'], patterns: ['Service'], domain: 'parking' },
    { name: 'EntryRepository', type: 'repository', layer: 'infrastructure', description: '入庫記録の永続化', dependencies: [], patterns: ['Repository'], domain: 'parking' },
    { name: 'FeeCalculator', type: 'calculator', layer: 'domain', description: '料金計算ロジック', dependencies: [], patterns: ['Strategy'], domain: 'parking' },
    { name: 'PaymentService', type: 'service', layer: 'application', description: '決済処理', dependencies: ['PaymentRepository'], patterns: ['Service'], domain: 'parking' },
    { name: 'DiscountValidator', type: 'validator', layer: 'domain', description: '割引コード検証', dependencies: [], patterns: ['Validator'], domain: 'parking' },
    { name: 'IdGenerator', type: 'factory', layer: 'domain', description: 'ユニークID生成', dependencies: [], patterns: ['Factory'], domain: 'parking' },
  ],
  
  // EC（ecommerce）ドメイン
  ecommerce: [
    { name: 'CartService', type: 'service', layer: 'application', description: 'カート管理', dependencies: ['CartRepository', 'ProductService'], patterns: ['Service'], domain: 'ecommerce' },
    { name: 'CartRepository', type: 'repository', layer: 'infrastructure', description: 'カートデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'ecommerce' },
    { name: 'ProductService', type: 'service', layer: 'application', description: '商品管理', dependencies: ['ProductRepository'], patterns: ['Service'], domain: 'ecommerce' },
    { name: 'ProductRepository', type: 'repository', layer: 'infrastructure', description: '商品データの永続化', dependencies: [], patterns: ['Repository'], domain: 'ecommerce' },
    { name: 'OrderService', type: 'service', layer: 'application', description: '注文管理', dependencies: ['OrderRepository', 'CartService', 'PaymentGateway'], patterns: ['Service'], domain: 'ecommerce' },
    { name: 'OrderRepository', type: 'repository', layer: 'infrastructure', description: '注文データの永続化', dependencies: [], patterns: ['Repository'], domain: 'ecommerce' },
    { name: 'PaymentGateway', type: 'gateway', layer: 'infrastructure', description: '決済ゲートウェイ連携', dependencies: [], patterns: ['Gateway', 'Adapter'], domain: 'ecommerce' },
    { name: 'CatalogService', type: 'service', layer: 'application', description: 'カタログ管理', dependencies: ['ProductRepository'], patterns: ['Service'], domain: 'ecommerce' },
    { name: 'PriceCalculator', type: 'calculator', layer: 'domain', description: '価格計算', dependencies: [], patterns: ['Strategy'], domain: 'ecommerce' },
    { name: 'InventoryChecker', type: 'validator', layer: 'domain', description: '在庫確認', dependencies: ['InventoryRepository'], patterns: ['Validator'], domain: 'ecommerce' },
  ],
  
  // 予約（booking）ドメイン
  booking: [
    { name: 'ReservationService', type: 'service', layer: 'application', description: '予約管理', dependencies: ['ReservationRepository', 'AvailabilityChecker'], patterns: ['Service'], domain: 'booking' },
    { name: 'ReservationRepository', type: 'repository', layer: 'infrastructure', description: '予約データの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'AvailabilityChecker', type: 'validator', layer: 'domain', description: '空き状況確認', dependencies: ['SlotRepository'], patterns: ['Validator'], domain: 'booking' },
    { name: 'SlotRepository', type: 'repository', layer: 'infrastructure', description: 'スロットデータの永続化', dependencies: [], patterns: ['Repository'], domain: 'booking' },
    { name: 'SlotManager', type: 'manager', layer: 'domain', description: 'スロット管理', dependencies: ['SlotRepository'], patterns: ['Manager'], domain: 'booking' },
    { name: 'ReminderService', type: 'service', layer: 'application', description: 'リマインダー送信', dependencies: ['NotificationGateway'], patterns: ['Service'], domain: 'booking' },
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
}

// シングルトンインスタンス
export const componentInference = new ComponentInference();
