/**
 * Traceability Types
 * 
 * トレーサビリティDBの型定義
 */

/**
 * トレースリンクの種類
 */
export type TraceLinkType =
  | 'implements'      // 要件を実装する
  | 'derives'         // から派生する
  | 'refines'         // を詳細化する
  | 'satisfies'       // を満たす
  | 'verifies'        // を検証する
  | 'traces'          // をトレースする
  | 'depends'         // に依存する
  | 'conflicts'       // と競合する
  | 'related';        // と関連する

/**
 * トレースノードの種類
 */
export type TraceNodeType =
  | 'requirement'     // 要件 (REQ-*)
  | 'design'          // 設計 (DES-*)
  | 'component'       // コンポーネント (COMP-*)
  | 'code'            // コード (CODE-*)
  | 'test'            // テスト (TEST-*)
  | 'task';           // タスク (TSK-*)

/**
 * トレースノード
 */
export interface TraceNode {
  /** ノードID (例: REQ-001, DES-002) */
  id: string;
  /** ノードタイプ */
  type: TraceNodeType;
  /** タイトル/説明 */
  title: string;
  /** 詳細情報 */
  description?: string;
  /** バージョン */
  version?: string;
  /** 作成日時 */
  createdAt: Date;
  /** 更新日時 */
  updatedAt: Date;
  /** メタデータ */
  metadata?: Record<string, unknown>;
}

/**
 * トレースノード入力（日時フィールドはオプショナル）
 */
export interface TraceNodeInput {
  /** ノードID (例: REQ-001, DES-002) */
  id: string;
  /** ノードタイプ */
  type: TraceNodeType;
  /** タイトル/説明 */
  title: string;
  /** 詳細情報 */
  description?: string;
  /** バージョン */
  version?: string;
  /** 作成日時（省略時は現在時刻） */
  createdAt?: Date;
  /** 更新日時（省略時は現在時刻） */
  updatedAt?: Date;
  /** メタデータ */
  metadata?: Record<string, unknown>;
}

/**
 * トレースリンク
 */
export interface TraceLink {
  /** リンクID (自動生成) */
  id?: string;
  /** ソースノードID */
  source: string;
  /** ターゲットノードID */
  target: string;
  /** リンクタイプ */
  type: TraceLinkType;
  /** リンクの説明 */
  description?: string;
  /** 信頼度 (0-1) */
  confidence?: number;
  /** 作成日時 */
  createdAt?: Date;
  /** メタデータ */
  metadata?: Record<string, unknown>;
}

/**
 * 影響分析結果
 */
export interface ImpactResult {
  /** 起点ノードID */
  sourceId: string;
  /** 影響を受けるノード */
  impactedNodes: ImpactedNode[];
  /** 分析深度 */
  depth: number;
  /** 総影響ノード数 */
  totalImpacted: number;
  /** 分析時間（ミリ秒） */
  duration: number;
}

/**
 * 影響を受けるノード
 */
export interface ImpactedNode {
  /** ノードID */
  id: string;
  /** ノードタイプ */
  type: TraceNodeType;
  /** タイトル */
  title: string;
  /** 起点からの距離（ホップ数） */
  distance: number;
  /** 影響パス */
  path: string[];
  /** リンクタイプ */
  linkType: TraceLinkType;
  /** 影響度 (0-1) */
  impactScore: number;
}

/**
 * クエリオプション
 */
export interface TraceQueryOptions {
  /** 検索するリンクタイプ */
  linkTypes?: TraceLinkType[];
  /** 検索するノードタイプ */
  nodeTypes?: TraceNodeType[];
  /** 最大深度 */
  maxDepth?: number;
  /** 方向 */
  direction?: 'forward' | 'backward' | 'both';
  /** 最小信頼度 */
  minConfidence?: number;
}

/**
 * クエリ結果
 */
export interface TraceQueryResult {
  /** 検索元ノード */
  source: TraceNode | null;
  /** 関連ノード */
  relatedNodes: TraceNode[];
  /** リンク */
  links: TraceLink[];
  /** 検索パス */
  paths: string[][];
}

/**
 * DB統計情報
 */
export interface TraceDbStats {
  /** ノード数 */
  nodeCount: number;
  /** リンク数 */
  linkCount: number;
  /** ノードタイプ別カウント */
  nodesByType: Record<TraceNodeType, number>;
  /** リンクタイプ別カウント */
  linksByType: Record<TraceLinkType, number>;
  /** 孤立ノード数 */
  orphanNodes: number;
  /** 最終更新日時 */
  lastUpdated: Date | null;
}
