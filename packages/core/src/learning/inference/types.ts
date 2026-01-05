/**
 * Advanced Inference Types
 *
 * @module learning/inference/types
 * @description Phase 3: Advanced Inference 型定義
 * @requirements REQ-ONTO-010, REQ-ONTO-011, REQ-ONTO-012, REQ-ONTO-013, REQ-ONTO-014
 */

/**
 * OWL 2 RL ルールタイプ
 * REQ-ONTO-010: OWL 2 RLプロファイル推論
 */
export type OWL2RLRuleType =
  // Class Expression Axioms
  | 'cls-thing'
  | 'cls-nothing1'
  | 'cls-nothing2'
  | 'cls-int1'
  | 'cls-int2'
  | 'cls-uni'
  | 'cls-com'
  | 'cls-svf1'
  | 'cls-svf2'
  | 'cls-avf'
  | 'cls-hv1'
  | 'cls-hv2'
  | 'cls-maxc1'
  | 'cls-maxc2'
  | 'cls-maxqc1'
  | 'cls-maxqc2'
  | 'cls-maxqc3'
  | 'cls-maxqc4'
  | 'cls-oo'
  // Property Expression Axioms
  | 'prp-dom'
  | 'prp-rng'
  | 'prp-fp'
  | 'prp-ifp'
  | 'prp-irp'
  | 'prp-symp'
  | 'prp-asyp'
  | 'prp-trp'
  | 'prp-spo1'
  | 'prp-spo2'
  | 'prp-eqp1'
  | 'prp-eqp2'
  | 'prp-pdw'
  | 'prp-adp'
  | 'prp-inv1'
  | 'prp-inv2'
  | 'prp-key'
  | 'prp-npa1'
  | 'prp-npa2'
  // Class Axioms
  | 'cax-sco'
  | 'cax-eqc1'
  | 'cax-eqc2'
  | 'cax-dw'
  | 'cax-adc'
  // Schema Vocabulary
  | 'scm-cls'
  | 'scm-sco'
  | 'scm-eqc1'
  | 'scm-eqc2'
  | 'scm-op'
  | 'scm-dp'
  | 'scm-spo'
  | 'scm-eqp1'
  | 'scm-eqp2'
  | 'scm-dom1'
  | 'scm-dom2'
  | 'scm-rng1'
  | 'scm-rng2'
  | 'scm-hv'
  | 'scm-svf1'
  | 'scm-svf2'
  | 'scm-avf1'
  | 'scm-avf2'
  | 'scm-int'
  | 'scm-uni'
  // Equality
  | 'eq-ref'
  | 'eq-sym'
  | 'eq-trans'
  | 'eq-rep-s'
  | 'eq-rep-p'
  | 'eq-rep-o'
  | 'eq-diff1'
  | 'eq-diff2'
  | 'eq-diff3';

/**
 * トリプル（RDF基本単位）
 */
export interface Triple {
  subject: string;
  predicate: string;
  object: string;
  graph?: string;
}

/**
 * OWL 2 RLルール定義
 */
export interface OWL2RLRule {
  /** ルールID */
  id: OWL2RLRuleType;
  /** ルール名 */
  name: string;
  /** 説明 */
  description: string;
  /** 前提条件（Datalog形式） */
  antecedent: string[];
  /** 結論 */
  consequent: string[];
  /** 優先度 */
  priority: number;
  /** 有効/無効 */
  enabled: boolean;
}

/**
 * Datalogルール
 * REQ-ONTO-014: Datalogルール統合
 */
export interface DatalogRule {
  /** ルールID */
  id: string;
  /** ルール名 */
  name: string;
  /** 説明 */
  description?: string;
  /** ヘッド（結論） */
  head: DatalogAtom;
  /** ボディ（前提条件） */
  body: DatalogAtom[];
  /** 優先度 */
  priority: number;
  /** 有効/無効 */
  enabled: boolean;
}

/**
 * Datalogアトム
 */
export interface DatalogAtom {
  /** 述語名 */
  predicate: string;
  /** 引数（変数または定数） */
  args: DatalogTerm[];
  /** 否定フラグ */
  negated?: boolean;
}

/**
 * Datalog項
 */
export type DatalogTerm =
  | { type: 'variable'; name: string }
  | { type: 'constant'; value: string }
  | { type: 'literal'; value: string; datatype?: string };

/**
 * 変数バインディング
 */
export type Bindings = Record<string, string>;

/**
 * 推論結果
 */
export interface InferenceResult {
  /** 推論されたトリプル */
  inferredTriples: Triple[];
  /** 適用されたルール */
  appliedRules: AppliedRule[];
  /** 推論統計 */
  stats: InferenceStats;
  /** 説明（オプション） */
  explanations?: InferenceExplanation[];
}

/**
 * 適用されたルール
 */
export interface AppliedRule {
  /** ルールID */
  ruleId: string;
  /** ルール名 */
  ruleName: string;
  /** バインディング */
  bindings: Bindings;
  /** 推論されたトリプル */
  inferredTriples: Triple[];
  /** 適用時刻 */
  appliedAt: number;
}

/**
 * 推論統計
 * REQ-ONTO-011: 200ms以内の推論
 */
export interface InferenceStats {
  /** 適用されたルール数 */
  rulesApplied: number;
  /** 推論されたトリプル数 */
  triplesInferred: number;
  /** 反復回数 */
  iterations: number;
  /** 処理時間（ms） */
  timeMs: number;
  /** 固定点到達 */
  fixedPointReached: boolean;
  /** 入力トリプル数 */
  inputTriples: number;
  /** 出力トリプル数 */
  outputTriples: number;
}

/**
 * 推論説明
 * REQ-ONTO-013: 人間可読な推論説明生成
 */
export interface InferenceExplanation {
  /** 説明ID */
  id: string;
  /** 結論トリプル */
  conclusion: Triple;
  /** 前提トリプル */
  premises: Triple[];
  /** 適用されたルール */
  rule: string;
  /** 人間可読な説明 */
  humanReadable: string;
  /** 推論の深さ */
  depth: number;
  /** 依存する説明ID */
  dependsOn: string[];
}

/**
 * 推論進捗
 * REQ-ONTO-012: 推論進捗フィードバック
 */
export interface InferenceProgress {
  /** 現在のフェーズ */
  phase: 'initializing' | 'loading' | 'reasoning' | 'explaining' | 'completed' | 'error';
  /** 合計トリプル数 */
  totalTriples: number;
  /** 処理済みトリプル数 */
  processedTriples: number;
  /** 推論済みトリプル数 */
  inferredTriples: number;
  /** 経過時間（ms） */
  elapsedMs: number;
  /** 推定残り時間（ms） */
  estimatedRemainingMs: number;
  /** メッセージ */
  message?: string;
}

/**
 * 推論オプション
 */
export interface ReasonerOptions {
  /** 最大イテレーション数 */
  maxIterations?: number;
  /** タイムアウト（ms） */
  timeout?: number;
  /** 説明を生成するか */
  generateExplanations?: boolean;
  /** 進捗コールバック */
  onProgress?: (progress: InferenceProgress) => void;
  /** 有効なルールセット */
  enabledRules?: OWL2RLRuleType[];
  /** 無効なルールセット */
  disabledRules?: OWL2RLRuleType[];
  /** Datalogルール */
  datalogRules?: DatalogRule[];
  /** プロファイル */
  profile?: 'full' | 'el' | 'rl' | 'ql';
}

/**
 * 推論エンジンインターフェース
 */
export interface IReasoner {
  /** 推論を実行 */
  infer(triples: Triple[], options?: ReasonerOptions): Promise<InferenceResult>;
  /** ルールを追加 */
  addRule(rule: DatalogRule): void;
  /** ルールを削除 */
  removeRule(ruleId: string): boolean;
  /** ルール一覧を取得 */
  getRules(): DatalogRule[];
  /** 統計をリセット */
  resetStats(): void;
}

/**
 * 説明生成器インターフェース
 */
export interface IExplainer {
  /** 説明を生成 */
  explain(conclusion: Triple, appliedRules: AppliedRule[]): InferenceExplanation;
  /** 全ての説明を生成 */
  explainAll(result: InferenceResult): InferenceExplanation[];
  /** 説明をフォーマット */
  format(explanation: InferenceExplanation, format: 'text' | 'html' | 'markdown'): string;
}

/**
 * 進捗コールバック
 */
export type ProgressCallback = (progress: InferenceProgress) => void;

/**
 * 進捗レポーターインターフェース
 */
export interface IProgressReporter {
  /** 進捗コールバックを登録 */
  onProgress(callback: ProgressCallback): () => void;
  /** レポートを開始 */
  start(totalTriples: number): void;
  /** 進捗を更新 */
  update(partial: Partial<InferenceProgress>): void;
  /** レポートを完了 */
  complete(inferredTriples: number): void;
  /** 現在の進捗を取得 */
  getProgress(): InferenceProgress;
}

/**
 * クエリ結果
 */
export interface QueryResult {
  /** 結果バインディング */
  bindings: Bindings[];
  /** 実行時間（ms） */
  executionTimeMs: number;
  /** 説明 */
  explanation?: string;
}

/**
 * 名前空間プレフィックス
 */
export const NAMESPACES = {
  RDF: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
  RDFS: 'http://www.w3.org/2000/01/rdf-schema#',
  OWL: 'http://www.w3.org/2002/07/owl#',
  XSD: 'http://www.w3.org/2001/XMLSchema#',
  MUSUBIX: 'http://musubix.dev/ontology#',
} as const;
