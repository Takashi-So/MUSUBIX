/**
 * @nahisaho/musubix-expert-delegation
 * Expert Delegation System - Type Definitions
 *
 * DES-EXP-001, DES-FMT-001, DES-PRV-001
 * Traces to: REQ-EXP-001, REQ-FMT-001, REQ-PRV-001
 */

// =============================================================================
// Expert Types
// =============================================================================

/**
 * エキスパートの種類
 */
export type ExpertType =
  | 'architect'
  | 'security-analyst'
  | 'code-reviewer'
  | 'plan-reviewer'
  | 'ears-analyst' // MUSUBIX独自
  | 'formal-verifier' // MUSUBIX独自
  | 'ontology-reasoner'; // MUSUBIX独自

/**
 * 実行モード
 */
export type ExecutionMode = 'advisory' | 'implementation';

/**
 * トリガーパターン
 */
export interface TriggerPattern {
  readonly pattern: string | RegExp;
  readonly language: 'en' | 'ja' | 'any';
  readonly priority: number; // 0-100
}

/**
 * エキスパートの能力
 */
export interface ExpertCapability {
  name: string;
  mode: ExecutionMode;
  description: string;
}

/**
 * エキスパート定義
 */
export interface Expert {
  readonly type: ExpertType;
  readonly name: string;
  readonly description: string;
  readonly systemPrompt: string;
  readonly triggers: TriggerPattern[];
  readonly ontologyClass: string;
  readonly capabilities: readonly ExpertCapability[];
}

// =============================================================================
// Delegation Types
// =============================================================================

/**
 * アクティブファイル情報
 */
export interface ActiveFile {
  path: string;
  content?: string;
}

/**
 * コンテキスト情報
 */
export interface DelegationContext {
  userMessage: string;
  mode?: ExecutionMode;
  activeFiles?: ActiveFile[];
  relatedRequirements?: string[];
  relatedDesigns?: string[];
  constitutionArticles?: string[];
  traceLinks?: TraceLink[];
}

/**
 * トレースリンク
 */
export interface TraceLink {
  sourceId: string; // e.g., "REQ-EXP-001"
  targetId: string; // e.g., "DES-EXP-001"
  type: 'traces-to' | 'implements' | 'derives' | 'tests';
}

/**
 * 憲法違反警告
 */
export interface ConstitutionViolation {
  article: string; // 'I' - 'X'
  name: string;
  severity: 'warning' | 'error' | 'critical';
  description: string;
}

/**
 * 委任タスク
 */
export interface DelegationTask {
  id: string;
  context: DelegationContext;
  expertType?: ExpertType;
  mode?: ExecutionMode;
  createdAt: Date;
}

/**
 * 委任結果
 */
export interface DelegationResult {
  success: boolean;
  expertType: ExpertType;
  mode: ExecutionMode;
  content: string;
  confidence: number;
  metadata?: Record<string, unknown>;
}

// =============================================================================
// =============================================================================
// Provider Types
// =============================================================================

/**
 * チャットメッセージ
 */
export interface ChatMessage {
  role: 'system' | 'user' | 'assistant';
  content: string;
}

/**
 * リクエストオプション
 */
export interface RequestOptions {
  messages: ChatMessage[];
  model?: string;
  temperature?: number;
  maxTokens?: number;
  cancellationToken?: { isCancellationRequested: boolean };
}

/**
 * プロバイダーレスポンス
 */
export interface ProviderResponse {
  content: string;
  finishReason?: 'stop' | 'length' | 'error';
  usage?: {
    promptTokens: number;
    completionTokens: number;
    totalTokens: number;
  };
}

/**
 * モデル情報
 */
export interface ModelInfo {
  id: string;
  name: string;
  family: string;
  version: string;
  maxInputTokens: number;
  vendor: string;
}

/**
 * モデル選択条件
 */
export interface ModelCriteria {
  family?: string; // e.g., 'gpt-4', 'claude-3'
  version?: string;
  vendor?: string; // e.g., 'copilot', 'openai'
  minTokens?: number;
}

/**
 * LLMプロバイダーインターフェース
 */
export interface LMProvider {
  /**
   * プロンプトを送信してレスポンスを取得
   */
  sendRequest(options: RequestOptions): Promise<ProviderResponse>;

  /**
   * 利用可能なモデル一覧を取得
   */
  listModels(): Promise<ModelInfo[]>;

  /**
   * 条件に合うモデルを選択
   */
  selectModel(criteria?: ModelCriteria): Promise<ModelInfo | null>;
}

// =============================================================================
// Trigger Types
// =============================================================================

/**
 * 意図検出結果
 */
export interface IntentResult {
  detected: boolean;
  expert: ExpertType | null;
  confidence: number; // 0-1
  matchedPattern?: string;
  language?: 'en' | 'ja' | 'unknown';
}

// =============================================================================
// Model Statistics Types
// =============================================================================

/**
 * モデル統計
 */
export interface ModelStats {
  model: string;
  successCount: number;
  failureCount: number;
  totalLatencyMs: number;
  avgLatencyMs: number;
  lastUsed: Date;
}
