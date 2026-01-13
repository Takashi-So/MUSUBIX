# MUSUBIX v3.2.0 設計書
# Expert Delegation System - C4モデル設計

**文書ID**: DES-MUSUBIX-v3.2.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-13  
**ステータス**: Draft  
**準拠規格**: C4 Model  
**参照文書**: REQ-MUSUBIX-v3.2.0.md

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.2.0 Expert Delegation Systemの設計をC4モデルに基づいて定義する。

### 1.2 設計原則

| 原則 | 説明 |
|------|------|
| **Library-First** | 憲法条項Iに準拠。独立パッケージとして実装 |
| **Dependency Inversion** | プロバイダーはインターフェースに依存 |
| **Single Responsibility** | 各コンポーネントは単一責務 |
| **Stateless Design** | 委任呼び出しはステートレス |

---

## 2. C4 Level 1: System Context

```
┌─────────────────────────────────────────────────────────────────────┐
│                        External Systems                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   ┌──────────────┐    ┌──────────────┐    ┌──────────────┐         │
│   │   VS Code    │    │   GitHub     │    │    User      │         │
│   │   LM API     │    │   Copilot    │    │  (Developer) │         │
│   └──────┬───────┘    └──────┬───────┘    └──────┬───────┘         │
│          │                   │                   │                  │
│          └───────────────────┼───────────────────┘                  │
│                              │                                       │
│                              ▼                                       │
│          ┌───────────────────────────────────────┐                  │
│          │                                       │                  │
│          │     MUSUBIX Expert Delegation         │                  │
│          │           System                      │                  │
│          │                                       │                  │
│          │  ┌─────────────────────────────────┐  │                  │
│          │  │  7 Specialized Experts          │  │                  │
│          │  │  - Architect                    │  │                  │
│          │  │  - Security Analyst             │  │                  │
│          │  │  - Code Reviewer                │  │                  │
│          │  │  - Plan Reviewer                │  │                  │
│          │  │  - EARS Analyst (MUSUBIX)       │  │                  │
│          │  │  - Formal Verifier (MUSUBIX)    │  │                  │
│          │  │  - Ontology Reasoner (MUSUBIX)  │  │                  │
│          │  └─────────────────────────────────┘  │                  │
│          │                                       │                  │
│          └───────────────────────────────────────┘                  │
│                              │                                       │
│                              ▼                                       │
│          ┌───────────────────────────────────────┐                  │
│          │         MUSUBIX Core System           │                  │
│          │  (ontology-mcp, formal-verify, etc.)  │                  │
│          └───────────────────────────────────────┘                  │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.1 外部システム

| システム | 役割 | インターフェース |
|---------|------|-----------------|
| **VS Code LM API** | LLMアクセス提供 | `vscode.lm` |
| **GitHub Copilot** | 認証・モデル提供 | OAuth/API |
| **User** | 開発者 | MCP/CLI |
| **MUSUBIX Core** | 既存機能 | Internal API |

---

## 3. C4 Level 2: Container Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                  Expert Delegation System                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────┐    ┌────────────────────┐                   │
│  │                    │    │                    │                   │
│  │   MCP Server       │◄───│   CLI Interface    │                   │
│  │   (10 new tools)   │    │   (new commands)   │                   │
│  │                    │    │                    │                   │
│  └─────────┬──────────┘    └─────────┬──────────┘                   │
│            │                         │                               │
│            └────────────┬────────────┘                               │
│                         │                                            │
│                         ▼                                            │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                                                               │   │
│  │                 Expert Delegation Core                        │   │
│  │                                                               │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐           │   │
│  │  │   Expert    │  │   Trigger   │  │  Delegation │           │   │
│  │  │   Registry  │  │   Router    │  │   Engine    │           │   │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘           │   │
│  │         │                │                │                   │   │
│  │         └────────────────┼────────────────┘                   │   │
│  │                          │                                    │   │
│  │                          ▼                                    │   │
│  │  ┌──────────────────────────────────────────────────────────┐│   │
│  │  │                   Provider Layer                          ││   │
│  │  │                                                           ││   │
│  │  │  ┌─────────────────────────────────────────────────────┐ ││   │
│  │  │  │           VS Code LM Provider                       │ ││   │
│  │  │  │           (vscode.lm API)                           │ ││   │
│  │  │  └─────────────────────────────────────────────────────┘ ││   │
│  │  │                                                           ││   │
│  │  └──────────────────────────────────────────────────────────┘│   │
│  │                                                               │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                      │
│            │                                                         │
│            ▼                                                         │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                    MUSUBIX Core Integration                   │   │
│  │                                                               │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐           │   │
│  │  │  ontology-  │  │   formal-   │  │    core     │           │   │
│  │  │     mcp     │  │   verify    │  │  (EARS等)   │           │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘           │   │
│  │                                                               │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 3.1 コンテナ一覧

| コンテナ | 技術 | 責務 | トレース |
|---------|------|------|---------|
| **MCP Server** | TypeScript | MCPツール提供 | REQ-MCP-001 |
| **CLI Interface** | TypeScript | CLIコマンド | - |
| **Expert Registry** | TypeScript | エキスパート管理 | REQ-EXP-001 |
| **Trigger Router** | TypeScript | 意図検出・ルーティング | REQ-TRG-001 |
| **Delegation Engine** | TypeScript | 委任実行 | REQ-EXP-002 |
| **VS Code LM Provider** | TypeScript | LLMアクセス | REQ-PRV-001 |

---

## 4. C4 Level 3: Component Diagram

### 4.1 Expert Registry コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Expert Registry                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                      ExpertManager                              │ │
│  │                                                                 │ │
│  │  + registerExpert(expert: Expert): void                         │ │
│  │  + getExpert(type: ExpertType): Expert                          │ │
│  │  + listExperts(): Expert[]                                      │ │
│  │  + getExpertByTrigger(trigger: string): Expert | null           │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                              │                                       │
│                              ▼                                       │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                       Expert Types                              │ │
│  │                                                                 │ │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐            │ │
│  │  │  Architect   │ │  Security    │ │    Code      │            │ │
│  │  │   Expert     │ │   Analyst    │ │   Reviewer   │            │ │
│  │  └──────────────┘ └──────────────┘ └──────────────┘            │ │
│  │                                                                 │ │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐            │ │
│  │  │    Plan      │ │    EARS      │ │   Formal     │            │ │
│  │  │   Reviewer   │ │   Analyst    │ │  Verifier    │            │ │
│  │  └──────────────┘ └──────────────┘ └──────────────┘            │ │
│  │                                                                 │ │
│  │  ┌──────────────┐                                               │ │
│  │  │  Ontology    │                                               │ │
│  │  │  Reasoner    │                                               │ │
│  │  └──────────────┘                                               │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

**トレーサビリティ**: REQ-EXP-001, REQ-EXP-003, REQ-EXP-004, REQ-EXP-005

---

### 4.2 Trigger Router コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Trigger Router                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    SemanticRouter                               │ │
│  │                                                                 │ │
│  │  + detectIntent(message: string): IntentResult                  │ │
│  │  + routeToExpert(intent: IntentResult): Expert                  │ │
│  │  + registerTrigger(pattern: TriggerPattern): void               │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                              │                                       │
│                              ▼                                       │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    TriggerPatterns                              │ │
│  │                                                                 │ │
│  │  ┌─────────────────────────────────────────────────────────┐   │ │
│  │  │ Expert             │ Trigger Patterns (EN/JA)           │   │ │
│  │  ├─────────────────────────────────────────────────────────┤   │ │
│  │  │ Architect          │ "how should I structure"           │   │ │
│  │  │                    │ "アーキテクチャ", "設計"            │   │ │
│  │  ├─────────────────────────────────────────────────────────┤   │ │
│  │  │ Security Analyst   │ "is this secure", "security"       │   │ │
│  │  │                    │ "セキュリティ", "脆弱性"            │   │ │
│  │  ├─────────────────────────────────────────────────────────┤   │ │
│  │  │ Code Reviewer      │ "review this code", "find issues"  │   │ │
│  │  │                    │ "レビュー", "コードチェック"        │   │ │
│  │  ├─────────────────────────────────────────────────────────┤   │ │
│  │  │ Plan Reviewer      │ "review this plan", "validate"     │   │ │
│  │  │                    │ "計画レビュー", "検証"              │   │ │
│  │  ├─────────────────────────────────────────────────────────┤   │ │
│  │  │ EARS Analyst       │ "define requirements", "EARS"      │   │ │
│  │  │                    │ "要件定義", "EARS形式"              │   │ │
│  │  ├─────────────────────────────────────────────────────────┤   │ │
│  │  │ Formal Verifier    │ "formal verification", "prove"     │   │ │
│  │  │                    │ "形式検証", "証明"                  │   │ │
│  │  ├─────────────────────────────────────────────────────────┤   │ │
│  │  │ Ontology Reasoner  │ "infer", "reasoning", "ontology"   │   │ │
│  │  │                    │ "推論", "オントロジー"              │   │ │
│  │  └─────────────────────────────────────────────────────────┘   │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                  ProactiveDelegation                            │ │
│  │                                                                 │ │
│  │  + checkEscalation(failCount: number): boolean                  │ │
│  │  + detectSecurityPattern(code: string): boolean                 │ │
│  │  + detectNonEarsRequirement(text: string): boolean              │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

**トレーサビリティ**: REQ-TRG-001, REQ-TRG-002

---

### 4.3 Delegation Engine コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                       Delegation Engine                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    DelegationEngine                             │ │
│  │                                                                 │ │
│  │  + delegate(task: DelegationTask): Promise<DelegationResult>    │ │
│  │  + setMode(mode: ExecutionMode): void                           │ │
│  │  + buildPrompt(task: DelegationTask): string                    │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                              │                                       │
│              ┌───────────────┼───────────────┐                       │
│              ▼               ▼               ▼                       │
│  ┌──────────────────┐ ┌──────────────────┐ ┌──────────────────┐    │
│  │   AdvisoryMode   │ │Implementation    │ │  PromptBuilder   │    │
│  │                  │ │     Mode         │ │                  │    │
│  │ - readOnly: true │ │ - write: true    │ │ + build7Section()│    │
│  │ - analyze()      │ │ - implement()    │ │ + buildEARS()    │    │
│  │ - recommend()    │ │ - modify()       │ │ + validate()     │    │
│  └──────────────────┘ └──────────────────┘ └──────────────────┘    │
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    RetryHandler                                 │ │
│  │                                                                 │ │
│  │  + retry(task: DelegationTask, error: Error): DelegationResult  │ │
│  │  + escalate(task: DelegationTask): EscalationResult             │ │
│  │  + maxRetries: number = 3                                       │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

**トレーサビリティ**: REQ-EXP-002, REQ-FMT-001, REQ-FMT-002, REQ-MCP-002

---

### 4.4 VS Code LM Provider コンポーネント

```
┌─────────────────────────────────────────────────────────────────────┐
│                     VS Code LM Provider                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    LMProviderInterface                          │ │
│  │                                                                 │ │
│  │  + sendRequest(prompt: string): Promise<string>                 │ │
│  │  + listModels(): Promise<Model[]>                               │ │
│  │  + selectModel(criteria: ModelCriteria): Promise<Model>         │ │
│  │  + isAvailable(): Promise<boolean>                              │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                              │                                       │
│                              ▼                                       │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    VSCodeLMProvider                             │ │
│  │                                                                 │ │
│  │  - vscodeAPI: typeof vscode                                     │ │
│  │  - currentModel: LanguageModelChat | null                       │ │
│  │                                                                 │ │
│  │  + async sendRequest(prompt: string): Promise<string>           │ │
│  │    {                                                            │ │
│  │      const models = await vscode.lm.selectChatModels();         │ │
│  │      const model = models[0];                                   │ │
│  │      const messages = [                                         │ │
│  │        vscode.LanguageModelChatMessage.User(prompt)             │ │
│  │      ];                                                         │ │
│  │      const response = await model.sendRequest(messages);        │ │
│  │      return this.collectResponse(response);                     │ │
│  │    }                                                            │ │
│  │                                                                 │ │
│  │  + async listModels(): Promise<Model[]>                         │ │
│  │    {                                                            │ │
│  │      return await vscode.lm.selectChatModels();                 │ │
│  │    }                                                            │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    ModelSelector                                │ │
│  │                                                                 │ │
│  │  + selectByFamily(family: string): Promise<Model>               │ │
│  │  + selectByVendor(vendor: string): Promise<Model>               │ │
│  │  + fallback(primary: Model, secondary: Model): Promise<Model>   │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                    UsageStatistics                              │ │
│  │                                                                 │ │
│  │  + recordSuccess(model: string, latencyMs: number): void        │ │
│  │  + recordFailure(model: string, error: Error): void             │ │
│  │  + getStats(): ModelStats[]                                     │ │
│  │                                                                 │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

**トレーサビリティ**: REQ-PRV-001, REQ-PRV-002

---

## 5. インターフェース設計

### 5.1 Expert インターフェース

```typescript
// DES-EXP-001: Expert Interface
// Traces to: REQ-EXP-001

/**
 * エキスパートの種類
 */
export type ExpertType =
  | 'architect'
  | 'security-analyst'
  | 'code-reviewer'
  | 'plan-reviewer'
  | 'ears-analyst'      // MUSUBIX独自
  | 'formal-verifier'   // MUSUBIX独自
  | 'ontology-reasoner'; // MUSUBIX独自

/**
 * 実行モード
 */
export type ExecutionMode = 'advisory' | 'implementation';

/**
 * エキスパート定義
 */
export interface Expert {
  readonly type: ExpertType;
  readonly name: string;
  readonly description: string;
  readonly systemPrompt: string;
  readonly triggers: TriggerPattern[];
  readonly ontologyClass: string; // オントロジーマッピング
  readonly capabilities: ExpertCapability[];
}

/**
 * エキスパートの能力
 */
export interface ExpertCapability {
  readonly name: string;
  readonly mode: ExecutionMode;
  readonly description: string;
}

/**
 * トリガーパターン
 */
export interface TriggerPattern {
  readonly pattern: string | RegExp;
  readonly language: 'en' | 'ja' | 'any';
  readonly priority: number; // 0-100
}
```

### 5.2 Delegation インターフェース

```typescript
// DES-FMT-001: Delegation Interface
// Traces to: REQ-FMT-001, REQ-FMT-002

/**
 * 7セクション委任タスク（claude-delegator互換）
 */
export interface DelegationTask {
  // 7セクション（claude-delegator形式）
  task: string;           // TASK: 具体的なゴール
  expectedOutcome: string; // EXPECTED OUTCOME: 成功の定義
  context: DelegationContext; // CONTEXT
  constraints: string[];  // CONSTRAINTS
  mustDo: string[];       // MUST DO
  mustNotDo: string[];    // MUST NOT DO
  outputFormat: string;   // OUTPUT FORMAT

  // MUSUBIX拡張セクション
  earsRequirement?: string;  // EARS REQUIREMENT（オプション）
  traceability?: TraceLink[]; // TRACEABILITY（オプション）
  constitutionCheck?: ConstitutionViolation[]; // CONSTITUTION CHECK（オプション）
}

/**
 * コンテキスト情報
 */
export interface DelegationContext {
  currentState: string;
  relevantCode?: string;
  background: string;
  files?: string[];
}

/**
 * トレースリンク
 */
export interface TraceLink {
  source: string; // e.g., "REQ-EXP-001"
  target: string; // e.g., "DES-EXP-001"
  type: 'implements' | 'derives' | 'tests';
}

/**
 * 憲法違反警告
 */
export interface ConstitutionViolation {
  article: number; // 1-10
  name: string;
  severity: 'warning' | 'error';
  description: string;
}

/**
 * 委任結果
 */
export interface DelegationResult {
  success: boolean;
  expert: ExpertType;
  mode: ExecutionMode;
  response: string;
  recommendations?: string[];
  filesModified?: string[];
  verification?: string;
  retryCount: number;
}
```

### 5.3 Provider インターフェース

```typescript
// DES-PRV-001: Provider Interface
// Traces to: REQ-PRV-001, REQ-PRV-002

/**
 * LLMプロバイダーインターフェース
 */
export interface LMProvider {
  /**
   * プロンプトを送信してレスポンスを取得
   */
  sendRequest(
    prompt: string,
    options?: RequestOptions
  ): Promise<ProviderResponse>;

  /**
   * 利用可能なモデル一覧を取得
   */
  listModels(): Promise<ModelInfo[]>;

  /**
   * 条件に合うモデルを選択
   */
  selectModel(criteria: ModelCriteria): Promise<ModelInfo | null>;

  /**
   * プロバイダーが利用可能かチェック
   */
  isAvailable(): Promise<boolean>;
}

/**
 * リクエストオプション
 */
export interface RequestOptions {
  model?: string;
  temperature?: number;
  maxTokens?: number;
  cancellationToken?: vscode.CancellationToken;
}

/**
 * プロバイダーレスポンス
 */
export interface ProviderResponse {
  content: string;
  model: string;
  usage?: {
    promptTokens: number;
    completionTokens: number;
  };
  latencyMs: number;
}

/**
 * モデル情報
 */
export interface ModelInfo {
  id: string;
  name: string;
  family: string;
  vendor: string;
  maxInputTokens: number;
}

/**
 * モデル選択条件
 */
export interface ModelCriteria {
  family?: string;  // e.g., 'gpt-4', 'claude-3'
  vendor?: string;  // e.g., 'copilot', 'openai'
  minTokens?: number;
}
```

### 5.4 MCP ツールスキーマ

```typescript
// DES-MCP-001: MCP Tool Schemas
// Traces to: REQ-MCP-001

/**
 * expert_delegate ツール
 */
export const expertDelegateSchema = {
  name: 'expert_delegate',
  description: '適切なエキスパートにタスクを委任する',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: '委任するタスクの説明' },
      expert: {
        type: 'string',
        enum: [
          'architect', 'security-analyst', 'code-reviewer',
          'plan-reviewer', 'ears-analyst', 'formal-verifier',
          'ontology-reasoner'
        ],
        description: '委任先エキスパート（省略時は自動選択）'
      },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        description: '実行モード（省略時は自動判定）'
      },
      context: { type: 'string', description: 'コンテキスト情報' }
    },
    required: ['task']
  }
};

/**
 * trigger_detect ツール
 */
export const triggerDetectSchema = {
  name: 'trigger_detect',
  description: 'ユーザー意図を検出してエキスパートをルーティング',
  inputSchema: {
    type: 'object',
    properties: {
      message: { type: 'string', description: 'ユーザーメッセージ' },
      language: {
        type: 'string',
        enum: ['en', 'ja', 'auto'],
        default: 'auto'
      }
    },
    required: ['message']
  }
};

/**
 * delegation_retry ツール
 */
export const delegationRetrySchema = {
  name: 'delegation_retry',
  description: '失敗した委任をリトライ',
  inputSchema: {
    type: 'object',
    properties: {
      taskId: { type: 'string', description: '元のタスクID' },
      errorContext: { type: 'string', description: 'エラー情報' },
      alternativeExpert: { type: 'string', description: '代替エキスパート' }
    },
    required: ['taskId', 'errorContext']
  }
};

/**
 * expert_architect ツール
 */
export const expertArchitectSchema = {
  name: 'expert_architect',
  description: 'アーキテクチャ設計をArchitectエキスパートに委任',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: '設計タスクの説明' },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        default: 'advisory'
      },
      context: { type: 'string', description: 'システムコンテキスト' },
      constraints: {
        type: 'array',
        items: { type: 'string' },
        description: '設計制約'
      }
    },
    required: ['task']
  }
};

/**
 * expert_security ツール
 */
export const expertSecuritySchema = {
  name: 'expert_security',
  description: 'セキュリティ分析をSecurity Analystエキスパートに委任',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: 'セキュリティ分析タスク' },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        default: 'advisory'
      },
      code: { type: 'string', description: '分析対象コード' },
      threatModel: { type: 'string', description: '脅威モデル（オプション）' }
    },
    required: ['task']
  }
};

/**
 * expert_review ツール
 */
export const expertReviewSchema = {
  name: 'expert_review',
  description: 'コードレビューをCode Reviewerエキスパートに委任',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: 'レビュータスク' },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        default: 'advisory'
      },
      code: { type: 'string', description: 'レビュー対象コード' },
      files: {
        type: 'array',
        items: { type: 'string' },
        description: 'レビュー対象ファイルパス'
      }
    },
    required: ['task']
  }
};

/**
 * expert_plan ツール
 */
export const expertPlanSchema = {
  name: 'expert_plan',
  description: '計画レビューをPlan Reviewerエキスパートに委任',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: '計画レビュータスク' },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        default: 'advisory'
      },
      plan: { type: 'string', description: 'レビュー対象の計画/設計書' },
      requirements: {
        type: 'array',
        items: { type: 'string' },
        description: '関連する要件ID（トレーサビリティチェック用）'
      },
      checkConstitution: {
        type: 'boolean',
        default: true,
        description: '憲法条項チェックを実行するか'
      }
    },
    required: ['task', 'plan']
  }
};

/**
 * expert_ears ツール（MUSUBIX独自）
 */
export const expertEarsSchema = {
  name: 'expert_ears',
  description: 'EARS形式要件分析をEARS Analystエキスパートに委任',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: '要件分析タスク' },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        default: 'advisory'
      },
      requirements: { type: 'string', description: '分析対象の要件テキスト' },
      existingReqs: {
        type: 'array',
        items: { type: 'string' },
        description: '既存要件ID（整合性チェック用）'
      }
    },
    required: ['task', 'requirements']
  }
};

/**
 * expert_formal ツール（MUSUBIX独自）
 */
export const expertFormalSchema = {
  name: 'expert_formal',
  description: '形式検証をFormal Verifierエキスパートに委任',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: '形式検証タスク' },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        default: 'advisory'
      },
      specification: { type: 'string', description: '検証対象の仕様' },
      verifier: {
        type: 'string',
        enum: ['z3', 'lean4'],
        default: 'z3',
        description: '使用する検証器'
      }
    },
    required: ['task', 'specification']
  }
};

/**
 * expert_ontology ツール（MUSUBIX独自）
 */
export const expertOntologySchema = {
  name: 'expert_ontology',
  description: 'オントロジー推論をOntology Reasonerエキスパートに委任',
  inputSchema: {
    type: 'object',
    properties: {
      task: { type: 'string', description: '推論タスク' },
      mode: {
        type: 'string',
        enum: ['advisory', 'implementation'],
        default: 'advisory'
      },
      query: { type: 'string', description: 'オントロジークエリ' },
      knowledgeBase: { type: 'string', description: '知識ベースパス（オプション）' }
    },
    required: ['task', 'query']
  }
};

/**
 * provider_select ツール
 */
export const providerSelectSchema = {
  name: 'provider_select',
  description: 'AIモデルを選択',
  inputSchema: {
    type: 'object',
    properties: {
      family: { type: 'string', description: 'モデルファミリー（gpt-4, claude-3等）' },
      vendor: { type: 'string', description: 'ベンダー（copilot等）' },
      minTokens: { type: 'number', description: '最小トークン数' }
    },
    required: []
  }
};
```

### 5.5 エラー型定義

```typescript
// DES-ERR-001: Error Types
// Traces to: REQ-NFR-001

/**
 * 委任エラーの種類
 */
export type DelegationErrorCode =
  | 'EXPERT_NOT_FOUND'      // エキスパートが見つからない
  | 'PROVIDER_UNAVAILABLE'  // プロバイダーが利用不可
  | 'MODEL_NOT_AVAILABLE'   // モデルが利用不可
  | 'TRIGGER_AMBIGUOUS'     // トリガーが曖昧
  | 'PROMPT_TOO_LONG'       // プロンプトが長すぎる
  | 'TIMEOUT'               // タイムアウト
  | 'RATE_LIMITED'          // レート制限
  | 'AUTHENTICATION_FAILED' // 認証失敗
  | 'RETRY_EXHAUSTED'       // リトライ回数超過
  | 'INVALID_MODE'          // 無効なモード
  | 'CONSTITUTION_VIOLATION'; // 憲法違反

/**
 * 委任エラー
 */
export class DelegationError extends Error {
  constructor(
    public readonly code: DelegationErrorCode,
    message: string,
    public readonly expert?: ExpertType,
    public readonly retryable: boolean = false,
    public readonly context?: Record<string, unknown>
  ) {
    super(message);
    this.name = 'DelegationError';
  }

  /**
   * リトライ可能なエラーか判定
   */
  static isRetryable(error: unknown): boolean {
    if (error instanceof DelegationError) {
      return error.retryable;
    }
    return false;
  }

  /**
   * エラーコードからエラーを生成
   */
  static fromCode(
    code: DelegationErrorCode,
    context?: Record<string, unknown>
  ): DelegationError {
    const messages: Record<DelegationErrorCode, string> = {
      EXPERT_NOT_FOUND: '指定されたエキスパートが見つかりません',
      PROVIDER_UNAVAILABLE: 'LLMプロバイダーが利用できません',
      MODEL_NOT_AVAILABLE: '指定されたモデルが利用できません',
      TRIGGER_AMBIGUOUS: 'トリガーが曖昧です。エキスパートを明示的に指定してください',
      PROMPT_TOO_LONG: 'プロンプトがモデルの制限を超えています',
      TIMEOUT: 'リクエストがタイムアウトしました',
      RATE_LIMITED: 'レート制限に達しました。しばらく待ってからリトライしてください',
      AUTHENTICATION_FAILED: 'GitHub Copilotの認証に失敗しました',
      RETRY_EXHAUSTED: 'リトライ回数の上限に達しました',
      INVALID_MODE: '無効な実行モードです',
      CONSTITUTION_VIOLATION: '憲法条項に違反する操作です',
    };

    const retryableCodes: DelegationErrorCode[] = [
      'PROVIDER_UNAVAILABLE',
      'MODEL_NOT_AVAILABLE',
      'TIMEOUT',
      'RATE_LIMITED',
    ];

    return new DelegationError(
      code,
      messages[code],
      undefined,
      retryableCodes.includes(code),
      context
    );
  }
}

/**
 * エスカレーション結果
 */
export interface EscalationResult {
  escalated: boolean;
  reason: string;
  suggestedExpert?: ExpertType;
  originalError: DelegationError;
  retryCount: number;
}
```

---

## 6. シーケンス図

### 6.1 基本委任フロー

```
User            MCP Server       Trigger Router    Expert Registry   Delegation Engine   VS Code LM
  │                 │                 │                 │                 │                 │
  │  expert_delegate│                 │                 │                 │                 │
  │ ───────────────>│                 │                 │                 │                 │
  │                 │                 │                 │                 │                 │
  │                 │ detectIntent    │                 │                 │                 │
  │                 │ ───────────────>│                 │                 │                 │
  │                 │                 │                 │                 │                 │
  │                 │                 │ getExpert       │                 │                 │
  │                 │                 │ ───────────────>│                 │                 │
  │                 │                 │                 │                 │                 │
  │                 │                 │<─ Expert ───────│                 │                 │
  │                 │                 │                 │                 │                 │
  │                 │<─ IntentResult ─│                 │                 │                 │
  │                 │                 │                 │                 │                 │
  │                 │ delegate                          │                 │                 │
  │                 │ ─────────────────────────────────>│                 │                 │
  │                 │                                   │                 │                 │
  │                 │                                   │ buildPrompt     │                 │
  │                 │                                   │ ───────────────>│                 │
  │                 │                                   │                 │                 │
  │                 │                                   │                 │ sendRequest     │
  │                 │                                   │                 │ ───────────────>│
  │                 │                                   │                 │                 │
  │                 │                                   │                 │<─ response ─────│
  │                 │                                   │                 │                 │
  │                 │                                   │<─ Delegation ───│                 │
  │                 │                                   │    Result       │                 │
  │                 │<─────────────────────────────────│                 │                 │
  │                 │                                                                       │
  │<─ Result ───────│                                                                       │
  │                 │                                                                       │
```

### 6.2 リトライフロー

```
User            MCP Server       Delegation Engine   RetryHandler      VS Code LM
  │                 │                 │                 │                 │
  │  (初回失敗)     │                 │                 │                 │
  │                 │                 │                 │                 │
  │                 │ delegate        │                 │                 │
  │                 │ ───────────────>│                 │                 │
  │                 │                 │ sendRequest     │                 │
  │                 │                 │ ────────────────────────────────>│
  │                 │                 │<─ error ─────────────────────────│
  │                 │                 │                 │                 │
  │                 │                 │ retry           │                 │
  │                 │                 │ ───────────────>│                 │
  │                 │                 │                 │ buildRetryPrompt│
  │                 │                 │                 │ (with context)  │
  │                 │                 │                 │ sendRequest     │
  │                 │                 │                 │ ───────────────>│
  │                 │                 │                 │<─ response ─────│
  │                 │                 │<───────────────│                 │
  │                 │<───────────────│                 │                 │
  │<───────────────│                 │                 │                 │
  │                 │                 │                 │                 │
  │  (3回失敗後)    │                 │                 │                 │
  │                 │                 │ escalate        │                 │
  │                 │                 │ ───────────────>│                 │
  │                 │                 │<─ Escalation ──│                 │
  │                 │<───────────────│                 │                 │
  │<─ "エスカレーション提案" ─────────│                 │                 │
  │                 │                 │                 │                 │
```

---

## 7. ディレクトリ構成

```
packages/expert-delegation/
├── package.json
├── tsconfig.json
├── README.md
├── src/
│   ├── index.ts                    # パッケージエントリポイント
│   │
│   ├── experts/                    # Expert定義
│   │   ├── index.ts
│   │   ├── expert-interface.ts     # Expert型定義
│   │   ├── expert-manager.ts       # ExpertManager実装
│   │   ├── architect.ts            # Architect Expert
│   │   ├── security-analyst.ts     # Security Analyst Expert
│   │   ├── code-reviewer.ts        # Code Reviewer Expert
│   │   ├── plan-reviewer.ts        # Plan Reviewer Expert
│   │   ├── ears-analyst.ts         # EARS Analyst Expert (MUSUBIX)
│   │   ├── formal-verifier.ts      # Formal Verifier Expert (MUSUBIX)
│   │   └── ontology-reasoner.ts    # Ontology Reasoner Expert (MUSUBIX)
│   │
│   ├── triggers/                   # トリガー検出
│   │   ├── index.ts
│   │   ├── semantic-router.ts      # SemanticRouter実装
│   │   ├── trigger-patterns.ts     # TriggerPattern定義
│   │   └── proactive-delegation.ts # ProactiveDelegation実装
│   │
│   ├── delegation/                 # 委任エンジン
│   │   ├── index.ts
│   │   ├── delegation-engine.ts    # DelegationEngine実装
│   │   ├── prompt-builder.ts       # PromptBuilder実装
│   │   ├── advisory-mode.ts        # AdvisoryMode実装
│   │   ├── implementation-mode.ts  # ImplementationMode実装
│   │   └── retry-handler.ts        # RetryHandler実装
│   │
│   ├── providers/                  # LLMプロバイダー
│   │   ├── index.ts
│   │   ├── provider-interface.ts   # LMProvider型定義
│   │   ├── vscode-lm-provider.ts   # VS Code LM Provider実装
│   │   ├── model-selector.ts       # ModelSelector実装
│   │   └── usage-statistics.ts     # UsageStatistics実装
│   │
│   ├── mcp/                        # MCPツール
│   │   ├── index.ts
│   │   ├── tools.ts                # ツール定義
│   │   └── handlers.ts             # ハンドラー実装
│   │
│   └── types/                      # 共通型定義
│       └── index.ts
│
└── tests/
    ├── experts/
    │   ├── expert-manager.test.ts
    │   ├── architect.test.ts
    │   ├── ears-analyst.test.ts
    │   └── ...
    ├── triggers/
    │   ├── semantic-router.test.ts
    │   └── proactive-delegation.test.ts
    ├── delegation/
    │   ├── delegation-engine.test.ts
    │   ├── prompt-builder.test.ts
    │   └── retry-handler.test.ts
    ├── providers/
    │   ├── vscode-lm-provider.test.ts
    │   └── model-selector.test.ts
    ├── mcp/
    │   └── tools.test.ts
    └── __mocks__/                  # VS Code APIモック
        └── vscode.ts
```

---

## 8. テストモック戦略

### 8.1 VS Code LM API モック

VS Code環境外でテストを実行するためのモック戦略。

```typescript
// tests/__mocks__/vscode.ts
// DES-TEST-001: VS Code API Mock
// Traces to: REQ-NFR-002

/**
 * モックLanguageModelChatMessage
 */
export const LanguageModelChatMessage = {
  User: (content: string) => ({ role: 'user', content }),
  Assistant: (content: string) => ({ role: 'assistant', content }),
};

/**
 * モックLanguageModelChat
 */
export class MockLanguageModelChat {
  readonly id: string;
  readonly name: string;
  readonly family: string;
  readonly vendor: string;
  readonly maxInputTokens: number;

  private mockResponse: string;

  constructor(options: {
    id?: string;
    name?: string;
    family?: string;
    vendor?: string;
    maxInputTokens?: number;
    mockResponse?: string;
  } = {}) {
    this.id = options.id ?? 'mock-model';
    this.name = options.name ?? 'Mock Model';
    this.family = options.family ?? 'gpt-4';
    this.vendor = options.vendor ?? 'copilot';
    this.maxInputTokens = options.maxInputTokens ?? 128000;
    this.mockResponse = options.mockResponse ?? 'Mock response';
  }

  async sendRequest(
    messages: Array<{ role: string; content: string }>,
    _options?: unknown,
    _token?: unknown
  ): Promise<AsyncIterable<string>> {
    const response = this.mockResponse;
    return {
      async *[Symbol.asyncIterator]() {
        yield response;
      },
    };
  }

  setMockResponse(response: string): void {
    this.mockResponse = response;
  }
}

/**
 * モックlm名前空間
 */
export const lm = {
  _models: [] as MockLanguageModelChat[],

  async selectChatModels(
    selector?: { family?: string; vendor?: string }
  ): Promise<MockLanguageModelChat[]> {
    if (this._models.length === 0) {
      this._models = [new MockLanguageModelChat()];
    }
    
    if (selector) {
      return this._models.filter(m => {
        if (selector.family && m.family !== selector.family) return false;
        if (selector.vendor && m.vendor !== selector.vendor) return false;
        return true;
      });
    }
    
    return this._models;
  },

  /**
   * テスト用：モックモデルを設定
   */
  __setMockModels(models: MockLanguageModelChat[]): void {
    this._models = models;
  },

  /**
   * テスト用：モックをリセット
   */
  __reset(): void {
    this._models = [];
  },
};

/**
 * モックCancellationToken
 */
export class CancellationTokenSource {
  token = {
    isCancellationRequested: false,
    onCancellationRequested: () => ({ dispose: () => {} }),
  };
  
  cancel(): void {
    this.token.isCancellationRequested = true;
  }
  
  dispose(): void {}
}
```

### 8.2 テストヘルパー

```typescript
// tests/helpers/test-utils.ts
// DES-TEST-002: Test Utilities

import { MockLanguageModelChat, lm } from '../__mocks__/vscode';
import type { Expert, DelegationTask, DelegationResult } from '../../src/types';

/**
 * テスト用エキスパート生成
 */
export function createMockExpert(overrides?: Partial<Expert>): Expert {
  return {
    type: 'architect',
    name: 'Mock Architect',
    description: 'Mock expert for testing',
    systemPrompt: 'You are a mock expert.',
    triggers: [{ pattern: 'test', language: 'en', priority: 50 }],
    ontologyClass: 'sdd:MockExpert',
    capabilities: [{ name: 'analyze', mode: 'advisory', description: 'Mock analysis' }],
    ...overrides,
  };
}

/**
 * テスト用委任タスク生成
 */
export function createMockDelegationTask(overrides?: Partial<DelegationTask>): DelegationTask {
  return {
    task: 'Mock task',
    expectedOutcome: 'Mock outcome',
    context: {
      currentState: 'Initial',
      background: 'Test background',
    },
    constraints: [],
    mustDo: ['Complete the task'],
    mustNotDo: ['Fail'],
    outputFormat: 'JSON',
    ...overrides,
  };
}

/**
 * テスト用委任結果生成
 */
export function createMockDelegationResult(overrides?: Partial<DelegationResult>): DelegationResult {
  return {
    success: true,
    expert: 'architect',
    mode: 'advisory',
    response: 'Mock response',
    retryCount: 0,
    ...overrides,
  };
}

/**
 * VS Code LMモックをセットアップ
 */
export function setupMockLM(options: {
  response?: string;
  models?: MockLanguageModelChat[];
  shouldFail?: boolean;
} = {}): void {
  lm.__reset();

  if (options.models) {
    lm.__setMockModels(options.models);
  } else {
    const model = new MockLanguageModelChat({
      mockResponse: options.response ?? 'Default mock response',
    });
    lm.__setMockModels([model]);
  }
}

/**
 * VS Code LMモックをリセット
 */
export function resetMockLM(): void {
  lm.__reset();
}
```

### 8.3 Vitest設定

```typescript
// vitest.config.ts (expert-delegation package)

import { defineConfig } from 'vitest/config';
import path from 'path';

export default defineConfig({
  test: {
    globals: true,
    environment: 'node',
    include: ['tests/**/*.test.ts'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
      exclude: ['tests/__mocks__/**', 'tests/helpers/**'],
      thresholds: {
        statements: 80,
        branches: 70,
        functions: 80,
        lines: 80,
      },
    },
    alias: {
      vscode: path.resolve(__dirname, 'tests/__mocks__/vscode.ts'),
    },
  },
});
```

---

## 9. 設計決定記録（ADR）

### ADR-001: VS Code LM API採用

| 項目 | 内容 |
|------|------|
| **決定** | 独自APIキー管理ではなく、VS Code LM APIを使用 |
| **理由** | GitHub Copilotユーザーは追加設定不要。APIキー管理の複雑さを排除 |
| **代替案** | OpenAI/Anthropic直接統合 → 却下（APIキー管理が必要） |
| **影響** | VS Code環境でのみ動作。CLI単独実行は制限される |
| **トレース** | REQ-PRV-001 |

### ADR-002: 7エキスパート構成

| 項目 | 内容 |
|------|------|
| **決定** | claude-delegator（5）+ MUSUBIX独自（3）= 7エキスパート |
| **理由** | MUSUBIXの強み（EARS、形式検証、オントロジー）を専門家として提供 |
| **代替案** | claude-delegator互換5エキスパートのみ → 却下（差別化不足） |
| **影響** | 独自エキスパートはMUSUBIX既存パッケージに依存 |
| **トレース** | REQ-EXP-001, REQ-EXP-003, REQ-EXP-004, REQ-EXP-005 |

### ADR-003: EARS拡張フォーマット

| 項目 | 内容 |
|------|------|
| **決定** | 7セクション + EARS/トレーサビリティ/憲法 = 10セクション |
| **理由** | claude-delegator互換性を維持しつつMUSUBIXらしさを追加 |
| **代替案** | 7セクション完全互換 → 却下（MUSUBIX独自価値が薄い） |
| **影響** | 拡張セクションはオプション。claude-delegator互換モードも提供 |
| **トレース** | REQ-FMT-002 |

---

## 10. トレーサビリティマトリクス

| 要件ID | 設計ID | コンポーネント |
|--------|--------|---------------|
| REQ-EXP-001 | DES-EXP-001 | ExpertManager, Expert Types |
| REQ-EXP-002 | DES-EXP-002 | DelegationEngine, AdvisoryMode, ImplementationMode |
| REQ-EXP-003 | DES-EXP-003 | EarsAnalyst Expert |
| REQ-EXP-004 | DES-EXP-004 | FormalVerifier Expert |
| REQ-EXP-005 | DES-EXP-005 | OntologyReasoner Expert |
| REQ-TRG-001 | DES-TRG-001 | SemanticRouter, TriggerPatterns |
| REQ-TRG-002 | DES-TRG-002 | ProactiveDelegation |
| REQ-PRV-001 | DES-PRV-001 | VSCodeLMProvider |
| REQ-PRV-002 | DES-PRV-002 | ModelSelector, UsageStatistics |
| REQ-FMT-001 | DES-FMT-001 | PromptBuilder (7-Section) |
| REQ-FMT-002 | DES-FMT-002 | PromptBuilder (EARS Extended) |
| REQ-MCP-001 | DES-MCP-001 | MCP Tools, Handlers |
| REQ-MCP-002 | DES-MCP-002 | RetryHandler |
| REQ-NFR-001 | DES-NFR-001 | Stateless Design |
| REQ-NFR-002 | DES-NFR-002 | Test Coverage |
| REQ-NFR-003 | DES-NFR-003 | Documentation |

---

## 11. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-13 | 初版作成 | AI Agent |

---

## 12. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-13 | - |
| レビュアー | - | - | - |
| 承認者 | - | - | - |

---

**END OF DOCUMENT**
