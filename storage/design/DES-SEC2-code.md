# MUSUBIX Security v2.0 コード設計書

**プロジェクト**: MUSUBIX Security Subsystem
**バージョン**: 2.0.0
**ステータス**: Draft
**作成日**: 2026-01-07
**関連ドキュメント**: 
- [コンポーネント設計書](DES-SEC2-components.md)
- [アーキテクチャ設計書](DES-SEC2-architecture.md)
- [要件定義書](../specs/REQ-SEC-v2.0.md)

---

## 1. ディレクトリ構造

```
packages/security/
├── src/
│   ├── index.ts                    # パブリックAPI
│   │
│   ├── cli/                        # CLI Interface
│   │   ├── index.ts                # CLI entry point
│   │   ├── commands/
│   │   │   ├── scan.ts             # scan コマンド
│   │   │   ├── taint.ts            # taint コマンド
│   │   │   ├── secrets.ts          # secrets コマンド
│   │   │   ├── audit.ts            # audit コマンド
│   │   │   ├── fix.ts              # fix コマンド
│   │   │   ├── report.ts           # report コマンド
│   │   │   ├── container.ts        # container コマンド
│   │   │   ├── iac.ts              # iac コマンド
│   │   │   └── config.ts           # config コマンド
│   │   └── formatters/
│   │       ├── json.ts
│   │       ├── sarif.ts
│   │       └── table.ts
│   │
│   ├── mcp/                        # MCP Server
│   │   ├── index.ts                # MCP server entry
│   │   ├── tools/
│   │   │   ├── security-scan.ts
│   │   │   ├── taint-analyze.ts
│   │   │   ├── secret-detect.ts
│   │   │   ├── dependency-audit.ts
│   │   │   ├── fix-generate.ts
│   │   │   ├── fix-verify.ts
│   │   │   └── report-generate.ts
│   │   └── prompts/
│   │       ├── security-review.ts
│   │       ├── vulnerability-explain.ts
│   │       └── fix-recommend.ts
│   │
│   ├── lsp/                        # LSP Server
│   │   ├── index.ts
│   │   ├── diagnostics.ts
│   │   ├── code-actions.ts
│   │   └── hover.ts
│   │
│   ├── core/                       # Core Domain
│   │   ├── security-service.ts     # SecurityService
│   │   ├── pipeline-manager.ts     # PipelineManager
│   │   └── result-aggregator.ts    # ResultAggregator
│   │
│   ├── analyzers/                  # Analysis Layer
│   │   ├── sast/
│   │   │   ├── vulnerability-scanner.ts
│   │   │   ├── zero-day-detector.ts           # NEW: ゼロデイ検出
│   │   │   ├── interprocedural-analyzer.ts    # NEW: インタープロシージャ解析
│   │   │   ├── detectors/
│   │   │   │   ├── sql-injection.ts
│   │   │   │   ├── xss.ts
│   │   │   │   ├── path-traversal.ts
│   │   │   │   ├── command-injection.ts
│   │   │   │   ├── insecure-deserialize.ts
│   │   │   │   └── ssrf.ts
│   │   │   └── rules/
│   │   │       └── rule-engine.ts
│   │   │
│   │   ├── taint/
│   │   │   ├── taint-tracker.ts
│   │   │   ├── source-identifier.ts
│   │   │   ├── sink-identifier.ts
│   │   │   ├── sanitizer-verifier.ts          # NEW: サニタイザー検証
│   │   │   └── adapters/
│   │   │       ├── express.ts
│   │   │       ├── fastify.ts
│   │   │       ├── nestjs.ts
│   │   │       └── nextjs.ts
│   │   │
│   │   ├── secrets/
│   │   │   ├── secret-detector.ts
│   │   │   ├── secret-classifier.ts           # NEW: シークレット分類
│   │   │   ├── pre-commit-hook.ts             # NEW: pre-commitフック
│   │   │   ├── entropy-calculator.ts
│   │   │   └── patterns/
│   │   │       ├── aws.ts
│   │   │       ├── github.ts
│   │   │       ├── stripe.ts
│   │   │       └── generic.ts
│   │   │
│   │   ├── dependency/
│   │   │   ├── dependency-auditor.ts
│   │   │   ├── sbom-generator.ts
│   │   │   └── supply-chain-analyzer.ts
│   │   │
│   │   ├── container/
│   │   │   ├── image-scanner.ts
│   │   │   └── dockerfile-analyzer.ts
│   │   │
│   │   ├── iac/
│   │   │   ├── iac-checker.ts
│   │   │   ├── terraform-analyzer.ts
│   │   │   └── kubernetes-analyzer.ts
│   │   │
│   │   └── ai/
│   │       ├── prompt-injection-detector.ts
│   │       └── llm-call-identifier.ts
│   │
│   ├── intelligence/               # Neuro-Symbolic Layer
│   │   ├── neuro-symbolic-core.ts
│   │   ├── llm-analyzer.ts
│   │   └── knowledge-query.ts
│   │
│   ├── fix/                        # Fix Layer
│   │   ├── fix-generator.ts
│   │   ├── z3-verifier.ts
│   │   └── test-generator.ts
│   │
│   ├── report/                     # Reporting
│   │   ├── report-generator.ts
│   │   └── templates/
│   │       ├── html.ts
│   │       ├── pdf.ts
│   │       └── sarif.ts
│   │
│   ├── compliance/                 # Compliance
│   │   ├── compliance-validator.ts
│   │   └── standards/
│   │       ├── owasp.ts
│   │       ├── pci-dss.ts
│   │       └── iso27001.ts
│   │
│   ├── infrastructure/             # Infrastructure
│   │   ├── ast-parser.ts
│   │   ├── yata-client.ts
│   │   ├── llm-client.ts
│   │   ├── cve-client.ts
│   │   ├── cache.ts
│   │   ├── audit-logger.ts
│   │   ├── config-manager.ts
│   │   └── error-handler.ts
│   │
│   └── types/                      # Type Definitions
│       ├── index.ts
│       ├── vulnerability.ts
│       ├── taint.ts
│       ├── secret.ts
│       ├── dependency.ts
│       ├── fix.ts
│       ├── report.ts
│       └── config.ts
│
├── tests/                          # Tests
│   ├── unit/
│   ├── integration/
│   └── fixtures/
│
├── bin/
│   └── musubix-security.js         # CLI binary
│
└── package.json
```

---

## 2. 主要クラス・インターフェース定義

### 2.1 Core Types

#### 2.1.1 Vulnerability型

**ファイル**: `src/types/vulnerability.ts`

```typescript
// DES-SEC2-TYPE-001: 脆弱性の型定義

/**
 * 脆弱性の重大度
 * CVSS v3.1 に基づく分類
 */
export type Severity = 'critical' | 'high' | 'medium' | 'low' | 'info';

/**
 * 脆弱性の検出元
 */
export type DetectionSource = 
  | 'sast'           // 静的解析
  | 'taint'          // テイント分析
  | 'secret'         // シークレット検出
  | 'dependency'     // 依存関係監査
  | 'container'      // コンテナスキャン
  | 'iac'            // IaCチェック
  | 'ai'             // AI/ML脆弱性
  | 'neuro-symbolic'; // Neuro-Symbolic統合

/**
 * ソースコード内の位置
 */
export interface SourceLocation {
  filePath: string;
  startLine: number;
  endLine: number;
  startColumn?: number;
  endColumn?: number;
}

/**
 * 脆弱性
 * REQ-SEC2-SAST-001, REQ-SEC2-TAINT-001 準拠
 */
export interface Vulnerability {
  /** 一意識別子 */
  id: string;
  
  /** タイトル */
  title: string;
  
  /** 説明 */
  description: string;
  
  /** 重大度 */
  severity: Severity;
  
  /** CVSSスコア (0.0-10.0) */
  cvssScore: number;
  
  /** 信頼度 (0.0-1.0) */
  confidence: number;
  
  /** CWE ID */
  cwes: string[];
  
  /** CVE ID (該当する場合) */
  cves?: string[];
  
  /** 検出元 */
  source: DetectionSource;
  
  /** ソースコード位置 */
  location: SourceLocation;
  
  /** 脆弱なコードスニペット */
  codeSnippet: string;
  
  /** 推奨される修正 */
  recommendation: string;
  
  /** 詳細情報URL */
  referenceUrls: string[];
  
  /** データフローパス (テイント分析の場合) */
  dataFlowPath?: TaintPath;
  
  /** Neuro-Symbolic分析結果 */
  neuroSymbolicResult?: NeuroSymbolicResult;
  
  /** 作成日時 */
  createdAt: Date;
}

/**
 * Neuro-Symbolic分析結果
 * REQ-SEC2-SAST-002 準拠
 */
export interface NeuroSymbolicResult {
  /** ニューラル（LLM）の信頼度 */
  neuralConfidence: number;
  
  /** シンボリック検証結果 */
  symbolicValid: boolean;
  
  /** 最終決定 */
  finalDecision: 'confirmed' | 'rejected' | 'needs-review';
  
  /** ニューラル分析による説明 */
  neuralExplanation: string;
  
  /** シンボリック推論のエビデンス */
  symbolicEvidence: Evidence[];
}

/**
 * シンボリック推論のエビデンス
 */
export interface Evidence {
  /** エビデンスの種類 */
  type: 'pattern-match' | 'rule-inference' | 'knowledge-graph';
  
  /** 根拠となるパターンまたはルール */
  source: string;
  
  /** 詳細説明 */
  description: string;
}
```

---

#### 2.1.2 Taint型

**ファイル**: `src/types/taint.ts`

```typescript
// DES-SEC2-TYPE-002: テイント分析の型定義

/**
 * テイントソースの種類
 */
export type TaintSourceType = 
  | 'user-input'    // ユーザー入力 (req.body, req.query等)
  | 'file'          // ファイル読み込み
  | 'network'       // ネットワーク入力
  | 'database'      // データベース読み込み
  | 'environment';  // 環境変数

/**
 * テイントシンクの種類
 */
export type TaintSinkType = 
  | 'sql'           // SQLクエリ
  | 'command'       // OSコマンド
  | 'file'          // ファイルシステム
  | 'html'          // HTMLレンダリング
  | 'url'           // URLリダイレクト
  | 'eval';         // 動的コード実行

/**
 * テイントソース
 * REQ-SEC2-TAINT-001 準拠
 */
export interface TaintSource {
  id: string;
  type: TaintSourceType;
  location: SourceLocation;
  variable: string;
  framework?: string;
}

/**
 * テイントシンク
 */
export interface TaintSink {
  id: string;
  type: TaintSinkType;
  location: SourceLocation;
  requiredSanitizers: string[];
}

/**
 * サニタイザー
 */
export interface Sanitizer {
  id: string;
  name: string;
  sanitizes: TaintSinkType[];
  location: SourceLocation;
}

/**
 * テイントパス内のステップ
 */
export interface TaintStep {
  location: SourceLocation;
  expression: string;
  operation: 'assign' | 'call' | 'return' | 'parameter';
}

/**
 * テイントパス（ソースからシンクへの経路）
 * REQ-SEC2-TAINT-002 準拠
 */
export interface TaintPath {
  source: TaintSource;
  sink: TaintSink;
  steps: TaintStep[];
  sanitizers: Sanitizer[];
  isSafe: boolean;
}

/**
 * テイント分析結果
 */
export interface TaintResult {
  sources: TaintSource[];
  sinks: TaintSink[];
  paths: TaintPath[];
  vulnerablePaths: TaintPath[];
  analyzedFiles: number;
  duration: number;
}

/**
 * サニタイザー検証結果
 * REQ-SEC2-TAINT-003 準拠
 */
export interface SanitizerVerificationResult {
  /** サニタイザーが有効かどうか */
  isEffective: boolean;
  
  /** 理由 */
  reason: string;
  
  /** 警告メッセージ */
  warnings: string[];
  
  /** 推奨サニタイザー */
  recommendation?: SanitizerRecommendation;
}

/**
 * サニタイザー推奨
 */
export interface SanitizerRecommendation {
  sanitizerName: string;
  example: string;
  documentation: string;
}

/**
 * シンクコンテキスト（サニタイザー検証用）
 */
export interface SinkContext {
  sinkType: TaintSinkType;
  framework?: string;
  database?: string;
  outputContext?: 'attribute' | 'element' | 'script' | 'style' | 'url';
}
```

---

#### 2.1.3 Secret型

**ファイル**: `src/types/secret.ts`

```typescript
// DES-SEC2-TYPE-003: シークレット検出の型定義

/**
 * シークレットの種類
 */
export type SecretType = 
  | 'api-key'
  | 'oauth-token'
  | 'password'
  | 'private-key'
  | 'certificate'
  | 'connection-string'
  | 'jwt'
  | 'ssh-key'
  | 'generic';

/**
 * 検出されたシークレット
 * REQ-SEC2-SECRET-001 準拠
 */
export interface Secret {
  /** 一意識別子 */
  id: string;
  
  /** シークレットの種類 */
  type: SecretType;
  
  /** マスクされた値 */
  maskedValue: string;
  
  /** 実際の値（内部処理用、出力時はマスク必須） */
  rawValue?: string;
  
  /** 検出位置 */
  location: SourceLocation;
  
  /** エントロピー値 */
  entropy: number;
  
  /** 信頼度 (0.0-1.0) */
  confidence: number;
  
  /** 関連サービス */
  service?: string;
  
  /** Git履歴で検出された場合のコミット情報 */
  gitInfo?: {
    commit: string;
    author: string;
    date: Date;
  };
}

/**
 * シークレット検出結果
 */
export interface SecretResult {
  secrets: Secret[];
  scannedFiles: number;
  gitHistoryScanned: boolean;
  duration: number;
}

/**
 * Pre-commitフック設定
 * REQ-SEC2-SECRET-003 準拠
 */
export interface PreCommitHookOptions {
  /** 検出時にコミットをブロックするか */
  blockOnDetection: boolean;
  
  /** 許可パターン（正規表現） */
  allowList?: string[];
  
  /** ブロック対象の重大度 */
  severity: Severity[];
}

/**
 * ステージング領域スキャン結果
 */
export interface StagedScanResult {
  secrets: Secret[];
  shouldBlock: boolean;
  message: string;
  alternatives: SecretAlternative[];
}

/**
 * シークレットの安全な代替案
 */
export interface SecretAlternative {
  description: string;
  example: string;
  tool?: string;  // 例: 'dotenv', 'vault', 'aws-secrets-manager'
}
```

---

#### 2.1.4 ZeroDay型

**ファイル**: `src/types/zero-day.ts`

```typescript
// DES-SEC2-TYPE-005: ゼロデイ検出の型定義
// REQ-SEC2-SAST-003 準拠

/**
 * ゼロデイ候補の逸脱タイプ
 */
export type DeviationType = 
  | 'pattern-mismatch'  // 既知パターンとの不一致
  | 'anomaly'           // 異常検出
  | 'unsafe-practice';  // 安全でないプラクティス

/**
 * ゼロデイ脆弱性候補
 */
export interface ZeroDayCandidate {
  /** 一意識別子 */
  id: string;
  
  /** 検出位置 */
  location: SourceLocation;
  
  /** コードスニペット */
  codeSnippet: string;
  
  /** 逸脱タイプ */
  deviationType: DeviationType;
  
  /** 信頼度 (0.0-1.0) */
  confidence: number;
  
  /** LLM分析結果 */
  llmAssessment?: LLMAnalysisResult;
  
  /** 重大度（ゼロデイは常にpotential） */
  severity: 'potential';
  
  /** 説明 */
  explanation: string;
}

/**
 * LLM分析結果
 */
export interface LLMAnalysisResult {
  /** 脆弱性の可能性（0.0-1.0） */
  vulnerabilityLikelihood: number;
  
  /** 分析理由 */
  reasoning: string;
  
  /** 推奨アクション */
  recommendedAction: 'review' | 'investigate' | 'safe';
  
  /** 類似するCWE（推測） */
  potentialCWEs: string[];
}

/**
 * リスク評価
 */
export interface RiskAssessment {
  /** リスクスコア (0-100) */
  score: number;
  
  /** リスク要因 */
  factors: RiskFactor[];
  
  /** 推奨アクション */
  recommendation: 'review' | 'investigate' | 'safe';
}

/**
 * リスク要因
 */
export interface RiskFactor {
  name: string;
  weight: number;
  description: string;
}
```

---

#### 2.1.5 Interprocedural型

**ファイル**: `src/types/interprocedural.ts`

```typescript
// DES-SEC2-TYPE-006: インタープロシージャ解析の型定義
// REQ-SEC2-SAST-004 準拠

/**
 * 呼び出しグラフノード
 */
export interface CallGraphNode {
  /** ノードID */
  id: string;
  
  /** 関数名 */
  name: string;
  
  /** モジュールパス */
  module: string;
  
  /** ソース位置 */
  location: SourceLocation;
  
  /** パラメータ情報 */
  parameters: ParameterInfo[];
  
  /** 戻り値の型 */
  returnType?: string;
}

/**
 * パラメータ情報
 */
export interface ParameterInfo {
  name: string;
  type?: string;
  isTainted?: boolean;
}

/**
 * 呼び出しグラフエッジ
 */
export interface CallGraphEdge {
  /** 呼び出し元 */
  caller: string;
  
  /** 呼び出し先 */
  callee: string;
  
  /** 呼び出し位置 */
  location: SourceLocation;
  
  /** 引数マッピング */
  argumentMapping: ArgumentMapping[];
}

/**
 * 引数マッピング
 */
export interface ArgumentMapping {
  callerExpression: string;
  calleeParameter: string;
}

/**
 * 呼び出しグラフ
 */
export interface CallGraph {
  nodes: CallGraphNode[];
  edges: CallGraphEdge[];
  
  // クエリメソッド（実装時）
  // getCallers(functionId: string): CallGraphNode[];
  // getCallees(functionId: string): CallGraphNode[];
  // getPath(from: string, to: string): CallGraphNode[];
}

/**
 * 循環呼び出し情報
 */
export interface CycleInfo {
  /** 循環に含まれるノード */
  nodes: string[];
  
  /** 循環の開始点 */
  entryPoint: string;
}

/**
 * データフローパス（関数境界越え）
 */
export interface DataFlowPath {
  /** 変数名 */
  variable: string;
  
  /** パス上のステップ */
  steps: DataFlowStep[];
  
  /** 関数境界を越えたか */
  crossesBoundary: boolean;
}

/**
 * データフローステップ
 */
export interface DataFlowStep {
  location: SourceLocation;
  expression: string;
  functionId: string;
  operation: 'define' | 'use' | 'call' | 'return';
}

/**
 * インタープロシージャ解析結果
 */
export interface InterproceduralResult {
  /** 呼び出しグラフ */
  callGraph: CallGraph;
  
  /** データフローパス */
  dataFlows: DataFlowPath[];
  
  /** 検出された循環 */
  cycles: CycleInfo[];
  
  /** 最大深度に達したか */
  maxDepthReached: boolean;
  
  /** 解析時間（ミリ秒） */
  analysisTime: number;
}
```

---

#### 2.1.6 Dependency型

**ファイル**: `src/types/dependency.ts`

```typescript
// DES-SEC2-TYPE-004: 依存関係監査の型定義

/**
 * パッケージエコシステム
 */
export type Ecosystem = 'npm' | 'pip' | 'maven' | 'cargo' | 'go' | 'nuget';

/**
 * 依存関係
 */
export interface Dependency {
  name: string;
  version: string;
  type: 'direct' | 'transitive';
  ecosystem: Ecosystem;
  integrity?: string;
  parent?: string;
}

/**
 * CVE情報
 * REQ-SEC2-DEP-001 準拠
 */
export interface CVE {
  id: string;
  description: string;
  severity: Severity;
  cvssScore: number;
  publishedDate: Date;
  patchedVersions: string[];
  references: string[];
}

/**
 * サプライチェーンリスク
 * REQ-SEC2-DEP-002 準拠
 */
export interface SupplyChainRisk {
  /** タイポスクワッティング検出 */
  typosquatting: boolean;
  typosquattingDetails?: {
    similarPackage: string;
    similarity: number;
  };
  
  /** 依存関係混乱攻撃 */
  dependencyConfusion: boolean;
  
  /** メンテナー変更 */
  maintainerChange: boolean;
  maintainerChangeDetails?: {
    previousMaintainer: string;
    newMaintainer: string;
    changeDate: Date;
  };
  
  /** 悪意あるコードの疑い */
  maliciousCode: boolean;
  
  /** 総合リスクスコア (0-100) */
  riskScore: number;
}

/**
 * 依存関係監査結果
 */
export interface AuditResult {
  dependencies: Dependency[];
  vulnerabilities: {
    dependency: Dependency;
    cves: CVE[];
  }[];
  supplyChainRisks: {
    dependency: Dependency;
    risk: SupplyChainRisk;
  }[];
  summary: {
    total: number;
    direct: number;
    transitive: number;
    vulnerable: number;
    highRisk: number;
  };
  duration: number;
}

/**
 * SBOM (Software Bill of Materials)
 * REQ-SEC2-DEP-003 準拠
 */
export interface SBOM {
  format: 'spdx' | 'cyclonedx';
  version: string;
  createdAt: Date;
  components: SBOMComponent[];
}

export interface SBOMComponent {
  name: string;
  version: string;
  purl: string; // Package URL
  licenses: string[];
  hashes?: {
    algorithm: string;
    value: string;
  }[];
}
```

---

#### 2.1.5 Fix型

**ファイル**: `src/types/fix.ts`

```typescript
// DES-SEC2-TYPE-005: 修正生成の型定義

/**
 * 生成された修正
 * REQ-SEC2-FIX-001 準拠
 */
export interface Fix {
  /** 一意識別子 */
  id: string;
  
  /** 対象脆弱性ID */
  vulnerabilityId: string;
  
  /** 元のコード */
  originalCode: string;
  
  /** 修正後のコード */
  fixedCode: string;
  
  /** 修正の説明 */
  explanation: string;
  
  /** 信頼度 (0.0-1.0) */
  confidence: number;
  
  /** 形式検証済みフラグ */
  verified: boolean;
  
  /** 検証結果 */
  verificationResult?: VerificationResult;
  
  /** 生成されたテストケース */
  testCases?: TestCase[];
  
  /** 差分 */
  diff: string;
}

/**
 * 形式検証結果
 * REQ-SEC2-FIX-002 準拠
 */
export interface VerificationResult {
  /** 検証成功 */
  verified: boolean;
  
  /** 反例（検証失敗時） */
  counterExample?: {
    input: string;
    expectedBehavior: string;
    actualBehavior: string;
  };
  
  /** 証明（検証成功時） */
  proof?: {
    strategy: string;
    steps: string[];
  };
  
  /** タイムアウト発生 */
  timeout: boolean;
  
  /** 検証時間(ms) */
  duration: number;
}

/**
 * テストケース
 * REQ-SEC2-FIX-003 準拠
 */
export interface TestCase {
  id: string;
  name: string;
  description: string;
  type: 'regression' | 'positive' | 'edge-case';
  input: unknown;
  expectedOutput: unknown;
  assertions: Assertion[];
}

export interface Assertion {
  type: 'equals' | 'throws' | 'notThrows' | 'contains' | 'matches';
  expected: unknown;
  message?: string;
}
```

---

#### 2.1.6 Config型

**ファイル**: `src/types/config.ts`

```typescript
// DES-SEC2-TYPE-006: 設定の型定義

/**
 * セキュリティ設定
 * REQ-SEC2-CFG-001 準拠
 */
export interface SecurityConfig {
  /** バージョン */
  version: '2.0';
  
  /** スキャン設定 */
  scan: ScanConfig;
  
  /** テイント分析設定 */
  taint: TaintConfig;
  
  /** シークレット検出設定 */
  secrets: SecretsConfig;
  
  /** 依存関係監査設定 */
  dependencies: DependenciesConfig;
  
  /** コンテナスキャン設定 */
  container: ContainerConfig;
  
  /** IaCスキャン設定 */
  iac: IaCConfig;
  
  /** AI脆弱性検出設定 */
  ai: AIConfig;
  
  /** レポート設定 */
  report: ReportConfig;
  
  /** 統合設定 */
  integrations: IntegrationsConfig;
  
  /** ロギング設定 */
  logging: LoggingConfig;
}

export interface ScanConfig {
  /** 対象拡張子 */
  extensions: string[];
  
  /** 除外パターン */
  exclude: string[];
  
  /** 最小重大度 */
  minSeverity: Severity;
  
  /** 並列度 */
  parallelism: number;
  
  /** タイムアウト(ms) */
  timeout: number;
}

export interface TaintConfig {
  /** 有効化 */
  enabled: boolean;
  
  /** フレームワーク自動検出 */
  autoDetectFramework: boolean;
  
  /** カスタムソース定義 */
  customSources?: CustomTaintSource[];
  
  /** カスタムシンク定義 */
  customSinks?: CustomTaintSink[];
  
  /** カスタムサニタイザー定義 */
  customSanitizers?: CustomSanitizer[];
}

export interface SecretsConfig {
  /** 有効化 */
  enabled: boolean;
  
  /** Git履歴スキャン */
  scanGitHistory: boolean;
  
  /** エントロピー閾値 */
  entropyThreshold: number;
  
  /** 除外パターン */
  allowlist: string[];
}

export interface DependenciesConfig {
  /** 有効化 */
  enabled: boolean;
  
  /** データソース */
  dataSources: ('nvd' | 'osv' | 'github-advisory' | 'snyk')[];
  
  /** サプライチェーン分析 */
  supplyChainAnalysis: boolean;
  
  /** SBOM生成 */
  generateSBOM: boolean;
  
  /** SBOMフォーマット */
  sbomFormat: 'spdx' | 'cyclonedx';
}

export interface ContainerConfig {
  /** 有効化 */
  enabled: boolean;
  
  /** ベースイメージ更新チェック */
  checkBaseImageUpdates: boolean;
  
  /** Dockerfile lint */
  dockerfileLint: boolean;
}

export interface IaCConfig {
  /** 有効化 */
  enabled: boolean;
  
  /** 対象プラットフォーム */
  platforms: ('terraform' | 'kubernetes' | 'cloudformation')[];
  
  /** ベンチマーク */
  benchmarks: ('cis' | 'soc2' | 'pci-dss')[];
}

export interface AIConfig {
  /** 有効化 */
  enabled: boolean;
  
  /** プロンプトインジェクション検出 */
  promptInjection: boolean;
  
  /** 出力検証チェック */
  outputValidation: boolean;
}

export interface ReportConfig {
  /** 出力形式 */
  formats: ('json' | 'sarif' | 'html' | 'pdf')[];
  
  /** 出力ディレクトリ */
  outputDir: string;
  
  /** 詳細レベル */
  detailLevel: 'summary' | 'standard' | 'detailed';
}

export interface IntegrationsConfig {
  /** CI/CD統合 */
  cicd: {
    failOnSeverity?: Severity;
    annotations: boolean;
  };
  
  /** YATA統合 */
  yata: {
    enabled: boolean;
    endpoint?: string;
  };
  
  /** LLM統合 */
  llm: {
    provider: 'openai' | 'anthropic' | 'azure-openai';
    model?: string;
    apiKey?: string;
  };
}

export interface LoggingConfig {
  /** ログレベル */
  level: 'debug' | 'info' | 'warn' | 'error';
  
  /** 監査ログ有効化 */
  auditLog: boolean;
  
  /** 監査ログ出力先 */
  auditLogPath?: string;
}
```

---

### 2.2 Core Service Classes

#### 2.2.1 SecurityService

**ファイル**: `src/core/security-service.ts`

```typescript
// DES-SEC2-ORCH-001: SecurityService実装

import { Result, ok, err } from 'neverthrow';
import { Vulnerability, ScanResult, TaintResult, SecretResult, AuditResult, Fix, Report } from '../types';
import { PipelineManager } from './pipeline-manager';
import { ResultAggregator } from './result-aggregator';
import { VulnerabilityScanner } from '../analyzers/sast/vulnerability-scanner';
import { TaintTracker } from '../analyzers/taint/taint-tracker';
import { SecretDetector } from '../analyzers/secrets/secret-detector';
import { DependencyAuditor } from '../analyzers/dependency/dependency-auditor';
import { NeuroSymbolicCore } from '../intelligence/neuro-symbolic-core';
import { FixGenerator } from '../fix/fix-generator';
import { ReportGenerator } from '../report/report-generator';

/**
 * スキャンオプション
 */
export interface ScanOptions {
  path: string;
  incremental?: boolean;
  minSeverity?: Severity;
  analyzers?: ('sast' | 'taint' | 'secret' | 'dependency' | 'container' | 'iac' | 'ai')[];
  config?: Partial<SecurityConfig>;
}

/**
 * SecurityService
 * セキュリティ分析のエントリーポイント
 * 
 * トレーサビリティ: REQ-SEC2-CLI-001, REQ-SEC2-INT-003
 */
export class SecurityService {
  private readonly pipelineManager: PipelineManager;
  private readonly resultAggregator: ResultAggregator;
  private readonly vulnScanner: VulnerabilityScanner;
  private readonly taintTracker: TaintTracker;
  private readonly secretDetector: SecretDetector;
  private readonly depAuditor: DependencyAuditor;
  private readonly neuroSymbolic: NeuroSymbolicCore;
  private readonly fixGenerator: FixGenerator;
  private readonly reportGenerator: ReportGenerator;
  
  constructor(config: SecurityConfig) {
    // DI initialization
    this.pipelineManager = new PipelineManager(config);
    this.resultAggregator = new ResultAggregator();
    this.vulnScanner = new VulnerabilityScanner(config.scan);
    this.taintTracker = new TaintTracker(config.taint);
    this.secretDetector = new SecretDetector(config.secrets);
    this.depAuditor = new DependencyAuditor(config.dependencies);
    this.neuroSymbolic = new NeuroSymbolicCore(config.integrations);
    this.fixGenerator = new FixGenerator(this.neuroSymbolic);
    this.reportGenerator = new ReportGenerator(config.report);
  }
  
  /**
   * 脆弱性スキャン実行
   */
  async scan(options: ScanOptions): Promise<Result<ScanResult, Error>> {
    const analyzers = options.analyzers ?? ['sast', 'taint', 'secret', 'dependency'];
    
    // パイプライン構築
    const pipeline = this.pipelineManager.createPipeline({
      stages: analyzers.map(analyzer => ({
        name: analyzer,
        analyzer: this.getAnalyzer(analyzer),
        options: { path: options.path, ...options.config },
      })),
    });
    
    // 並列実行
    const results = await this.pipelineManager.executeParallel([pipeline]);
    
    // 結果集約
    const aggregated = this.resultAggregator.aggregate(results);
    
    // Neuro-Symbolic強化（P0要件）
    const enhanced = await this.enhanceWithNeuroSymbolic(aggregated.vulnerabilities);
    
    return ok({
      vulnerabilities: enhanced,
      summary: aggregated.summary,
      duration: aggregated.duration,
    });
  }
  
  /**
   * テイント分析実行
   */
  async analyzeTaint(path: string): Promise<Result<TaintResult, Error>> {
    return this.taintTracker.analyze(path);
  }
  
  /**
   * シークレット検出実行
   */
  async detectSecrets(path: string): Promise<Result<SecretResult, Error>> {
    return this.secretDetector.detect(path);
  }
  
  /**
   * 依存関係監査実行
   */
  async auditDependencies(packageFile: string): Promise<Result<AuditResult, Error>> {
    return this.depAuditor.audit(packageFile);
  }
  
  /**
   * 自動修正生成
   * REQ-SEC2-FIX-001 準拠
   */
  async generateFix(vulnerability: Vulnerability): Promise<Result<Fix[], Error>> {
    return this.fixGenerator.generate(vulnerability);
  }
  
  /**
   * レポート生成
   * REQ-SEC2-REPORT-001 準拠
   */
  async generateReport(
    results: ScanResult,
    format: 'json' | 'sarif' | 'html' | 'pdf'
  ): Promise<Result<Report, Error>> {
    return this.reportGenerator.generate(results, format);
  }
  
  /**
   * Neuro-Symbolic強化
   * REQ-SEC2-SAST-002 準拠
   */
  private async enhanceWithNeuroSymbolic(
    vulnerabilities: Vulnerability[]
  ): Promise<Vulnerability[]> {
    return Promise.all(
      vulnerabilities.map(async vuln => {
        const nsResult = await this.neuroSymbolic.analyze(vuln);
        return {
          ...vuln,
          neuroSymbolicResult: nsResult,
          confidence: nsResult.finalDecision === 'confirmed' 
            ? Math.max(vuln.confidence, nsResult.neuralConfidence)
            : vuln.confidence * 0.5,
        };
      })
    );
  }
  
  private getAnalyzer(type: string): Analyzer {
    switch (type) {
      case 'sast': return this.vulnScanner;
      case 'taint': return this.taintTracker;
      case 'secret': return this.secretDetector;
      case 'dependency': return this.depAuditor;
      default: throw new Error(`Unknown analyzer: ${type}`);
    }
  }
}
```

---

#### 2.2.2 NeuroSymbolicCore

**ファイル**: `src/intelligence/neuro-symbolic-core.ts`

```typescript
// DES-SEC2-SAST-002: NeuroSymbolicCore実装

import { Vulnerability, NeuroSymbolicResult, Evidence } from '../types';
import { LLMAnalyzer } from './llm-analyzer';
import { KnowledgeQuery } from './knowledge-query';

/**
 * NeuroSymbolicCore
 * LLM（Neural）と知識グラフ（Symbolic）の統合推論
 * 
 * 信頼度統合ルール（REQ-INT-002準拠）:
 * | シンボリック結果 | ニューラル信頼度 | 最終決定       |
 * |-----------------|-----------------|---------------|
 * | invalid         | -               | rejected      |
 * | valid           | ≥0.8            | confirmed     |
 * | valid           | <0.8            | needs-review  |
 * 
 * トレーサビリティ: REQ-SEC2-SAST-002
 */
export class NeuroSymbolicCore {
  private readonly llmAnalyzer: LLMAnalyzer;
  private readonly knowledgeQuery: KnowledgeQuery;
  
  // 信頼度閾値（REQ-INT-002より）
  private readonly CONFIDENCE_THRESHOLD = 0.8;
  
  constructor(config: IntegrationsConfig) {
    this.llmAnalyzer = new LLMAnalyzer(config.llm);
    this.knowledgeQuery = new KnowledgeQuery(config.yata);
  }
  
  /**
   * 統合分析実行
   */
  async analyze(vulnerability: Vulnerability): Promise<NeuroSymbolicResult> {
    // 1. シンボリック検証（知識グラフ）
    const symbolicResult = await this.symbolicVerify(vulnerability);
    
    // 2. シンボリックが無効なら即座に棄却
    if (!symbolicResult.valid) {
      return {
        neuralConfidence: 0,
        symbolicValid: false,
        finalDecision: 'rejected',
        neuralExplanation: '',
        symbolicEvidence: symbolicResult.evidence,
      };
    }
    
    // 3. ニューラル分析（LLM）
    const neuralResult = await this.neuralAnalyze(vulnerability);
    
    // 4. 信頼度統合
    const finalDecision = this.integrateConfidence(
      neuralResult.confidence,
      symbolicResult.valid
    );
    
    return {
      neuralConfidence: neuralResult.confidence,
      symbolicValid: symbolicResult.valid,
      finalDecision,
      neuralExplanation: neuralResult.explanation,
      symbolicEvidence: symbolicResult.evidence,
    };
  }
  
  /**
   * シンボリック検証
   * YATA知識グラフを使用
   */
  private async symbolicVerify(
    vulnerability: Vulnerability
  ): Promise<{ valid: boolean; evidence: Evidence[] }> {
    // パターンマッチング
    const patterns = await this.knowledgeQuery.queryPattern({
      cwes: vulnerability.cwes,
      codePattern: vulnerability.codeSnippet,
    });
    
    // ルール推論
    const rules = await this.knowledgeQuery.matchRule(
      vulnerability.codeSnippet,
      this.detectLanguage(vulnerability.location.filePath)
    );
    
    const evidence: Evidence[] = [
      ...patterns.map(p => ({
        type: 'pattern-match' as const,
        source: p.id,
        description: p.description,
      })),
      ...rules.map(r => ({
        type: 'rule-inference' as const,
        source: r.id,
        description: r.description,
      })),
    ];
    
    // パターンまたはルールが存在すれば有効
    const valid = patterns.length > 0 || rules.length > 0;
    
    return { valid, evidence };
  }
  
  /**
   * ニューラル分析
   * LLMを使用したコンテキスト分析
   */
  private async neuralAnalyze(
    vulnerability: Vulnerability
  ): Promise<{ confidence: number; explanation: string }> {
    const prompt = this.buildAnalysisPrompt(vulnerability);
    const response = await this.llmAnalyzer.analyzeContext(prompt);
    
    return {
      confidence: response.confidence,
      explanation: response.explanation,
    };
  }
  
  /**
   * 信頼度統合
   * REQ-INT-002の決定ルールを適用
   */
  private integrateConfidence(
    neuralConfidence: number,
    symbolicValid: boolean
  ): 'confirmed' | 'rejected' | 'needs-review' {
    // シンボリックが無効なら棄却
    if (!symbolicValid) {
      return 'rejected';
    }
    
    // ニューラル信頼度が閾値以上なら確定
    if (neuralConfidence >= this.CONFIDENCE_THRESHOLD) {
      return 'confirmed';
    }
    
    // それ以外はレビュー必要
    return 'needs-review';
  }
  
  private buildAnalysisPrompt(vulnerability: Vulnerability): string {
    return `
Analyze the following potential security vulnerability:

**Title**: ${vulnerability.title}
**CWE**: ${vulnerability.cwes.join(', ')}
**Severity**: ${vulnerability.severity}
**Code**:
\`\`\`
${vulnerability.codeSnippet}
\`\`\`

Please assess:
1. Is this a true positive vulnerability?
2. What is the potential impact?
3. How confident are you in this assessment (0.0-1.0)?

Respond in JSON format: { "isVulnerable": boolean, "impact": string, "confidence": number, "explanation": string }
    `.trim();
  }
  
  private detectLanguage(filePath: string): string {
    const ext = filePath.split('.').pop()?.toLowerCase();
    const langMap: Record<string, string> = {
      ts: 'typescript',
      tsx: 'typescript',
      js: 'javascript',
      jsx: 'javascript',
      py: 'python',
      java: 'java',
      go: 'go',
      rs: 'rust',
    };
    return langMap[ext ?? ''] ?? 'unknown';
  }
}
```

---

### 2.3 Analyzer Classes

#### 2.3.1 VulnerabilityScanner

**ファイル**: `src/analyzers/sast/vulnerability-scanner.ts`

```typescript
// DES-SEC2-SAST-001: VulnerabilityScanner実装

import { Project, SourceFile } from 'ts-morph';
import { Result, ok, err } from 'neverthrow';
import { Vulnerability, ScanConfig, SecurityRule } from '../../types';
import { SQLInjectionDetector } from './detectors/sql-injection';
import { XSSDetector } from './detectors/xss';
import { PathTraversalDetector } from './detectors/path-traversal';
import { CommandInjectionDetector } from './detectors/command-injection';

/**
 * セキュリティ検出器のインターフェース
 */
export interface SecurityDetector {
  readonly id: string;
  readonly cwes: string[];
  detect(sourceFile: SourceFile): Vulnerability[];
}

/**
 * VulnerabilityScanner
 * 静的解析による脆弱性検出
 * 
 * トレーサビリティ: REQ-SEC2-SAST-001
 */
export class VulnerabilityScanner {
  private readonly project: Project;
  private readonly config: ScanConfig;
  private readonly detectors: SecurityDetector[] = [];
  private readonly customRules: SecurityRule[] = [];
  
  constructor(config: ScanConfig) {
    this.config = config;
    this.project = new Project({
      tsConfigFilePath: 'tsconfig.json',
      skipAddingFilesFromTsConfig: true,
    });
    
    // 組み込み検出器の登録
    this.registerBuiltinDetectors();
  }
  
  /**
   * ファイルスキャン
   */
  async scanFile(filePath: string): Promise<Result<Vulnerability[], Error>> {
    try {
      const sourceFile = this.project.addSourceFileAtPath(filePath);
      const vulnerabilities: Vulnerability[] = [];
      
      // 全検出器で検査
      for (const detector of this.detectors) {
        const detected = detector.detect(sourceFile);
        vulnerabilities.push(...detected);
      }
      
      // カスタムルールで検査
      for (const rule of this.customRules) {
        const detected = this.applyCustomRule(sourceFile, rule);
        vulnerabilities.push(...detected);
      }
      
      return ok(vulnerabilities);
    } catch (error) {
      return err(error instanceof Error ? error : new Error(String(error)));
    }
  }
  
  /**
   * ディレクトリスキャン
   */
  async scanDirectory(path: string): Promise<Result<Vulnerability[], Error>> {
    const glob = this.buildGlobPattern(path);
    const files = this.project.addSourceFilesAtPaths(glob);
    
    const allVulnerabilities: Vulnerability[] = [];
    
    // 並列実行（config.parallelismに従う）
    const chunks = this.chunkArray(files, this.config.parallelism);
    
    for (const chunk of chunks) {
      const results = await Promise.all(
        chunk.map(file => this.scanSourceFile(file))
      );
      
      results.forEach(result => {
        if (result.isOk()) {
          allVulnerabilities.push(...result.value);
        }
      });
    }
    
    return ok(allVulnerabilities);
  }
  
  /**
   * インクリメンタルスキャン
   * 変更されたファイルのみスキャン
   */
  async scanIncremental(changedFiles: string[]): Promise<Result<Vulnerability[], Error>> {
    const vulnerabilities: Vulnerability[] = [];
    
    for (const filePath of changedFiles) {
      const result = await this.scanFile(filePath);
      if (result.isOk()) {
        vulnerabilities.push(...result.value);
      }
    }
    
    return ok(vulnerabilities);
  }
  
  /**
   * カスタムルールの追加
   */
  addRule(rule: SecurityRule): void {
    this.customRules.push(rule);
  }
  
  /**
   * 検出器の追加
   */
  addDetector(detector: SecurityDetector): void {
    this.detectors.push(detector);
  }
  
  private registerBuiltinDetectors(): void {
    this.detectors.push(
      new SQLInjectionDetector(),
      new XSSDetector(),
      new PathTraversalDetector(),
      new CommandInjectionDetector(),
    );
  }
  
  private async scanSourceFile(sourceFile: SourceFile): Promise<Result<Vulnerability[], Error>> {
    const vulnerabilities: Vulnerability[] = [];
    
    for (const detector of this.detectors) {
      const detected = detector.detect(sourceFile);
      vulnerabilities.push(...detected);
    }
    
    return ok(vulnerabilities);
  }
  
  private applyCustomRule(sourceFile: SourceFile, rule: SecurityRule): Vulnerability[] {
    // カスタムルールのパターンマッチング実装
    // ...
    return [];
  }
  
  private buildGlobPattern(path: string): string {
    const extensions = this.config.extensions.join(',');
    return `${path}/**/*.{${extensions}}`;
  }
  
  private chunkArray<T>(array: T[], size: number): T[][] {
    const chunks: T[][] = [];
    for (let i = 0; i < array.length; i += size) {
      chunks.push(array.slice(i, i + size));
    }
    return chunks;
  }
}
```

---

## 3. CLI実装

### 3.1 CLI Entry Point

**ファイル**: `src/cli/index.ts`

```typescript
#!/usr/bin/env node
// DES-SEC2-CLI-001: CLI実装

import { Command } from 'commander';
import { scanCommand } from './commands/scan';
import { taintCommand } from './commands/taint';
import { secretsCommand } from './commands/secrets';
import { auditCommand } from './commands/audit';
import { fixCommand } from './commands/fix';
import { reportCommand } from './commands/report';
import { containerCommand } from './commands/container';
import { iacCommand } from './commands/iac';
import { configCommand } from './commands/config';

const program = new Command();

program
  .name('musubix-security')
  .description('MUSUBIX Security - Neuro-Symbolic Security Analysis')
  .version('2.0.0');

// REQ-SEC2-CLI-001: 標準コマンド
program.addCommand(scanCommand);      // scan <path>
program.addCommand(taintCommand);     // taint <path>
program.addCommand(secretsCommand);   // secrets <path>
program.addCommand(auditCommand);     // audit <path>
program.addCommand(fixCommand);       // fix <vuln-id>
program.addCommand(reportCommand);    // report <path>
program.addCommand(containerCommand); // container <image>
program.addCommand(iacCommand);       // iac <path>
program.addCommand(configCommand);    // config init/validate

// REQ-SEC2-CLI-002: ヘルプとエラーコード
program.exitOverride((err) => {
  if (err.code === 'commander.help') {
    process.exit(0);
  }
  process.exit(1);
});

program.parse(process.argv);
```

---

### 3.2 Scan Command

**ファイル**: `src/cli/commands/scan.ts`

```typescript
// DES-SEC2-CLI-001: scan コマンド実装

import { Command } from 'commander';
import { SecurityService } from '../../core/security-service';
import { loadConfig } from '../../infrastructure/config-manager';
import { formatOutput } from '../formatters';

export const scanCommand = new Command('scan')
  .description('Scan for security vulnerabilities')
  .argument('<path>', 'Path to scan')
  .option('-f, --format <format>', 'Output format (json, sarif, table)', 'table')
  .option('-s, --severity <severity>', 'Minimum severity (critical, high, medium, low)', 'low')
  .option('-c, --config <file>', 'Config file path')
  .option('-o, --output <file>', 'Output file')
  .option('--incremental', 'Incremental scan (changed files only)')
  .option('--analyzers <list>', 'Comma-separated analyzers to run', 'sast,taint,secret,dependency')
  .action(async (path, options) => {
    try {
      const config = await loadConfig(options.config);
      const service = new SecurityService(config);
      
      const result = await service.scan({
        path,
        incremental: options.incremental,
        minSeverity: options.severity,
        analyzers: options.analyzers.split(','),
      });
      
      if (result.isErr()) {
        console.error('Scan failed:', result.error.message);
        process.exit(1);
      }
      
      const output = formatOutput(result.value, options.format);
      
      if (options.output) {
        await writeFile(options.output, output);
      } else {
        console.log(output);
      }
      
      // CI/CD統合: 重大な脆弱性があれば終了コード1
      const criticalCount = result.value.vulnerabilities
        .filter(v => v.severity === 'critical' || v.severity === 'high')
        .length;
      
      if (criticalCount > 0 && config.integrations.cicd.failOnSeverity) {
        process.exit(1);
      }
      
      process.exit(0);
    } catch (error) {
      console.error('Error:', error);
      process.exit(1);
    }
  });
```

---

## 4. テスト構造

### 4.1 テストファイル構造

```
tests/
├── unit/
│   ├── analyzers/
│   │   ├── vulnerability-scanner.test.ts
│   │   ├── taint-tracker.test.ts
│   │   ├── secret-detector.test.ts
│   │   └── dependency-auditor.test.ts
│   ├── intelligence/
│   │   └── neuro-symbolic-core.test.ts
│   ├── fix/
│   │   ├── fix-generator.test.ts
│   │   └── z3-verifier.test.ts
│   └── core/
│       └── security-service.test.ts
│
├── integration/
│   ├── cli.test.ts
│   ├── mcp-server.test.ts
│   └── full-scan.test.ts
│
└── fixtures/
    ├── vulnerable-code/
    │   ├── sql-injection.ts
    │   ├── xss.ts
    │   ├── path-traversal.ts
    │   └── command-injection.ts
    ├── safe-code/
    │   └── sanitized-input.ts
    └── configs/
        └── test-config.yaml
```

### 4.2 テスト例

**ファイル**: `tests/unit/intelligence/neuro-symbolic-core.test.ts`

```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NeuroSymbolicCore } from '../../../src/intelligence/neuro-symbolic-core';
import { Vulnerability } from '../../../src/types';

describe('NeuroSymbolicCore', () => {
  let core: NeuroSymbolicCore;
  
  beforeEach(() => {
    core = new NeuroSymbolicCore({
      yata: { enabled: true },
      llm: { provider: 'openai' },
    });
  });
  
  describe('analyze', () => {
    it('should reject when symbolic verification fails', async () => {
      // REQ-INT-002: シンボリックが無効なら棄却
      const vuln = createMockVulnerability();
      vi.spyOn(core as any, 'symbolicVerify').mockResolvedValue({
        valid: false,
        evidence: [],
      });
      
      const result = await core.analyze(vuln);
      
      expect(result.finalDecision).toBe('rejected');
      expect(result.symbolicValid).toBe(false);
    });
    
    it('should confirm when symbolic valid and neural confidence >= 0.8', async () => {
      // REQ-INT-002: シンボリック有効かつニューラル信頼度>=0.8なら確定
      const vuln = createMockVulnerability();
      vi.spyOn(core as any, 'symbolicVerify').mockResolvedValue({
        valid: true,
        evidence: [{ type: 'pattern-match', source: 'P1', description: 'test' }],
      });
      vi.spyOn(core as any, 'neuralAnalyze').mockResolvedValue({
        confidence: 0.85,
        explanation: 'High confidence vulnerability',
      });
      
      const result = await core.analyze(vuln);
      
      expect(result.finalDecision).toBe('confirmed');
      expect(result.symbolicValid).toBe(true);
      expect(result.neuralConfidence).toBeGreaterThanOrEqual(0.8);
    });
    
    it('should mark needs-review when symbolic valid but neural confidence < 0.8', async () => {
      // REQ-INT-002: シンボリック有効だがニューラル信頼度<0.8ならレビュー必要
      const vuln = createMockVulnerability();
      vi.spyOn(core as any, 'symbolicVerify').mockResolvedValue({
        valid: true,
        evidence: [],
      });
      vi.spyOn(core as any, 'neuralAnalyze').mockResolvedValue({
        confidence: 0.6,
        explanation: 'Uncertain vulnerability',
      });
      
      const result = await core.analyze(vuln);
      
      expect(result.finalDecision).toBe('needs-review');
      expect(result.neuralConfidence).toBeLessThan(0.8);
    });
  });
});

function createMockVulnerability(): Vulnerability {
  return {
    id: 'VULN-001',
    title: 'SQL Injection',
    description: 'Test vulnerability',
    severity: 'high',
    cvssScore: 8.0,
    confidence: 0.9,
    cwes: ['CWE-89'],
    source: 'sast',
    location: {
      filePath: 'test.ts',
      startLine: 10,
      endLine: 15,
    },
    codeSnippet: 'const query = `SELECT * FROM users WHERE id = ${id}`;',
    recommendation: 'Use parameterized queries',
    referenceUrls: [],
    createdAt: new Date(),
  };
}
```

---

## 5. トレーサビリティサマリー

| 設計ID | ファイル | 要件ID |
|--------|---------|--------|
| DES-SEC2-TYPE-001 | src/types/vulnerability.ts | REQ-SEC2-SAST-001 |
| DES-SEC2-TYPE-002 | src/types/taint.ts | REQ-SEC2-TAINT-001, REQ-SEC2-TAINT-002, REQ-SEC2-TAINT-003 |
| DES-SEC2-TYPE-003 | src/types/secret.ts | REQ-SEC2-SECRET-001, REQ-SEC2-SECRET-002, REQ-SEC2-SECRET-003 |
| DES-SEC2-TYPE-004 | src/types/dependency.ts | REQ-SEC2-DEP-001〜003 |
| DES-SEC2-TYPE-005 | src/types/zero-day.ts | REQ-SEC2-SAST-003 |
| DES-SEC2-TYPE-006 | src/types/interprocedural.ts | REQ-SEC2-SAST-004 |
| DES-SEC2-TYPE-007 | src/types/fix.ts | REQ-SEC2-FIX-001〜003 |
| DES-SEC2-TYPE-008 | src/types/config.ts | REQ-SEC2-CFG-001 |
| DES-SEC2-ORCH-001 | src/core/security-service.ts | REQ-SEC2-CLI-001, REQ-SEC2-INT-003 |
| DES-SEC2-SAST-001 | src/analyzers/sast/vulnerability-scanner.ts | REQ-SEC2-SAST-001 |
| DES-SEC2-SAST-002 | src/intelligence/neuro-symbolic-core.ts | REQ-SEC2-SAST-002 |
| DES-SEC2-SAST-003 | src/analyzers/sast/zero-day-detector.ts | REQ-SEC2-SAST-003 |
| DES-SEC2-SAST-004 | src/analyzers/sast/interprocedural-analyzer.ts | REQ-SEC2-SAST-004 |
| DES-SEC2-TAINT-003 | src/analyzers/taint/sanitizer-verifier.ts | REQ-SEC2-TAINT-003 |
| DES-SEC2-SECRET-003 | src/analyzers/secrets/pre-commit-hook.ts | REQ-SEC2-SECRET-003 |
| DES-SEC2-CLI-001 | src/cli/index.ts | REQ-SEC2-CLI-001, REQ-SEC2-CLI-002 |

---

## 6. 改訂履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 0.1.0 | 2026-01-07 | 初版作成（全コード設計） | AI Agent |
| 0.2.0 | 2026-01-07 | レビュー指摘対応: SAST-003/004, TAINT-003, SECRET-003の型定義追加 | AI Agent |

