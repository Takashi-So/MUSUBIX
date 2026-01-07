# MUSUBIX Security v2.0 コンポーネント設計書

**プロジェクト**: MUSUBIX Security Subsystem
**バージョン**: 2.0.0
**ステータス**: Draft
**作成日**: 2026-01-07
**関連ドキュメント**: 
- [アーキテクチャ設計書](DES-SEC2-architecture.md)
- [要件定義書](../specs/REQ-SEC-v2.0.md)

---

## 1. C4 Level 3: コンポーネント図

### 1.1 Security Engine コンポーネント

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Security Engine                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                    Orchestration Layer                               │   │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐  │   │
│  │  │  SecurityService │  │  PipelineManager │  │  ResultAggregator│  │   │
│  │  │                  │  │                  │  │                  │  │   │
│  │  │ • scan()         │  │ • createPipeline │  │ • aggregate()    │  │   │
│  │  │ • fix()          │  │ • execute()      │  │ • deduplicate()  │  │   │
│  │  │ • report()       │  │ • parallel()     │  │ • prioritize()   │  │   │
│  │  └────────┬─────────┘  └────────┬─────────┘  └────────┬─────────┘  │   │
│  └───────────┼──────────────────────┼──────────────────────┼───────────┘   │
│              │                      │                      │               │
│  ┌───────────▼──────────────────────▼──────────────────────▼───────────┐   │
│  │                      Analysis Layer                                  │   │
│  │                                                                      │   │
│  │  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐       │   │
│  │  │Vulnerability│ │TaintTracker│ │SecretDet-  │ │Dependency  │       │   │
│  │  │Scanner     │ │            │ │ector       │ │Auditor     │       │   │
│  │  │• scanFile()│ │• analyze() │ │• detect()  │ │• audit()   │       │   │
│  │  │• scanDir() │ │• track()   │ │• classify()│ │• checkCVE()│       │   │
│  │  └────────────┘ └────────────┘ └────────────┘ └────────────┘       │   │
│  │                                                                      │   │
│  │  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐       │   │
│  │  │ImageScanner│ │IaCChecker  │ │PromptInj-  │ │Compliance  │       │   │
│  │  │            │ │            │ │Detector    │ │Validator   │       │   │
│  │  │• scanImage│ │• analyze() │ │• detect()  │ │• validate()│       │   │
│  │  │• scanDocker││• benchmark()│ │• classify()│ │• report()  │       │   │
│  │  └────────────┘ └────────────┘ └────────────┘ └────────────┘       │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                     │                                      │
│  ┌──────────────────────────────────▼──────────────────────────────────┐   │
│  │                    Intelligence Layer                                │   │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐  │   │
│  │  │NeuroSymbolicCore │  │  LLMAnalyzer     │  │  KnowledgeQuery  │  │   │
│  │  │                  │  │                  │  │                  │  │   │
│  │  │• integrate()     │  │• analyzeContext()│  │• queryPattern()  │  │   │
│  │  │• validate()      │  │• generateExplan()│  │• matchRule()     │  │   │
│  │  │• score()         │  │• suggestFix()    │  │• inferVuln()     │  │   │
│  │  └──────────────────┘  └──────────────────┘  └──────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                     │                                      │
│  ┌──────────────────────────────────▼──────────────────────────────────┐   │
│  │                       Fix Layer                                      │   │
│  │  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐  │   │
│  │  │  FixGenerator    │  │  Z3Verifier      │  │  TestGenerator   │  │   │
│  │  │                  │  │                  │  │                  │  │   │
│  │  │• generate()      │  │• verify()        │  │• generateTest()  │  │   │
│  │  │• rank()          │  │• checkInvariant()│  │• regression()    │  │   │
│  │  │• apply()         │  │• proveSafe()     │  │• edgeCase()      │  │   │
│  │  └──────────────────┘  └──────────────────┘  └──────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. コンポーネント詳細設計

### 2.1 Orchestration Layer

#### DES-SEC2-ORCH-001: SecurityService

**責務**: セキュリティ分析のエントリーポイント、全体オーケストレーション

**インターフェース**:
```typescript
interface SecurityService {
  // 脆弱性スキャン
  scan(options: ScanOptions): Promise<ScanResult>;
  
  // テイント分析
  analyzeTaint(options: TaintOptions): Promise<TaintResult>;
  
  // シークレット検出
  detectSecrets(options: SecretOptions): Promise<SecretResult>;
  
  // 依存関係監査
  auditDependencies(options: AuditOptions): Promise<AuditResult>;
  
  // 自動修正
  generateFix(vulnerability: Vulnerability): Promise<Fix[]>;
  
  // レポート生成
  generateReport(results: AnalysisResult[], format: ReportFormat): Promise<Report>;
}
```

**依存関係**:
- PipelineManager
- ResultAggregator
- All Analyzers

**トレーサビリティ**: REQ-SEC2-CLI-001, REQ-SEC2-INT-003

---

#### DES-SEC2-ORCH-002: PipelineManager

**責務**: 解析パイプラインの構築と実行管理

**インターフェース**:
```typescript
interface PipelineManager {
  // パイプライン作成
  createPipeline(config: PipelineConfig): Pipeline;
  
  // 並列実行
  executeParallel(pipelines: Pipeline[]): Promise<PipelineResult[]>;
  
  // 順次実行
  executeSequential(pipeline: Pipeline): Promise<PipelineResult>;
  
  // キャンセル
  cancel(pipelineId: string): void;
}

interface Pipeline {
  stages: PipelineStage[];
  onProgress?: (progress: Progress) => void;
  timeout?: number;
}

interface PipelineStage {
  name: string;
  analyzer: Analyzer;
  options: AnalyzerOptions;
  dependsOn?: string[];
}
```

**設計パターン**: Pipeline & Filters Pattern

**トレーサビリティ**: REQ-SEC2-PERF-001

---

#### DES-SEC2-ORCH-003: ResultAggregator

**責務**: 複数アナライザーの結果を集約・重複排除・優先度付け

**インターフェース**:
```typescript
interface ResultAggregator {
  // 結果集約
  aggregate(results: AnalysisResult[]): AggregatedResult;
  
  // 重複排除
  deduplicate(vulnerabilities: Vulnerability[]): Vulnerability[];
  
  // 優先度付け
  prioritize(vulnerabilities: Vulnerability[]): Vulnerability[];
  
  // リスクスコア計算
  calculateRiskScore(vulnerabilities: Vulnerability[]): number;
}
```

**アルゴリズム**:
- 重複判定: 同一ファイル・行範囲・CWEの組み合わせ
- 優先度: CVSS × 信頼度 × 影響範囲

**トレーサビリティ**: REQ-SEC2-REPORT-001

---

### 2.2 Analysis Layer

#### DES-SEC2-SAST-001: VulnerabilityScanner

**責務**: 静的解析による脆弱性検出

**インターフェース**:
```typescript
interface VulnerabilityScanner {
  // ファイルスキャン
  scanFile(file: SourceFile, options: ScanOptions): Promise<Vulnerability[]>;
  
  // ディレクトリスキャン
  scanDirectory(path: string, options: ScanOptions): Promise<ScanResult>;
  
  // インクリメンタルスキャン
  scanIncremental(changes: FileChange[]): Promise<Vulnerability[]>;
  
  // ルール追加
  addRule(rule: SecurityRule): void;
}

interface SecurityRule {
  id: string;
  name: string;
  severity: Severity;
  cwes: string[];
  pattern: RulePattern;
  message: string;
  recommendation: string;
}
```

**検出器**:
| 検出器 | CWE | 説明 |
|--------|-----|------|
| SQLInjectionDetector | CWE-89 | SQLインジェクション |
| XSSDetector | CWE-79 | クロスサイトスクリプティング |
| PathTraversalDetector | CWE-22 | パストラバーサル |
| CommandInjectionDetector | CWE-78 | コマンドインジェクション |
| InsecureDeserializationDetector | CWE-502 | 安全でないデシリアライズ |
| SSRFDetector | CWE-918 | サーバーサイドリクエストフォージェリ |

**トレーサビリティ**: REQ-SEC2-SAST-001

---

#### DES-SEC2-SAST-003: ZeroDayDetector

**責務**: 知識グラフのセキュアコーディングパターンからの逸脱分析によるゼロデイ検出

**インターフェース**:
```typescript
interface ZeroDayDetector {
  // ゼロデイ脆弱性検出
  detect(sourceFile: SourceFile, knownPatterns: SecurityPattern[]): Promise<ZeroDayCandidate[]>;
  
  // パターン逸脱分析
  analyzeDeviation(code: AST.Node, patterns: SecurityPattern[]): DeviationResult;
  
  // リスク評価
  assessRisk(candidate: ZeroDayCandidate): RiskAssessment;
  
  // LLM支援分析
  analyzewithLLM(candidate: ZeroDayCandidate): Promise<LLMAnalysisResult>;
  
  // 専門家レビュー用フラグ付け
  flagForReview(candidate: ZeroDayCandidate): ReviewRequest;
}

interface ZeroDayCandidate {
  id: string;
  location: SourceLocation;
  codeSnippet: string;
  deviationType: 'pattern-mismatch' | 'anomaly' | 'unsafe-practice';
  confidence: number;  // 0.0-1.0
  llmAssessment?: LLMAnalysisResult;
  severity: 'potential';  // ゼロデイは常にpotential
  explanation: string;
}

interface RiskAssessment {
  score: number;  // 0-100
  factors: RiskFactor[];
  recommendation: 'review' | 'investigate' | 'safe';
}
```

**検出アルゴリズム**:
1. 知識グラフからセキュアパターンを取得
2. コードがパターンに準拠しているか検証
3. 準拠しない箇所をLLMで分析
4. 信頼度スコア付きで候補を出力
5. 誤検出率20%以下を目標

**トレーサビリティ**: REQ-SEC2-SAST-003

---

#### DES-SEC2-SAST-004: InterproceduralAnalyzer

**責務**: 関数・モジュール境界を越えたデータフロー解析

**インターフェース**:
```typescript
interface InterproceduralAnalyzer {
  // インタープロシージャ解析
  analyze(entryPoint: AST.FunctionDeclaration, maxDepth?: number): Promise<InterproceduralResult>;
  
  // 呼び出しグラフ構築
  buildCallGraph(sourceFiles: SourceFile[]): CallGraph;
  
  // データフロー追跡（関数境界越え）
  trackDataFlow(variable: string, startLocation: SourceLocation): DataFlowPath[];
  
  // 循環呼び出し検出
  detectCycles(callGraph: CallGraph): CycleInfo[];
  
  // モジュール境界分析
  analyzeModuleBoundary(importNode: AST.ImportDeclaration): ModuleBoundaryInfo;
}

interface CallGraph {
  nodes: CallGraphNode[];
  edges: CallGraphEdge[];
  
  // クエリメソッド
  getCallers(functionId: string): CallGraphNode[];
  getCallees(functionId: string): CallGraphNode[];
  getPath(from: string, to: string): CallGraphNode[];
}

interface CallGraphNode {
  id: string;
  name: string;
  module: string;
  location: SourceLocation;
  parameters: ParameterInfo[];
  returnType?: string;
}

interface InterproceduralResult {
  callGraph: CallGraph;
  dataFlows: DataFlowPath[];
  cycles: CycleInfo[];
  maxDepthReached: boolean;
  analysisTime: number;
}
```

**解析制約**:
| パラメータ | デフォルト値 | 説明 |
|-----------|-------------|------|
| maxDepth | 20 | 最大呼び出し深度 |
| timeout | 30秒 | 解析タイムアウト |
| maxNodes | 10,000 | 最大ノード数 |

**トレーサビリティ**: REQ-SEC2-SAST-004

---

#### DES-SEC2-TAINT-001: TaintTracker

**責務**: データフロー追跡によるテイント分析

**インターフェース**:
```typescript
interface TaintTracker {
  // テイント分析
  analyze(sourceFile: SourceFile): Promise<TaintResult>;
  
  // ソース識別
  identifySources(ast: AST): TaintSource[];
  
  // シンク識別
  identifySinks(ast: AST): TaintSink[];
  
  // パス追跡
  trackPaths(source: TaintSource, sink: TaintSink): TaintPath[];
  
  // サニタイザー検証
  verifySanitizer(path: TaintPath, sanitizer: Sanitizer): boolean;
}

interface TaintSource {
  id: string;
  type: 'user-input' | 'file' | 'network' | 'database' | 'environment';
  location: SourceLocation;
  variable: string;
}

interface TaintSink {
  id: string;
  type: 'sql' | 'command' | 'file' | 'html' | 'url' | 'eval';
  location: SourceLocation;
  requiredSanitizers: string[];
}

interface TaintPath {
  source: TaintSource;
  sink: TaintSink;
  steps: TaintStep[];
  sanitizers: Sanitizer[];
  isSafe: boolean;
}
```

**フレームワークアダプター**:
| フレームワーク | アダプター |
|--------------|-----------|
| Express | ExpressTaintAdapter |
| Fastify | FastifyTaintAdapter |
| NestJS | NestJSTaintAdapter |
| Next.js | NextJSTaintAdapter |
| Koa | KoaTaintAdapter |

**トレーサビリティ**: REQ-SEC2-TAINT-001, REQ-SEC2-TAINT-002

---

#### DES-SEC2-TAINT-003: SanitizerVerifier

**責務**: サニタイザーの有効性検証（シンクコンテキストに対する適合性チェック）

**インターフェース**:
```typescript
interface SanitizerVerifier {
  // サニタイザー有効性検証
  verify(sanitizer: Sanitizer, sinkContext: SinkContext): VerificationResult;
  
  // 適合性マトリクスチェック
  checkCompatibility(sanitizerType: string, sinkType: string): boolean;
  
  // カスタムサニタイザー評価
  evaluateCustomSanitizer(sanitizerCode: AST.Node): SafetyAssessment;
  
  // 推奨サニタイザー取得
  getRecommendedSanitizer(sinkContext: SinkContext): SanitizerRecommendation;
}

interface SinkContext {
  sinkType: 'sql' | 'command' | 'file' | 'html' | 'url' | 'eval';
  framework?: string;
  database?: string;
  outputContext?: 'attribute' | 'element' | 'script' | 'style' | 'url';
}

interface VerificationResult {
  isEffective: boolean;
  reason: string;
  warnings: string[];
  recommendation?: SanitizerRecommendation;
}

interface SanitizerRecommendation {
  sanitizerName: string;
  example: string;
  documentation: string;
}
```

**サニタイザー-シンク適合性マトリクス**:
| サニタイザー | SQL | Command | HTML | URL | File | Eval |
|-------------|-----|---------|------|-----|------|------|
| SQL Parameterization | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ |
| HTML Encoding | ❌ | ❌ | ✅ | ❌ | ❌ | ❌ |
| URL Encoding | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ |
| Shell Escape | ❌ | ✅ | ❌ | ❌ | ❌ | ❌ |
| Path Sanitization | ❌ | ❌ | ❌ | ❌ | ✅ | ❌ |
| JSON Stringify | ❌ | ❌ | ⚠️ | ❌ | ❌ | ✅ |

**トレーサビリティ**: REQ-SEC2-TAINT-003

---

#### DES-SEC2-SECRET-001: SecretDetector

**責務**: シークレット（APIキー、トークン等）の検出

**インターフェース**:
```typescript
interface SecretDetector {
  // シークレット検出
  detect(content: string, filePath: string): Promise<Secret[]>;
  
  // Git履歴スキャン
  scanGitHistory(repoPath: string): Promise<Secret[]>;
  
  // エントロピー計算
  calculateEntropy(value: string): number;
  
  // 分類
  classify(secret: Secret): SecretClassification;
}

interface Secret {
  id: string;
  type: SecretType;
  value: string; // マスク済み
  location: SourceLocation;
  entropy: number;
  confidence: number;
  service?: string; // AWS, Azure, Stripe等
}

type SecretType = 
  | 'api-key'
  | 'oauth-token'
  | 'password'
  | 'private-key'
  | 'certificate'
  | 'connection-string'
  | 'jwt'
  | 'ssh-key';
```

**検出パターン**:
| サービス | パターン | エントロピー閾値 |
|---------|---------|----------------|
| AWS | `AKIA[0-9A-Z]{16}` | 4.0 |
| GitHub | `ghp_[a-zA-Z0-9]{36}` | 4.5 |
| Stripe | `sk_live_[a-zA-Z0-9]{24}` | 4.5 |
| JWT | `eyJ[a-zA-Z0-9_-]*\.eyJ[a-zA-Z0-9_-]*\.[a-zA-Z0-9_-]*` | 3.5 |
| Generic API Key | 高エントロピー文字列 | 4.5 |

**トレーサビリティ**: REQ-SEC2-SECRET-001, REQ-SEC2-SECRET-002

---

#### DES-SEC2-SECRET-003: PreCommitHook

**責務**: コミット前のシークレット検出・ブロック

**インターフェース**:
```typescript
interface PreCommitHook {
  // フック設定のインストール
  install(repoPath: string, options?: HookOptions): Promise<void>;
  
  // フック設定のアンインストール
  uninstall(repoPath: string): Promise<void>;
  
  // ステージングエリアのスキャン
  scanStaged(repoPath: string): Promise<StagedScanResult>;
  
  // コミットのブロック判定
  shouldBlock(secrets: Secret[]): boolean;
  
  // 安全な代替案の提案
  suggestAlternatives(secret: Secret): SecretAlternative[];
}

interface HookOptions {
  blockOnDetection: boolean;  // デフォルト: true
  allowList?: string[];       // 許可パターン
  severity: Severity[];       // ブロック対象の重大度
}

interface StagedScanResult {
  secrets: Secret[];
  shouldBlock: boolean;
  message: string;
  alternatives: SecretAlternative[];
}

interface SecretAlternative {
  description: string;
  example: string;
  tool?: string;  // 例: 'dotenv', 'vault', 'aws-secrets-manager'
}
```

**IDE統合**:
| IDE | 統合方式 | 機能 |
|-----|---------|------|
| VS Code | LSP | リアルタイム警告、Quick Fix |
| JetBrains | プラグイン | インライン警告 |
| Vim/Neovim | LSP | 診断表示 |

**トレーサビリティ**: REQ-SEC2-SECRET-003

---

#### DES-SEC2-DEP-001: DependencyAuditor

**責務**: 依存関係の脆弱性監査

**インターフェース**:
```typescript
interface DependencyAuditor {
  // 依存関係監査
  audit(packageFile: string): Promise<AuditResult>;
  
  // CVE照合
  checkCVE(dependency: Dependency): Promise<CVE[]>;
  
  // サプライチェーン分析
  analyzeSupplyChain(dependency: Dependency): Promise<SupplyChainRisk>;
  
  // SBOM生成
  generateSBOM(format: 'spdx' | 'cyclonedx'): Promise<SBOM>;
}

interface Dependency {
  name: string;
  version: string;
  type: 'direct' | 'transitive';
  ecosystem: 'npm' | 'pip' | 'maven' | 'cargo' | 'go';
  integrity?: string;
}

interface SupplyChainRisk {
  typosquatting: boolean;
  dependencyConfusion: boolean;
  maintainerChange: boolean;
  maliciousCode: boolean;
  riskScore: number;
}
```

**データソース**:
| ソース | API | 更新頻度 |
|--------|-----|---------|
| NVD | REST | 毎日 |
| GitHub Advisory | GraphQL | リアルタイム |
| OSV | REST | リアルタイム |
| Snyk | REST | リアルタイム |

**トレーサビリティ**: REQ-SEC2-DEP-001, REQ-SEC2-DEP-002, REQ-SEC2-DEP-003

---

#### DES-SEC2-AI-001: PromptInjectionDetector

**責務**: LLM統合コードにおけるプロンプトインジェクション検出

**インターフェース**:
```typescript
interface PromptInjectionDetector {
  // プロンプトインジェクション検出
  detect(sourceFile: SourceFile): Promise<PromptInjection[]>;
  
  // LLM API呼び出し識別
  identifyLLMCalls(ast: AST): LLMCall[];
  
  // 入力検証チェック
  checkInputValidation(call: LLMCall): ValidationStatus;
  
  // 出力検証チェック
  checkOutputValidation(call: LLMCall): ValidationStatus;
}

interface PromptInjection {
  id: string;
  type: 'direct' | 'indirect' | 'jailbreak' | 'prompt-leak';
  location: SourceLocation;
  llmProvider: string;
  userInputPath: TaintPath;
  severity: Severity;
  recommendation: string;
}

interface LLMCall {
  provider: 'openai' | 'anthropic' | 'azure-openai' | 'other';
  method: string;
  promptArgument: AST.Node;
  location: SourceLocation;
}
```

**検出パターン**:
| パターン | 説明 | 例 |
|---------|------|-----|
| Direct Concatenation | ユーザー入力の直接結合 | `prompt = userInput + systemPrompt` |
| Template Literal | テンプレートリテラル内挿入 | `` `${userInput}` `` |
| Indirect via RAG | RAG経由の間接挿入 | 外部ドキュメント内の悪意あるテキスト |
| Jailbreak Pattern | 既知のJailbreakパターン | "Ignore previous instructions" |

**トレーサビリティ**: REQ-SEC2-AI-001, REQ-SEC2-AI-002

---

### 2.3 Intelligence Layer

#### DES-SEC2-SAST-002: NeuroSymbolicCore

**責務**: LLM（Neural）と知識グラフ（Symbolic）の統合推論

**インターフェース**:
```typescript
interface NeuroSymbolicCore {
  // 統合分析
  analyze(vulnerability: Vulnerability): Promise<NeuroSymbolicResult>;
  
  // ニューラル分析
  neuralAnalyze(code: string, context: AnalysisContext): Promise<NeuralResult>;
  
  // シンボリック検証
  symbolicVerify(vulnerability: Vulnerability): Promise<SymbolicResult>;
  
  // 信頼度統合
  integrateConfidence(neural: NeuralResult, symbolic: SymbolicResult): number;
}

interface NeuroSymbolicResult {
  isValid: boolean;
  confidence: number;
  neuralExplanation: string;
  symbolicEvidence: Evidence[];
  finalDecision: 'confirmed' | 'rejected' | 'needs-review';
}

// 信頼度統合ルール（REQ-INT-002準拠）
// | シンボリック結果 | ニューラル信頼度 | 最終決定 |
// |-----------------|-----------------|---------|
// | invalid         | -               | 棄却    |
// | valid           | ≥0.8            | 採用    |
// | valid           | <0.8            | シンボリック優先 |
```

**統合アルゴリズム**:
```
1. ニューラル分析実行 → neural_confidence
2. シンボリック検証実行 → symbolic_valid
3. IF symbolic_valid == false THEN return REJECT
4. IF neural_confidence >= 0.8 THEN return ACCEPT with neural_explanation
5. ELSE return ACCEPT with symbolic_evidence
```

**トレーサビリティ**: REQ-SEC2-SAST-002

---

#### DES-SEC2-INT-YATA: KnowledgeQuery

**責務**: YATA知識グラフへのクエリ

**インターフェース**:
```typescript
interface KnowledgeQuery {
  // パターン検索
  queryPattern(pattern: PatternQuery): Promise<SecurityPattern[]>;
  
  // ルールマッチング
  matchRule(code: string, language: Language): Promise<MatchedRule[]>;
  
  // 脆弱性推論
  inferVulnerability(codePattern: CodePattern): Promise<InferredVuln[]>;
  
  // ベストプラクティス取得
  getBestPractice(context: string): Promise<BestPractice[]>;
}

interface SecurityPattern {
  id: string;
  name: string;
  description: string;
  cwes: string[];
  codePatterns: CodePattern[];
  mitigations: Mitigation[];
  confidence: number;
}
```

**トレーサビリティ**: REQ-SEC2-SAST-002, REQ-SEC2-SAST-003

---

### 2.4 Fix Layer

#### DES-SEC2-FIX-001: FixGenerator

**責務**: LLMを活用した修正コード生成

**インターフェース**:
```typescript
interface FixGenerator {
  // 修正生成
  generate(vulnerability: Vulnerability): Promise<Fix[]>;
  
  // 修正ランキング
  rank(fixes: Fix[]): Fix[];
  
  // 修正適用
  apply(fix: Fix): Promise<ApplyResult>;
  
  // 差分生成
  generateDiff(fix: Fix): string;
}

interface Fix {
  id: string;
  vulnerabilityId: string;
  originalCode: string;
  fixedCode: string;
  explanation: string;
  confidence: number;
  verified: boolean;
  testCases?: TestCase[];
}
```

**LLMプロンプト戦略**:
1. **コンテキスト提供**: 脆弱性情報、周辺コード、プロジェクト規約
2. **複数候補生成**: temperature調整で多様な修正候補
3. **説明要求**: 修正理由の自然言語説明

**トレーサビリティ**: REQ-SEC2-FIX-001

---

#### DES-SEC2-FIX-002: Z3Verifier

**責務**: Z3 SMTソルバーによる修正の形式検証

**インターフェース**:
```typescript
interface Z3Verifier {
  // 修正検証
  verify(original: Code, fixed: Code, property: SecurityProperty): Promise<VerifyResult>;
  
  // 不変条件チェック
  checkInvariant(code: Code, invariant: Invariant): Promise<boolean>;
  
  // 安全性証明
  proveSafe(fix: Fix, vulnerability: Vulnerability): Promise<ProofResult>;
}

interface SecurityProperty {
  type: 'no-injection' | 'no-overflow' | 'no-null-deref' | 'sanitized';
  constraints: Constraint[];
}

interface VerifyResult {
  verified: boolean;
  counterExample?: CounterExample;
  proof?: Proof;
  timeout: boolean;
}
```

**検証戦略**:
1. **前条件抽出**: 脆弱性を発生させる条件
2. **後条件定義**: 修正後に満たすべき安全性条件
3. **SMT問題生成**: コードを論理式に変換
4. **検証実行**: Z3で充足可能性チェック

**トレーサビリティ**: REQ-SEC2-FIX-002

---

#### DES-SEC2-FIX-003: TestGenerator

**責務**: 脆弱性修正のための回帰テスト自動生成

**インターフェース**:
```typescript
interface TestGenerator {
  // テスト生成
  generate(vulnerability: Vulnerability, fix: Fix): Promise<TestCase[]>;
  
  // 回帰テスト
  generateRegression(vulnerability: Vulnerability): TestCase;
  
  // エッジケース
  generateEdgeCases(fix: Fix): TestCase[];
  
  // テストコード出力
  renderTest(testCase: TestCase, framework: TestFramework): string;
}

interface TestCase {
  id: string;
  name: string;
  description: string;
  input: any;
  expectedOutput: any;
  assertions: Assertion[];
  type: 'regression' | 'positive' | 'edge-case';
}
```

**トレーサビリティ**: REQ-SEC2-FIX-003

---

## 3. Infrastructure Layer コンポーネント

### 3.1 DES-SEC2-INFRA-001: ASTParser

**責務**: ソースコードのAST解析

**実装**: ts-morph (TypeScript), tree-sitter (多言語)

```typescript
interface ASTParser {
  parse(code: string, language: Language): AST;
  getSourceFile(filePath: string): SourceFile;
  findNodes(ast: AST, kind: SyntaxKind): AST.Node[];
}
```

### 3.2 DES-SEC2-INFRA-002: YATAClient

**責務**: YATA知識グラフとの通信

```typescript
interface YATAClient {
  query(sparql: string): Promise<QueryResult>;
  addTriple(triple: Triple): Promise<void>;
  getPattern(id: string): Promise<Pattern>;
}
```

### 3.3 DES-SEC2-INFRA-003: LLMClient

**責務**: LLM APIとの通信

```typescript
interface LLMClient {
  complete(prompt: string, options: LLMOptions): Promise<string>;
  chat(messages: Message[], options: LLMOptions): Promise<Message>;
  embed(text: string): Promise<number[]>;
}
```

### 3.4 DES-SEC2-LOG-001: AuditLogger

**責務**: セキュリティ監査ログの記録

```typescript
interface AuditLogger {
  logScan(scan: ScanEvent): void;
  logVulnerability(vuln: VulnerabilityEvent): void;
  logFix(fix: FixEvent): void;
  logConfig(config: ConfigEvent): void;
  export(format: 'json' | 'syslog'): string;
}
```

**トレーサビリティ**: REQ-SEC2-LOG-001

### 3.5 DES-SEC2-CFG-001: ConfigManager

**責務**: 設定ファイルの読み込み・検証

```typescript
interface ConfigManager {
  load(filePath?: string): SecurityConfig;
  validate(config: SecurityConfig): ValidationResult;
  merge(base: SecurityConfig, override: Partial<SecurityConfig>): SecurityConfig;
  getDefault(): SecurityConfig;
}
```

**トレーサビリティ**: REQ-SEC2-CFG-001

### 3.6 DES-SEC2-ERR-001: ErrorHandler

**責務**: エラーハンドリングとリカバリー

```typescript
interface ErrorHandler {
  handle(error: Error, context: ErrorContext): ErrorResult;
  retry<T>(fn: () => Promise<T>, options: RetryOptions): Promise<T>;
  aggregate(errors: Error[]): AggregatedError;
}
```

**トレーサビリティ**: REQ-SEC2-ERR-001

---

## 4. Interface Layer コンポーネント

### 4.1 DES-SEC2-CLI-001: SecurityCLI

**責務**: コマンドラインインターフェース

```typescript
// コマンド構造
musubix-security
├── scan <path>           # 脆弱性スキャン
│   ├── --format          # 出力形式
│   ├── --severity        # 最小重大度
│   ├── --config          # 設定ファイル
│   └── --output          # 出力先
├── taint <path>          # テイント分析
├── secrets <path>        # シークレット検出
├── audit <path>          # 依存関係監査
├── fix <vuln-id>         # 自動修正
├── report <path>         # レポート生成
├── container <image>     # コンテナスキャン
├── iac <path>            # IaCスキャン
└── config                # 設定管理
    ├── init              # 設定初期化
    └── validate          # 設定検証
```

**トレーサビリティ**: REQ-SEC2-CLI-001, REQ-SEC2-CLI-002

### 4.2 DES-SEC2-INT-003: SecurityMCPServer

**責務**: MCPプロトコルによるAIエージェント統合

```typescript
// MCP Tools
const tools = [
  'security_scan',      // 脆弱性スキャン
  'taint_analyze',      // テイント分析
  'secret_detect',      // シークレット検出
  'dependency_audit',   // 依存関係監査
  'fix_generate',       // 修正生成
  'fix_verify',         // 修正検証
  'report_generate',    // レポート生成
];

// MCP Prompts
const prompts = [
  'security_review',        // セキュリティレビュー
  'vulnerability_explain',  // 脆弱性説明
  'fix_recommend',          // 修正推奨
];
```

**トレーサビリティ**: REQ-SEC2-INT-003

### 4.3 DES-SEC2-INT-001: SecurityLSPServer

**責務**: VS Code統合（Language Server Protocol）

```typescript
// LSP Capabilities
const capabilities = {
  diagnostics: true,        // インライン診断
  codeActions: true,        // Quick Fix
  codeLens: true,           // 脆弱性インジケータ
  hover: true,              // 脆弱性詳細ホバー
  completion: false,        // 補完は提供しない
};
```

**トレーサビリティ**: REQ-SEC2-INT-001

---

## 5. コンポーネント間依存関係

```
┌─────────────────────────────────────────────────────────────────┐
│                        Dependency Graph                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  CLI ──────┐                                                    │
│            │                                                    │
│  MCP ──────┼──► SecurityService ──► PipelineManager             │
│            │         │                    │                     │
│  LSP ──────┘         │                    ▼                     │
│                      │              All Analyzers                │
│                      │                    │                     │
│                      │                    ▼                     │
│                      │         NeuroSymbolicCore                 │
│                      │              │         │                 │
│                      │              ▼         ▼                 │
│                      │         LLMClient  YATAClient            │
│                      │                                          │
│                      ▼                                          │
│               FixGenerator ──► Z3Verifier                       │
│                    │                                            │
│                    ▼                                            │
│              TestGenerator                                       │
│                                                                 │
│  ═══════════════════════════════════════════════════════════   │
│  Infrastructure: ASTParser, ConfigManager, AuditLogger,         │
│                  ErrorHandler, Cache                             │
└─────────────────────────────────────────────────────────────────┘
```

---

## 6. 改訂履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 0.1.0 | 2026-01-07 | 初版作成（全コンポーネント定義） | AI Agent |
| 0.2.0 | 2026-01-07 | レビュー指摘対応: DES-SEC2-SAST-003/004, DES-SEC2-TAINT-003, DES-SEC2-SECRET-003追加、コンポーネント名統一 | AI Agent |

