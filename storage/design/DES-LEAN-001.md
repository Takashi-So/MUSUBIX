# DES-LEAN-001: musubix-lean パッケージ設計仕様書

**バージョン**: 2.0.0-alpha.1  
**作成日**: 2026-01-06  
**ステータス**: Draft  
**トレーサビリティ**: REQ-LEAN-001

---

## 1. 概要

### 1.1 設計目標

musubix-leanパッケージは、Lean 4形式検証システムとMUSUBIXフレームワークの統合を実現する。本設計は以下の原則に基づく：

1. **疎結合**: Lean 4ランタイムへの依存を最小限に抑え、Lean未インストール環境でもグレースフルに動作
2. **拡張性**: ReProver等の外部証明探索システムへの拡張をサポート
3. **トレーサビリティ**: EARS要件から証明結果まで完全な追跡を維持
4. **段階的採用**: 既存formal-verifyパッケージとの共存と段階的移行をサポート

### 1.2 アーキテクチャ方針

| 方針 | 説明 |
|------|------|
| **Strategy Pattern** | 証明戦略の差し替え可能な設計 |
| **Adapter Pattern** | Lean 4 CLIとの疎結合な連携 |
| **Builder Pattern** | Leanコード生成の段階的構築 |
| **Observer Pattern** | 証明進捗の通知機構 |

---

## 2. C4モデル

### 2.1 Context Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           External Systems                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐              │
│  │  Developer   │    │   Lean 4     │    │   ReProver   │              │
│  │              │    │   Runtime    │    │   Service    │              │
│  └──────┬───────┘    └──────┬───────┘    └──────┬───────┘              │
│         │                   │                   │                       │
│         │  CLI/API          │  lake/lean CLI    │  REST API             │
│         ▼                   ▼                   ▼                       │
│  ┌─────────────────────────────────────────────────────────────┐       │
│  │                    musubix-lean                              │       │
│  │                                                              │       │
│  │  • EARS→Lean変換                                             │       │
│  │  • TypeScript仕様化                                          │       │
│  │  • 証明生成・検証                                            │       │
│  │  • トレーサビリティ管理                                      │       │
│  └──────────────────────────┬──────────────────────────────────┘       │
│                             │                                           │
│         ┌───────────────────┼───────────────────┐                       │
│         │                   │                   │                       │
│         ▼                   ▼                   ▼                       │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐              │
│  │ formal-verify│    │ YATA Local   │    │  MCP Server  │              │
│  │   (Z3/SMT)   │    │   (KG)       │    │              │              │
│  └──────────────┘    └──────────────┘    └──────────────┘              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Container Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         musubix-lean Package                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                        Public API Layer                          │   │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │   │
│  │  │ LeanIntegration │  │    LeanCLI      │  │  LeanMCPTools   │  │   │
│  │  │     (API)       │  │  (Commander)    │  │   (MCP)         │  │   │
│  │  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘  │   │
│  └───────────┼────────────────────┼────────────────────┼────────────┘   │
│              │                    │                    │                │
│  ┌───────────┼────────────────────┼────────────────────┼────────────┐   │
│  │           ▼                    ▼                    ▼            │   │
│  │                         Core Services                            │   │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │   │
│  │  │ LeanEnvironment │  │EarsToLeanConv   │  │TypeScriptSpec   │  │   │
│  │  │   Detector      │  │    erter        │  │    ifier        │  │   │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘  │   │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │   │
│  │  │  ProofGenerator │  │ ReProverClient  │  │ Verification    │  │   │
│  │  │                 │  │                 │  │   Reporter      │  │   │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘  │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                       Infrastructure Layer                        │   │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │   │
│  │  │   LeanRunner    │  │ LeanFileGen     │  │ LeanProject     │  │   │
│  │  │  (CLI Adapter)  │  │   erator        │  │  Initializer    │  │   │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘  │   │
│  │  ┌─────────────────┐  ┌─────────────────┐                       │   │
│  │  │ Traceability    │  │ HybridVerifier  │                       │   │
│  │  │   Manager       │  │  (Z3 Bridge)    │                       │   │
│  │  └─────────────────┘  └─────────────────┘                       │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.3 Component Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          Core Components                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                    LeanIntegration (Facade)                     │    │
│  │  ┌──────────────────────────────────────────────────────────┐  │    │
│  │  │ + initialize(): Promise<void>                             │  │    │
│  │  │ + earsToTheorem(req: EarsReq): Promise<LeanTheorem>       │  │    │
│  │  │ + specifyFunction(fn: TSFunction): Promise<LeanSpec>      │  │    │
│  │  │ + prove(theorem: LeanTheorem): Promise<ProofResult>       │  │    │
│  │  │ + verify(proof: LeanProof): Promise<VerificationResult>   │  │    │
│  │  │ + getTraceability(): TraceabilityMatrix                   │  │    │
│  │  └──────────────────────────────────────────────────────────┘  │    │
│  └────────────────────────────────────────────────────────────────┘    │
│         │                                                               │
│         ├──────────────────┬──────────────────┬────────────────────┐   │
│         ▼                  ▼                  ▼                    ▼   │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐   ┌──────────┐│
│  │LeanEnviron   │   │EarsToLean    │   │TypeScript    │   │Proof     ││
│  │mentDetector  │   │Converter     │   │Specifier     │   │Generator ││
│  ├──────────────┤   ├──────────────┤   ├──────────────┤   ├──────────┤│
│  │+detect()     │   │+convert()    │   │+specify()    │   │+generate()│
│  │+validateVer()│   │+parseEars()  │   │+extractSig() │   │+applyTac()│
│  │+getPath()    │   │+buildThm()   │   │+inferPre()   │   │+search() ││
│  └──────────────┘   └──────────────┘   └──────────────┘   └──────────┘│
│                                                                         │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐   ┌──────────┐│
│  │ReProver      │   │Verification  │   │Traceability  │   │Hybrid    ││
│  │Client        │   │Reporter      │   │Manager       │   │Verifier  ││
│  ├──────────────┤   ├──────────────┤   ├──────────────┤   ├──────────┤│
│  │+connect()    │   │+success()    │   │+link()       │   │+classify()│
│  │+search()     │   │+failure()    │   │+getMatrix()  │   │+routeZ3()││
│  │+feedback()   │   │+counterex()  │   │+update()     │   │+routeLean│
│  └──────────────┘   └──────────────┘   └──────────────┘   └──────────┘│
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 3. コンポーネント詳細設計

### 3.1 LeanEnvironmentDetector

**責務**: Lean 4実行環境の検出と検証  
**トレーサビリティ**: REQ-LEAN-CORE-001, REQ-LEAN-ERR-001

```typescript
interface LeanEnvironmentInfo {
  readonly installed: boolean;
  readonly version: string | null;
  readonly path: string | null;
  readonly lakeVersion: string | null;
  readonly mathlibAvailable: boolean;
}

interface LeanEnvironmentDetector {
  detect(): Promise<LeanEnvironmentInfo>;
  validateVersion(minVersion: string): boolean;
  getInstallInstructions(os: 'linux' | 'macos' | 'windows'): string;
}
```

**実装方針**:
- `which lean` または `where lean` でパス検出
- `lean --version` でバージョン取得
- キャッシュにより再検出を回避

### 3.2 EarsToLeanConverter

**責務**: EARS形式要件からLean定理への変換  
**トレーサビリティ**: REQ-LEAN-CONV-001〜005

```typescript
interface EarsRequirement {
  readonly id: string;
  readonly pattern: 'ubiquitous' | 'event-driven' | 'state-driven' | 'unwanted' | 'optional';
  readonly text: string;
  readonly parsed: EarsParsedComponents;
}

interface LeanTheorem {
  readonly name: string;
  readonly requirementId: string;
  readonly hypotheses: LeanHypothesis[];
  readonly conclusion: LeanExpression;
  readonly sourceText: string;
}

interface EarsToLeanConverter {
  convert(requirement: EarsRequirement): Result<LeanTheorem, ConversionError>;
  parseEars(text: string): Result<EarsParsedComponents, ParseError>;
  buildTheorem(components: EarsParsedComponents, reqId: string): LeanTheorem;
}
```

**変換ルール**:

| EARSパターン | Lean構造 |
|-------------|---------|
| Ubiquitous | `theorem req_xxx : ∀ x, P x` |
| Event-driven | `theorem req_xxx : event → response` |
| State-driven | `theorem req_xxx : state_pred → invariant_preserved` |
| Unwanted | `theorem req_xxx : ¬ unwanted_behavior` |
| Optional | `theorem req_xxx : condition → response` |

### 3.3 TypeScriptSpecifier

**責務**: TypeScriptコードからLean仕様への変換  
**トレーサビリティ**: REQ-LEAN-TS-001〜004

```typescript
interface TypeScriptFunction {
  readonly name: string;
  readonly filePath: string;
  readonly parameters: TSParameter[];
  readonly returnType: TSType;
  readonly preconditions: Precondition[];
  readonly postconditions: Postcondition[];
  readonly invariants: Invariant[];
}

interface LeanFunctionSpec {
  readonly functionName: string;
  readonly typeSignature: string;
  readonly preconditionHypotheses: LeanHypothesis[];
  readonly postconditionGoal: LeanExpression;
  readonly leanCode: string;
}

interface TypeScriptSpecifier {
  specify(func: TypeScriptFunction): Result<LeanFunctionSpec, SpecificationError>;
  extractSignature(code: string, funcName: string): TSFunctionSignature;
  inferPreconditions(func: TypeScriptFunction): Precondition[];
  inferPostconditions(func: TypeScriptFunction): Postcondition[];
}
```

**型マッピング**:

| TypeScript | Lean 4 |
|------------|--------|
| `number` | `Int` (整数文脈) / `Float` (浮動小数点) |
| `string` | `String` |
| `boolean` | `Bool` |
| `Array<T>` | `List T` |
| `T \| null` | `Option T` |
| `Result<T, E>` | `Except E T` |

### 3.4 ProofGenerator

**責務**: 証明の自動生成と探索  
**トレーサビリティ**: REQ-LEAN-PROOF-001〜003

```typescript
interface ProofStrategy {
  readonly name: string;
  readonly tactics: string[];
  readonly applicability: (theorem: LeanTheorem) => boolean;
}

interface ProofResult {
  readonly success: boolean;
  readonly proof: LeanProof | null;
  readonly proofState: ProofState | null;
  readonly tacticsAttempted: string[];
  readonly duration: number;
}

interface ProofGenerator {
  generate(theorem: LeanTheorem, options?: ProofOptions): Promise<ProofResult>;
  applyTactic(state: ProofState, tactic: string): Promise<TacticResult>;
  generateSketch(theorem: LeanTheorem): LeanProofSketch;
  selectStrategy(theorem: LeanTheorem): ProofStrategy;
}
```

**標準タクティクス**:
1. `simp` - 単純化
2. `rfl` - 反射性
3. `decide` - 決定可能命題
4. `native_decide` - ネイティブ決定
5. `induction` - 帰納法
6. `cases` - 場合分け

### 3.5 ReProverClient

**責務**: ReProver外部サービスとの連携  
**トレーサビリティ**: REQ-LEAN-REPROVER-001〜003

```typescript
interface ReProverConfig {
  readonly endpoint: string;
  readonly timeout: number;
  readonly maxDepth: number;
  readonly apiKey?: string;
}

interface ReProverSearchResult {
  readonly found: boolean;
  readonly proof: string | null;
  readonly searchPath: SearchNode[];
  readonly suggestions: string[];
}

interface ReProverClient {
  connect(config: ReProverConfig): Promise<void>;
  isAvailable(): boolean;
  search(proofState: ProofState, options?: SearchOptions): Promise<ReProverSearchResult>;
  getFeedback(failedState: ProofState): ProofFeedback;
}
```

### 3.6 VerificationReporter

**責務**: 検証結果のレポート生成  
**トレーサビリティ**: REQ-LEAN-FEEDBACK-001〜003

```typescript
interface VerificationReport {
  readonly requirementId: string;
  readonly theoremName: string;
  readonly status: 'verified' | 'failed' | 'timeout' | 'error';
  readonly proof?: LeanProof;
  readonly counterexample?: Counterexample;
  readonly diagnostics: Diagnostic[];
  readonly timestamp: Date;
  readonly duration: number;
}

interface Counterexample {
  readonly values: Record<string, unknown>;
  readonly violatedCondition: string;
  readonly typescriptReproduction: string;
}

interface VerificationReporter {
  reportSuccess(result: VerificationResult): VerificationReport;
  reportFailure(failure: VerificationFailure): VerificationReport;
  generateCounterexample(state: ProofState): Counterexample | null;
  formatDiagnostic(error: LeanError): Diagnostic;
}
```

### 3.7 LeanRunner

**責務**: Lean 4 CLI実行のアダプター  
**トレーサビリティ**: REQ-LEAN-CORE-004

```typescript
interface LeanRunnerOptions {
  readonly timeout: number;
  readonly cwd?: string;
  readonly env?: Record<string, string>;
}

interface LeanExecutionResult {
  readonly exitCode: number;
  readonly stdout: string;
  readonly stderr: string;
  readonly duration: number;
}

interface LeanRunner {
  run(args: string[], options?: LeanRunnerOptions): Promise<LeanExecutionResult>;
  lakeBuild(projectDir: string): Promise<LeanExecutionResult>;
  checkFile(filePath: string): Promise<LeanExecutionResult>;
  evaluate(expression: string): Promise<LeanExecutionResult>;
}
```

### 3.8 TraceabilityManager

**責務**: 要件から検証結果までのトレーサビリティ管理  
**トレーサビリティ**: REQ-LEAN-INTEG-002

```typescript
interface TraceabilityLink {
  readonly requirementId: string;
  readonly theoremName: string;
  readonly verificationStatus: 'pending' | 'verified' | 'failed';
  readonly leanFilePath: string;
  readonly lastVerified?: Date;
}

interface TraceabilityMatrix {
  readonly links: TraceabilityLink[];
  readonly coverage: number;
  readonly lastUpdated: Date;
}

interface TraceabilityManager {
  link(requirementId: string, theoremName: string, filePath: string): void;
  updateStatus(theoremName: string, status: 'verified' | 'failed'): void;
  getMatrix(): TraceabilityMatrix;
  exportToMarkdown(): string;
}
```

### 3.9 HybridVerifier

**責務**: Z3とLean 4の協調検証  
**トレーサビリティ**: REQ-LEAN-INTEG-001

```typescript
type VerificationTarget = 'z3' | 'lean' | 'both';

interface ClassificationResult {
  readonly target: VerificationTarget;
  readonly reason: string;
  readonly confidence: number;
}

interface HybridVerificationResult {
  readonly z3Result?: Z3VerificationResult;
  readonly leanResult?: LeanVerificationResult;
  readonly combinedStatus: 'verified' | 'failed' | 'partial';
  readonly report: CombinedReport;
}

interface HybridVerifier {
  classify(property: Property): ClassificationResult;
  routeToZ3(property: Property): Promise<Z3VerificationResult>;
  routeToLean(property: Property): Promise<LeanVerificationResult>;
  combine(z3: Z3VerificationResult, lean: LeanVerificationResult): HybridVerificationResult;
}
```

**分類基準**:

| 特性 | 推奨ターゲット |
|------|---------------|
| 線形算術制約 | Z3 |
| 配列境界チェック | Z3 |
| 帰納的性質 | Lean |
| 高次関数性質 | Lean |
| 型不変条件 | Both |

---

## 4. ディレクトリ構造

```
packages/lean/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── README.md
├── src/
│   ├── index.ts                    # Public exports
│   ├── integration/
│   │   └── LeanIntegration.ts      # Facade class
│   ├── environment/
│   │   ├── LeanEnvironmentDetector.ts
│   │   ├── LeanProjectInitializer.ts
│   │   └── index.ts
│   ├── converters/
│   │   ├── EarsToLeanConverter.ts
│   │   ├── TypeScriptSpecifier.ts
│   │   ├── types.ts
│   │   └── index.ts
│   ├── proof/
│   │   ├── ProofGenerator.ts
│   │   ├── ProofStrategy.ts
│   │   ├── ReProverClient.ts
│   │   └── index.ts
│   ├── reporting/
│   │   ├── VerificationReporter.ts
│   │   ├── templates/
│   │   └── index.ts
│   ├── infrastructure/
│   │   ├── LeanRunner.ts
│   │   ├── LeanFileGenerator.ts
│   │   └── index.ts
│   ├── traceability/
│   │   ├── TraceabilityManager.ts
│   │   └── index.ts
│   ├── hybrid/
│   │   ├── HybridVerifier.ts
│   │   └── index.ts
│   ├── cli/
│   │   └── lean-commands.ts
│   └── mcp/
│       └── lean-tools.ts
└── __tests__/
    ├── environment/
    ├── converters/
    ├── proof/
    ├── reporting/
    └── integration/
```

---

## 5. シーケンス図

### 5.1 EARS→Lean変換フロー

```
Developer          LeanIntegration    EarsToLeanConverter    LeanFileGenerator
    │                    │                    │                    │
    │ earsToTheorem(req) │                    │                    │
    │───────────────────>│                    │                    │
    │                    │                    │                    │
    │                    │ convert(req)       │                    │
    │                    │───────────────────>│                    │
    │                    │                    │                    │
    │                    │                    │ parseEars(text)    │
    │                    │                    │──────────┐         │
    │                    │                    │<─────────┘         │
    │                    │                    │                    │
    │                    │                    │ buildTheorem()     │
    │                    │                    │──────────┐         │
    │                    │                    │<─────────┘         │
    │                    │                    │                    │
    │                    │ Result<LeanTheorem>│                    │
    │                    │<───────────────────│                    │
    │                    │                    │                    │
    │                    │ generate(theorem)  │                    │
    │                    │────────────────────────────────────────>│
    │                    │                    │                    │
    │                    │                    │    leanFilePath    │
    │                    │<────────────────────────────────────────│
    │                    │                    │                    │
    │ Result<LeanTheorem>│                    │                    │
    │<───────────────────│                    │                    │
```

### 5.2 証明生成フロー

```
Developer       LeanIntegration    ProofGenerator    LeanRunner    ReProverClient
    │                 │                  │               │               │
    │ prove(theorem)  │                  │               │               │
    │────────────────>│                  │               │               │
    │                 │                  │               │               │
    │                 │ generate(thm)    │               │               │
    │                 │─────────────────>│               │               │
    │                 │                  │               │               │
    │                 │                  │ run(["lean"]) │               │
    │                 │                  │──────────────>│               │
    │                 │                  │               │               │
    │                 │                  │   result      │               │
    │                 │                  │<──────────────│               │
    │                 │                  │               │               │
    │                 │                  │ [if basic fails]             │
    │                 │                  │               │               │
    │                 │                  │ search(state) │               │
    │                 │                  │───────────────────────────────>
    │                 │                  │               │               │
    │                 │                  │              result           │
    │                 │                  │<───────────────────────────────
    │                 │                  │               │               │
    │                 │  ProofResult     │               │               │
    │                 │<─────────────────│               │               │
    │                 │                  │               │               │
    │  ProofResult    │                  │               │               │
    │<────────────────│                  │               │               │
```

---

## 6. エラーハンドリング

### 6.1 エラー階層

```typescript
// Base error
class LeanError extends Error {
  constructor(
    message: string,
    public readonly code: string,
    public readonly cause?: Error
  ) {
    super(message);
  }
}

// Environment errors
class LeanNotFoundError extends LeanError {
  constructor(os: string) {
    super(
      `Lean 4 is not installed. ${getInstallInstructions(os)}`,
      'LEAN_NOT_FOUND'
    );
  }
}

class LeanVersionError extends LeanError {
  constructor(required: string, actual: string) {
    super(
      `Lean version ${actual} is below minimum required ${required}`,
      'LEAN_VERSION_MISMATCH'
    );
  }
}

// Conversion errors
class EarsConversionError extends LeanError {
  constructor(requirementId: string, reason: string) {
    super(
      `Failed to convert requirement ${requirementId}: ${reason}`,
      'EARS_CONVERSION_FAILED'
    );
  }
}

// Proof errors
class ProofTimeoutError extends LeanError {
  constructor(theoremName: string, timeout: number) {
    super(
      `Proof search for ${theoremName} timed out after ${timeout}ms`,
      'PROOF_TIMEOUT'
    );
  }
}
```

### 6.2 リカバリ戦略

| エラー | リカバリ戦略 |
|--------|-------------|
| Lean未インストール | インストール手順を表示、グレースフルに終了 |
| バージョン不一致 | アップグレード手順を表示 |
| 変換失敗 | 部分変換を継続、失敗レポートを蓄積 |
| 証明タイムアウト | スケッチを生成して手動完了を促す |
| ReProver接続失敗 | 基本証明にフォールバック |

---

## 7. 設定スキーマ

```typescript
interface LeanConfig {
  /** Lean 4 executable path (auto-detected if not specified) */
  leanPath?: string;
  
  /** Minimum required Lean version */
  minVersion: string; // default: "4.0.0"
  
  /** Default proof timeout in milliseconds */
  proofTimeout: number; // default: 30000
  
  /** ReProver configuration */
  reprover?: {
    endpoint: string;
    apiKey?: string;
    maxDepth: number; // default: 10
    timeout: number; // default: 60000
  };
  
  /** Output directory for generated Lean files */
  outputDir: string; // default: ".musubix/lean"
  
  /** Include Mathlib dependency */
  useMathlib: boolean; // default: false
  
  /** Verification strategy */
  strategy: 'lean-only' | 'hybrid' | 'z3-fallback'; // default: 'hybrid'
}
```

---

## 8. トレーサビリティマトリクス

| 要件ID | 設計コンポーネント | ファイル |
|--------|-------------------|----------|
| REQ-LEAN-CORE-001 | LeanEnvironmentDetector | environment/LeanEnvironmentDetector.ts |
| REQ-LEAN-CORE-002 | LeanProjectInitializer | environment/LeanProjectInitializer.ts |
| REQ-LEAN-CORE-003 | LeanFileGenerator | infrastructure/LeanFileGenerator.ts |
| REQ-LEAN-CORE-004 | LeanRunner | infrastructure/LeanRunner.ts |
| REQ-LEAN-CONV-001 | EarsToLeanConverter | converters/EarsToLeanConverter.ts |
| REQ-LEAN-CONV-002 | EarsToLeanConverter | converters/EarsToLeanConverter.ts |
| REQ-LEAN-CONV-003 | EarsToLeanConverter | converters/EarsToLeanConverter.ts |
| REQ-LEAN-CONV-004 | EarsToLeanConverter | converters/EarsToLeanConverter.ts |
| REQ-LEAN-CONV-005 | EarsToLeanConverter | converters/EarsToLeanConverter.ts |
| REQ-LEAN-TS-001 | TypeScriptSpecifier | converters/TypeScriptSpecifier.ts |
| REQ-LEAN-TS-002 | TypeScriptSpecifier | converters/TypeScriptSpecifier.ts |
| REQ-LEAN-TS-003 | TypeScriptSpecifier | converters/TypeScriptSpecifier.ts |
| REQ-LEAN-TS-004 | TypeScriptSpecifier | converters/TypeScriptSpecifier.ts |
| REQ-LEAN-PROOF-001 | ProofGenerator | proof/ProofGenerator.ts |
| REQ-LEAN-PROOF-002 | ProofGenerator | proof/ProofGenerator.ts |
| REQ-LEAN-PROOF-003 | ProofGenerator | proof/ProofGenerator.ts |
| REQ-LEAN-REPROVER-001 | ReProverClient | proof/ReProverClient.ts |
| REQ-LEAN-REPROVER-002 | ReProverClient | proof/ReProverClient.ts |
| REQ-LEAN-REPROVER-003 | ReProverClient | proof/ReProverClient.ts |
| REQ-LEAN-FEEDBACK-001 | VerificationReporter | reporting/VerificationReporter.ts |
| REQ-LEAN-FEEDBACK-002 | VerificationReporter | reporting/VerificationReporter.ts |
| REQ-LEAN-FEEDBACK-003 | VerificationReporter | reporting/VerificationReporter.ts |
| REQ-LEAN-API-001 | LeanIntegration | integration/LeanIntegration.ts |
| REQ-LEAN-API-002 | LeanCLI | cli/lean-commands.ts |
| REQ-LEAN-API-003 | LeanMCPTools | mcp/lean-tools.ts |
| REQ-LEAN-INTEG-001 | HybridVerifier | hybrid/HybridVerifier.ts |
| REQ-LEAN-INTEG-002 | TraceabilityManager | traceability/TraceabilityManager.ts |
| REQ-LEAN-PERF-001 | EarsToLeanConverter | converters/EarsToLeanConverter.ts |
| REQ-LEAN-PERF-002 | ProofGenerator | proof/ProofGenerator.ts |
| REQ-LEAN-ERR-001 | LeanEnvironmentDetector | environment/LeanEnvironmentDetector.ts |
| REQ-LEAN-ERR-002 | EarsToLeanConverter | converters/EarsToLeanConverter.ts |

---

## 9. 変更履歴

| バージョン | 日付 | 変更内容 | 著者 |
|-----------|------|----------|------|
| 0.1.0 | 2026-01-06 | 初版作成 | AI Agent |

