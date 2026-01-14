# DES-BUGFIX-v3.3.10: 不具合修正設計書

## 概要

REQ-BUGFIX-v3.3.10で定義された22要件を実装するための設計を記述します。

## トレーサビリティ

| 設計ID | 対応要件 |
|--------|----------|
| DES-BUGFIX-001 | REQ-BUGFIX-001-01〜04 |
| DES-BUGFIX-002 | REQ-BUGFIX-002-01〜04 |
| DES-BUGFIX-003 | REQ-BUGFIX-003-01〜04 |
| DES-BUGFIX-004 | REQ-BUGFIX-004-01〜03 |
| DES-BUGFIX-005 | REQ-BUGFIX-005-01〜05 |
| DES-BUGFIX-006 | REQ-BUGFIX-006-01〜04 |

---

## C4 Context Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                        MUSUBIX CLI                               │
│                                                                   │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │  scaffold   │  │   codegen   │  │   version   │              │
│  │   command   │  │   command   │  │   command   │              │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘              │
│         │                │                │                      │
│         ▼                ▼                ▼                      │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    @nahisaho/musubix-core               │    │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐     │    │
│  │  │ ScaffoldGen  │ │ CodeGenerator│ │VersionInfo  │     │    │
│  │  └──────────────┘ └──────────────┘ └──────────────┘     │    │
│  │  ┌──────────────┐ ┌──────────────┐                      │    │
│  │  │ContextAnalyz │ │UnitTestGen   │                      │    │
│  │  └──────────────┘ └──────────────┘                      │    │
│  └─────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────┘
```

---

## DES-BUGFIX-001: scaffoldコマンド出力改善

### C4 Component Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                  scaffold command                            │
│                                                              │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │ ScaffoldExecutor │─────▶│ OutputFormatter  │            │
│  │                  │      │                  │            │
│  │ - execute()      │      │ - formatFiles()  │            │
│  │ - validate()     │      │ - formatStats()  │            │
│  └────────┬─────────┘      │ - formatTree()   │            │
│           │                └──────────────────┘            │
│           ▼                                                 │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │ FileGenerator    │─────▶│ DirectoryChecker │            │
│  │                  │      │                  │            │
│  │ - generate()     │      │ - exists()       │            │
│  │ - countLines()   │      │ - isWritable()   │            │
│  └──────────────────┘      └──────────────────┘            │
└─────────────────────────────────────────────────────────────┘
```

### コンポーネント一覧

| ID | コンポーネント | 責務 | 対応要件 |
|----|---------------|------|----------|
| DES-001-C1 | OutputFormatter | 生成ファイル一覧・統計のフォーマット | REQ-BUGFIX-001-01, 001-02 |
| DES-001-C2 | DirectoryChecker | ディレクトリ存在・書き込み権限確認 | REQ-BUGFIX-001-04 |
| DES-001-C3 | ErrorGuidance | エラー時のガイダンス生成 | REQ-BUGFIX-001-03 |

### インターフェース定義

```typescript
// DES-001-C1: OutputFormatter
interface ScaffoldOutput {
  files: GeneratedFile[];
  stats: ScaffoldStats;
  tree: string;
}

interface GeneratedFile {
  path: string;
  lines: number;
  size: number;
}

interface ScaffoldStats {
  totalFiles: number;
  totalLines: number;
  totalSize: number;
}

function formatScaffoldOutput(output: ScaffoldOutput): string;

// DES-001-C2: DirectoryChecker
interface DirectoryCheckResult {
  exists: boolean;
  writable: boolean;
  error?: string;
}

function checkDirectory(path: string): DirectoryCheckResult;
```

### 変更対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `packages/core/src/cli/commands/scaffold.ts` | OutputFormatter統合、DirectoryChecker追加 |

---

## DES-BUGFIX-002: getMissingQuestions堅牢性向上

### C4 Component Diagram

```
┌─────────────────────────────────────────────────────────────┐
│              requirements module                             │
│                                                              │
│  ┌──────────────────────────────────────────────────┐       │
│  │         getMissingQuestions (overloaded)          │       │
│  │                                                   │       │
│  │  ┌─────────────┐     ┌─────────────────────┐     │       │
│  │  │ string[]    │     │ ClarificationContext│     │       │
│  │  │ (missingIds)│     │ (context object)    │     │       │
│  │  └──────┬──────┘     └──────────┬──────────┘     │       │
│  │         │                       │                │       │
│  │         │      ┌────────────────┘                │       │
│  │         │      ▼                                 │       │
│  │         │  ┌─────────────────────┐              │       │
│  │         │  │analyzeContextCompl- │              │       │
│  │         │  │eteness()            │              │       │
│  │         │  └──────────┬──────────┘              │       │
│  │         │             │                         │       │
│  │         ▼             ▼                         │       │
│  │     ┌─────────────────────────┐                 │       │
│  │     │  ArgumentValidator      │                 │       │
│  │     │  - validateInput()      │                 │       │
│  │     │  - isStringArray()      │                 │       │
│  │     │  - isContext()          │                 │       │
│  │     └─────────────────────────┘                 │       │
│  └──────────────────────────────────────────────────┘       │
└─────────────────────────────────────────────────────────────┘
```

### コンポーネント一覧

| ID | コンポーネント | 責務 | 対応要件 |
|----|---------------|------|----------|
| DES-002-C1 | ArgumentValidator | 引数型の検証・エラーメッセージ生成 | REQ-BUGFIX-002-02 |
| DES-002-C2 | OverloadResolver | オーバーロードパターンの解決 | REQ-BUGFIX-002-01, 002-03 |
| DES-002-C3 | DefaultHandler | 空配列/undefinedのデフォルト処理 | REQ-BUGFIX-002-04 |

### インターフェース定義

```typescript
// DES-002: Overloaded getMissingQuestions
type GetMissingQuestionsInput = readonly string[] | ClarificationContext | undefined;

function getMissingQuestions(input?: GetMissingQuestionsInput): ClarifyingQuestion[];

// 内部ヘルパー
function isStringArray(input: unknown): input is readonly string[];
function isClarificationContext(input: unknown): input is ClarificationContext;
function validateInput(input: unknown): void; // throws TypeError
```

### 変更対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `packages/core/src/requirements/clarifying-questions.ts` | オーバーロード実装、バリデーション追加 |

---

## DES-BUGFIX-003: codegenコマンド完全実装

### C4 Component Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                  codegen generate command                    │
│                                                              │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │ C4DesignParser   │─────▶│ PatternDetector  │            │
│  │                  │      │                  │            │
│  │ - parseC4()      │      │ - detect()       │            │
│  │ - extractComp()  │      │ - Repository     │            │
│  └────────┬─────────┘      │ - Service        │            │
│           │                │ - Factory        │            │
│           ▼                └──────────────────┘            │
│  ┌──────────────────┐                                      │
│  │ SkeletonGenerator│                                      │
│  │                  │      ┌──────────────────┐            │
│  │ - interface.ts   │─────▶│TraceabilityInject│            │
│  │ - impl.ts        │      │                  │            │
│  │ - test.ts        │      │ - addDESRef()    │            │
│  │ - index.ts       │      │ - addREQRef()    │            │
│  └──────────────────┘      └──────────────────┘            │
└─────────────────────────────────────────────────────────────┘
```

### コンポーネント一覧

| ID | コンポーネント | 責務 | 対応要件 |
|----|---------------|------|----------|
| DES-003-C1 | C4DesignParser | C4設計ドキュメントの解析 | REQ-BUGFIX-003-01 |
| DES-003-C2 | PatternDetector | 設計パターンの自動検出 | REQ-BUGFIX-003-02 |
| DES-003-C3 | SkeletonGenerator | 4種類のファイル生成 | REQ-BUGFIX-003-04 |
| DES-003-C4 | TraceabilityInjector | DES-*/REQ-*参照の挿入 | REQ-BUGFIX-003-03 |

### インターフェース定義

```typescript
// DES-003-C3: SkeletonGenerator
interface GeneratedSkeleton {
  interface: GeneratedFile;    // *.interface.ts
  implementation: GeneratedFile; // *.ts
  test: GeneratedFile;         // *.test.ts
  index: GeneratedFile;        // index.ts
}

interface GenerateOptions {
  withTests: boolean;
  patterns: DesignPattern[];
  traceRefs: string[];
}

function generateSkeleton(
  component: C4Component,
  options: GenerateOptions
): GeneratedSkeleton;
```

### 変更対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `packages/core/src/cli/commands/codegen.ts` | `--with-tests`オプション追加、4ファイル生成 |
| `packages/core/src/codegen/generator.ts` | SkeletonGenerator拡張 |

---

## DES-BUGFIX-004: APIドキュメント改善

### コンポーネント一覧

| ID | コンポーネント | 責務 | 対応要件 |
|----|---------------|------|----------|
| DES-004-C1 | JSDocEnhancer | JSDocコメントの追加・改善 | REQ-BUGFIX-004-03 |
| DES-004-C2 | UsageExamples | 使用例ドキュメントの追加 | REQ-BUGFIX-004-01, 004-02 |

### 変更対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `packages/core/src/symbolic/quality-gate.ts` | JSDoc追加、使用例追加 |
| `docs/API-REFERENCE.md` | QualityGateValidator、ニューロシンボリックAPI使用例追加 |

---

## DES-BUGFIX-005: CLIバージョン管理改善

### C4 Component Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                    version command                           │
│                                                              │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │ VersionDisplay   │─────▶│ DependencyVersion│            │
│  │                  │      │   Collector      │            │
│  │ - show()         │      │                  │            │
│  │ - showVerbose()  │      │ - getCoreVer()   │            │
│  └────────┬─────────┘      │ - getMcpVer()    │            │
│           │                │ - getKnowledgeV()│            │
│           ▼                └──────────────────┘            │
│  ┌──────────────────┐                                      │
│  │ VersionMismatch  │      ┌──────────────────┐            │
│  │    Detector      │─────▶│ CacheGuidance    │            │
│  │                  │      │                  │            │
│  │ - checkConfig()  │      │ - showHelp()     │            │
│  │ - warn()         │      └──────────────────┘            │
│  └──────────────────┘                                      │
└─────────────────────────────────────────────────────────────┘
```

### コンポーネント一覧

| ID | コンポーネント | 責務 | 対応要件 |
|----|---------------|------|----------|
| DES-005-C1 | VersionDisplay | バージョン表示（通常/詳細） | REQ-BUGFIX-005-01, 005-05 |
| DES-005-C2 | DependencyVersionCollector | 依存パッケージのバージョン収集 | REQ-BUGFIX-005-04 |
| DES-005-C3 | VersionMismatchDetector | config.jsonとの不一致検出 | REQ-BUGFIX-005-03 |
| DES-005-C4 | CacheGuidance | npxキャッシュクリア方法の案内 | REQ-BUGFIX-005-02 |

### インターフェース定義

```typescript
// DES-005-C1: VersionDisplay
interface VersionInfo {
  version: string;
  verbose?: DependencyVersions;
}

interface DependencyVersions {
  core: string;
  mcpServer: string;
  knowledge: string;
  policy: string;
  decisions: string;
}

function displayVersion(verbose: boolean): void;

// DES-005-C3: VersionMismatchDetector
interface MismatchResult {
  hasMismatch: boolean;
  expected: string;
  actual: string;
}

function checkVersionMismatch(configPath: string): MismatchResult;
```

### 変更対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `packages/core/src/cli/base.ts` | カスタムversionアクション実装 |
| `packages/core/src/version.ts` | DependencyVersionCollector追加 |

---

## DES-BUGFIX-006: テスト生成機能統合

### C4 Component Diagram

```
┌─────────────────────────────────────────────────────────────┐
│              codegen generate --with-tests                   │
│                                                              │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │ CodegenCommand   │─────▶│ TestIntegrator   │            │
│  │                  │      │                  │            │
│  │ --with-tests     │      │ - integrate()    │            │
│  └────────┬─────────┘      └────────┬─────────┘            │
│           │                         │                       │
│           ▼                         ▼                       │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │ UnitTestGenerator│◀─────│ TestFileNamer    │            │
│  │ (existing)       │      │                  │            │
│  │                  │      │ - getName()      │            │
│  │ - generate()     │      │ - getPath()      │            │
│  └──────────────────┘      └──────────────────┘            │
└─────────────────────────────────────────────────────────────┘
```

### コンポーネント一覧

| ID | コンポーネント | 責務 | 対応要件 |
|----|---------------|------|----------|
| DES-006-C1 | TestIntegrator | UnitTestGeneratorとの統合 | REQ-BUGFIX-006-01, 006-02 |
| DES-006-C2 | TestFileNamer | テストファイル命名・配置 | REQ-BUGFIX-006-03 |
| DES-006-C3 | TestCoverageSpec | カバレッジ対象の決定 | REQ-BUGFIX-006-04 |

### インターフェース定義

```typescript
// DES-006-C1: TestIntegrator
interface TestGenerationOptions {
  withTests: boolean;
  testDir: 'same' | '__tests__';
  framework: 'vitest' | 'jest';
}

function integrateTestGeneration(
  component: GeneratedCode,
  options: TestGenerationOptions
): GeneratedCode[];

// DES-006-C2: TestFileNamer  
function getTestFileName(componentName: string): string;
function getTestFilePath(componentPath: string, testDir: 'same' | '__tests__'): string;
```

### 変更対象ファイル

| ファイル | 変更内容 |
|----------|----------|
| `packages/core/src/cli/commands/codegen.ts` | `--with-tests`オプション、TestIntegrator呼び出し |
| `packages/core/src/codegen/index.ts` | TestIntegratorエクスポート |

---

## 設計パターン適用

| パターン | 適用箇所 | 理由 |
|---------|---------|------|
| Strategy | PatternDetector | 複数のパターン検出戦略を切り替え可能に |
| Factory | SkeletonGenerator | ファイル種別に応じた生成ロジック |
| Adapter | TestIntegrator | 既存UnitTestGeneratorとの統合 |
| Decorator | TraceabilityInjector | 生成コードへのメタデータ付与 |

---

## 非機能要件

| 項目 | 要件 |
|------|------|
| パフォーマンス | scaffold/codegen完了まで5秒以内 |
| 後方互換性 | 既存CLI引数・API署名を維持 |
| テスト容易性 | 各コンポーネントをモック可能に設計 |

---

## 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-14 | ✅ |
| レビュアー | | | |
| 承認者 | | | |

---

## 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-14 | 初版作成 | AI Agent |
