# MUSUBIX v1.5.0 Design Specification

**Version**: 1.5.0
**Status**: Reviewed
**Last Updated**: 2025-01-05
**Based On**: REQ-v1.5.0.md
**Review Date**: 2025-01-05

---

## C4 Model: Context Level

### System Context

```
┌─────────────────────────────────────────────────────────────────┐
│                        External Context                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────┐    ┌────────────────────────┐    ┌──────────────┐ │
│  │Developer │───▶│      MUSUBIX v1.5      │◀───│Pattern Repo  │ │
│  │  (User)  │    │  Neuro-Symbolic AI     │    │  (External)  │ │
│  └──────────┘    │  Integration System    │    └──────────────┘ │
│                  └────────────────────────┘                      │
│                           │   ▲                                  │
│                           ▼   │                                  │
│                  ┌────────────────────────┐                      │
│                  │   File System / IDE    │                      │
│                  └────────────────────────┘                      │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## C4 Model: Container Level

### Containers

| Container | Technology | Responsibility |
|-----------|------------|----------------|
| **CLI Application** | Node.js/TypeScript | ユーザーインターフェース、コマンド処理 |
| **MCP Server** | Node.js/TypeScript | AIエージェント連携、ツール提供 |
| **Core Library** | TypeScript | ビジネスロジック、推論エンジン |
| **Pattern Library** | JSON/N3 Store | パターン永続化、知識グラフ |
| **Wake-Sleep Engine** | TypeScript | 学習サイクル制御 |

```
┌─────────────────────────────────────────────────────────────────┐
│                      MUSUBIX v1.5 System                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │     CLI      │────▶│  Core Lib    │◀───▶│  MCP Server      │ │
│  │ Application  │     │  (Engine)    │     │  (AI Interface)  │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│         │                    │                      │            │
│         │                    ▼                      │            │
│         │            ┌──────────────┐               │            │
│         │            │ Wake-Sleep   │               │            │
│         │            │   Engine     │               │            │
│         │            └──────────────┘               │            │
│         │                    │                      │            │
│         ▼                    ▼                      ▼            │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │                    Pattern Library                           ││
│  │              (N3 Store + JSON Files)                         ││
│  └─────────────────────────────────────────────────────────────┘│
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## C4 Model: Component Level

### Feature 1: Real-time Pattern Learning

#### DES-LEARN-010: Real-time Learning Architecture

**Pattern**: Observer + Event Sourcing

```
┌─────────────────────────────────────────────────────────────────┐
│                Real-time Learning Components                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │FileWatcher   │────▶│StreamProcessor│───▶│PatternExtractor  │ │
│  │(fs.watch)    │     │(EventEmitter) │     │(AST Analysis)    │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│                              │                      │            │
│                              ▼                      ▼            │
│                       ┌──────────────┐     ┌──────────────────┐ │
│                       │FeedbackQueue │     │IncrementalUpdater│ │
│                       │(Non-blocking)│     │(Delta Update)    │ │
│                       └──────────────┘     └──────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

| Component | Responsibility | REQ Reference |
|-----------|---------------|---------------|
| **FileWatcher** | ファイル変更の監視 | REQ-LEARN-011 |
| **StreamProcessor** | イベントストリーム処理 | REQ-LEARN-014 |
| **PatternExtractor** | パターン抽出（AST解析） | REQ-LEARN-010 |
| **FeedbackQueue** | 非同期フィードバック収集 | REQ-LEARN-013 |
| **IncrementalUpdater** | 差分パターン更新 | REQ-LEARN-012 |

#### Interface Definitions

```typescript
// DES-LEARN-010: FileWatcher Interface
interface FileWatcher {
  watch(paths: string[]): void;
  onFileChange(callback: (event: FileChangeEvent) => void): void;
  stop(): void;
}

interface FileChangeEvent {
  path: string;
  type: 'create' | 'modify' | 'delete';
  timestamp: number;
  content?: string;
}

// DES-LEARN-011: StreamProcessor Interface (500ms SLA)
interface StreamProcessor {
  process(event: FileChangeEvent): Promise<ProcessResult>;
  getLatency(): number; // Must be < 500ms
}

// DES-LEARN-013: FeedbackQueue Interface (100ms SLA)
interface FeedbackQueue {
  enqueue(feedback: Feedback): void; // Non-blocking, < 100ms
  dequeue(): Feedback | undefined;
  size(): number;
}

// DES-LEARN-014: EventStream Interface (1000 events/sec)
interface EventStream {
  emit(event: PatternEvent): void;
  subscribe(handler: (event: PatternEvent) => void): Subscription;
  getThroughput(): number; // Must be >= 1000/sec
}
```

---

### Feature 2: Pattern Sharing

#### DES-SHARE-001: Pattern Export/Import Architecture

**Pattern**: Strategy + Factory

```
┌─────────────────────────────────────────────────────────────────┐
│                 Pattern Sharing Components                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │PatternExporter│───▶│DataSanitizer │────▶│JSONSerializer    │ │
│  │              │     │(Privacy)     │     │(Standard Format) │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│                                                                  │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │PatternImporter│◀───│OntologyValidator│◀──│ConflictResolver │ │
│  │              │     │(Constraint)  │     │(Strategy)        │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

| Component | Responsibility | REQ Reference |
|-----------|---------------|---------------|
| **PatternExporter** | パターンエクスポート | REQ-SHARE-001 |
| **PatternImporter** | パターンインポート | REQ-SHARE-002 |
| **DataSanitizer** | 機密データ除去 | REQ-SHARE-004 |
| **OntologyValidator** | オントロジー制約検証 | REQ-SHARE-003 |
| **ConflictResolver** | 競合解決戦略 | REQ-SHARE-005 |

#### Interface Definitions

```typescript
// DES-SHARE-001: PatternExporter Interface
interface PatternExporter {
  export(patterns: Pattern[], options?: ExportOptions): string; // JSON format
}

interface ExportOptions {
  sanitize: boolean; // REQ-SHARE-004
  format: 'json' | 'n3';
}

// DES-SHARE-002: PatternImporter Interface
interface PatternImporter {
  import(data: string): Promise<ImportResult>;
  validate(data: string): ValidationResult; // REQ-SHARE-003
}

// DES-SHARE-005: ConflictResolver Interface
interface ConflictResolver {
  resolve(conflicts: Conflict[]): Promise<Resolution>;
  setStrategy(strategy: 'keep-local' | 'keep-remote' | 'merge' | 'prompt'): void;
}
```

---

### Feature 3: Advanced Inference

#### DES-ONTO-010: OWL 2 RL Reasoning Architecture

**Pattern**: Chain of Responsibility + Visitor

```
┌─────────────────────────────────────────────────────────────────┐
│               Advanced Inference Components                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │QueryEngine   │────▶│RuleEngine    │────▶│InferenceExecutor │ │
│  │              │     │(OWL 2 RL)    │     │(200ms SLA)       │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│         │                    │                      │            │
│         ▼                    ▼                      ▼            │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │ProgressMonitor│    │DatalogIntegrator│  │ExplanationGenerator│
│  │(500ms interval)│   │(100 rules max)│   │(Human-readable)  │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

| Component | Responsibility | REQ Reference |
|-----------|---------------|---------------|
| **QueryEngine** | クエリ解析・最適化 | REQ-ONTO-011 |
| **RuleEngine** | OWL 2 RLルール適用 | REQ-ONTO-010 |
| **InferenceExecutor** | 推論実行（200ms SLA） | REQ-ONTO-011 |
| **ProgressMonitor** | 進捗フィードバック | REQ-ONTO-012 |
| **DatalogIntegrator** | Datalogルール統合 | REQ-ONTO-014 |
| **ExplanationGenerator** | 説明生成 | REQ-ONTO-013 |

#### Interface Definitions

```typescript
// DES-ONTO-010: RuleEngine Interface (OWL 2 RL)
interface RuleEngine {
  loadRules(rules: OWLRule[]): void;
  apply(graph: KnowledgeGraph): InferenceResult;
  getSupportedProfiles(): string[]; // ['OWL 2 RL']
}

// DES-ONTO-011: InferenceExecutor Interface (200ms SLA)
interface InferenceExecutor {
  execute(query: Query, graph: KnowledgeGraph): Promise<QueryResult>;
  getExecutionTime(): number; // Must be < 200ms for 10k triples
}

// DES-ONTO-012: ProgressMonitor Interface (500ms interval)
interface ProgressMonitor {
  onProgress(callback: (progress: Progress) => void): void;
  setInterval(ms: number): void; // Default: 500ms
}

// DES-ONTO-013: ExplanationGenerator Interface
interface ExplanationGenerator {
  explain(result: InferenceResult): string; // Human-readable
  getReasoningChain(): ReasoningStep[];
}

// DES-ONTO-014: DatalogIntegrator Interface (100 rules max)
interface DatalogIntegrator {
  loadRules(rules: DatalogRule[]): void; // Max 100 rules
  integrate(engine: RuleEngine): void;
  getRuleCount(): number;
}
```

---

### Feature 4: Interactive CLI Mode

#### DES-CLI-010: REPL Architecture

**Pattern**: Command + Interpreter

```
┌─────────────────────────────────────────────────────────────────┐
│                 Interactive CLI Components                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │REPLController│────▶│CommandParser │────▶│CommandExecutor   │ │
│  │(1s startup)  │     │              │     │                  │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│         │                                          │            │
│         ▼                                          ▼            │
│  ┌──────────────┐                          ┌──────────────────┐ │
│  │AutoCompleter │                          │HistoryManager    │ │
│  │(50ms response)│                         │(1000 entries)    │ │
│  └──────────────┘                          └──────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

| Component | Responsibility | REQ Reference |
|-----------|---------------|---------------|
| **REPLController** | REPL起動・制御 | REQ-CLI-010 |
| **AutoCompleter** | コマンド補完（50ms） | REQ-CLI-011, REQ-CLI-013 |
| **HistoryManager** | 履歴管理（1000件） | REQ-CLI-012 |

#### Interface Definitions

```typescript
// DES-CLI-010: REPLController Interface (1s startup)
interface REPLController {
  start(): Promise<void>; // Must complete < 1s
  stop(): void;
  isRunning(): boolean;
}

// DES-CLI-011: AutoCompleter Interface (50ms response)
interface AutoCompleter {
  complete(input: string): Completion[]; // Must respond < 50ms
  registerCommands(commands: CommandDefinition[]): void;
}

// DES-CLI-012: HistoryManager Interface (1000 entries)
interface HistoryManager {
  add(command: string): void;
  search(query: string): string[];
  getAll(): string[]; // Max 1000 entries
  clear(): void;
}
```

---

### Feature 5: Performance Optimization

#### DES-PERF-001: Performance Architecture

**Pattern**: Lazy Initialization + Cache Aside

```
┌─────────────────────────────────────────────────────────────────┐
│              Performance Optimization Components                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────────┐ │
│  │LazyLoader    │────▶│CacheManager  │────▶│ParallelProcessor │ │
│  │              │     │(500MB limit) │     │(4+ threads)      │ │
│  └──────────────┘     └──────────────┘     └──────────────────┘ │
│                              │                                   │
│                              ▼                                   │
│                       ┌──────────────┐                           │
│                       │AsyncRefresher│                           │
│                       │(5min TTL)    │                           │
│                       └──────────────┘                           │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

| Component | Responsibility | REQ Reference |
|-----------|---------------|---------------|
| **LazyLoader** | 遅延読み込み | REQ-PERF-001 |
| **CacheManager** | キャッシュ管理（500MB上限） | REQ-PERF-002, REQ-PERF-004 |
| **ParallelProcessor** | 並列処理（4+スレッド） | REQ-PERF-003 |
| **AsyncRefresher** | 非同期リフレッシュ（5分TTL） | REQ-PERF-005 |

#### Interface Definitions

```typescript
// DES-PERF-001: LazyLoader Interface
interface LazyLoader<T> {
  load(): Promise<T>;
  isLoaded(): boolean;
  unload(): void;
}

// DES-PERF-002: CacheManager Interface (500MB limit)
interface CacheManager {
  get<T>(key: string): T | undefined;
  set<T>(key: string, value: T, ttl?: number): void;
  getMemoryUsage(): number; // Must be < 500MB
  evict(key: string): void;
}

// DES-PERF-003: ParallelProcessor Interface (4+ threads)
interface ParallelProcessor {
  process<T, R>(items: T[], processor: (item: T) => R): Promise<R[]>;
  setWorkerCount(count: number): void; // Min 4 for 10k+ files
  getWorkerCount(): number;
}

// DES-PERF-005: AsyncRefresher Interface (5min TTL)
interface AsyncRefresher {
  scheduleRefresh(key: string, ttl: number): void; // Default: 5min
  onExpire(callback: (key: string) => void): void;
  refresh(key: string): Promise<void>; // Async
}
```

---

## Design Patterns Applied

| Pattern | Application | Rationale |
|---------|-------------|-----------|
| **Observer** | FileWatcher → StreamProcessor | ファイル変更の非同期通知 |
| **Event Sourcing** | StreamProcessor | イベントベースの状態管理 |
| **Strategy** | ConflictResolver | 競合解決戦略の切り替え |
| **Factory** | PatternExporter/Importer | フォーマット別の生成 |
| **Chain of Responsibility** | QueryEngine → RuleEngine → Executor | 推論パイプライン |
| **Command** | REPLController | コマンドの実行・履歴管理 |
| **Lazy Initialization** | LazyLoader | 遅延読み込みによるメモリ節約 |
| **Cache Aside** | CacheManager | キャッシュ戦略 |

---

## Traceability Matrix

| Requirement | Design Component | Interface |
|-------------|------------------|-----------|
| REQ-LEARN-010 | PatternExtractor | - |
| REQ-LEARN-011 | FileWatcher, StreamProcessor | StreamProcessor.process() |
| REQ-LEARN-012 | IncrementalUpdater | - |
| REQ-LEARN-013 | FeedbackQueue | FeedbackQueue.enqueue() |
| REQ-LEARN-014 | StreamProcessor | EventStream |
| REQ-SHARE-001 | PatternExporter | PatternExporter.export() |
| REQ-SHARE-002 | PatternImporter | PatternImporter.import() |
| REQ-SHARE-003 | OntologyValidator | PatternImporter.validate() |
| REQ-SHARE-004 | DataSanitizer | ExportOptions.sanitize |
| REQ-SHARE-005 | ConflictResolver | ConflictResolver.resolve() |
| REQ-ONTO-010 | RuleEngine | RuleEngine.apply() |
| REQ-ONTO-011 | InferenceExecutor | InferenceExecutor.execute() |
| REQ-ONTO-012 | ProgressMonitor | ProgressMonitor.onProgress() |
| REQ-ONTO-013 | ExplanationGenerator | ExplanationGenerator.explain() |
| REQ-ONTO-014 | DatalogIntegrator | DatalogIntegrator.loadRules() |
| REQ-CLI-010 | REPLController | REPLController.start() |
| REQ-CLI-011 | AutoCompleter | AutoCompleter.complete() |
| REQ-CLI-012 | HistoryManager | HistoryManager.getAll() |
| REQ-CLI-013 | AutoCompleter | AutoCompleter.complete() |
| REQ-PERF-001 | LazyLoader | LazyLoader.load() |
| REQ-PERF-002 | CacheManager | CacheManager.set() |
| REQ-PERF-003 | ParallelProcessor | ParallelProcessor.process() |
| REQ-PERF-004 | CacheManager | CacheManager.getMemoryUsage() |
| REQ-PERF-005 | AsyncRefresher | AsyncRefresher.scheduleRefresh() |

---

## Non-Functional Requirements

| NFR | Target | Monitoring |
|-----|--------|------------|
| **Latency (Learning)** | < 500ms | StreamProcessor.getLatency() |
| **Latency (Feedback)** | < 100ms | FeedbackQueue timing |
| **Throughput (Stream)** | ≥ 1000/sec | EventStream.getThroughput() |
| **Latency (Inference)** | < 200ms | InferenceExecutor.getExecutionTime() |
| **Progress Interval** | ≤ 500ms | ProgressMonitor.setInterval() |
| **REPL Startup** | < 1s | REPLController.start() timing |
| **Auto-complete** | < 50ms | AutoCompleter.complete() timing |
| **Memory** | < 500MB | CacheManager.getMemoryUsage() |
| **History Size** | ≥ 1000 | HistoryManager.getAll().length |
| **Worker Threads** | ≥ 4 | ParallelProcessor.getWorkerCount() |
| **Cache TTL** | 5min | AsyncRefresher default |

---

## Quality Gates

### Phase 1 → Phase 2 移行基準（Foundation → Core Features）

| 基準 | 条件 | 検証方法 |
|------|------|----------|
| **設計完了** | 全コンポーネントのインターフェース定義完了 | DES-v1.5.0.md レビュー |
| **ADR承認** | 3件のADRがaccepted状態 | ADR status確認 |
| **テスト計画** | 全要件のテストケース設計完了 | TST-v1.5.0.md存在確認 |
| **依存関係** | 必要なパッケージのバージョン確定 | package.json確認 |

### Phase 2 → Phase 3 移行基準（Core Features → Integration）

| 基準 | 条件 | 検証方法 |
|------|------|----------|
| **P0実装完了** | REQ-LEARN-010〜014の実装完了 | ユニットテスト合格 |
| **カバレッジ** | P0機能の80%以上 | vitest --coverage |
| **性能目標** | 500ms, 100ms, 1000/sec達成 | ベンチマークテスト |
| **API安定** | 公開インターフェースの凍結 | TypeDoc生成確認 |

### Phase 3 → Phase 4 移行基準（Integration → Stabilization）

| 基準 | 条件 | 検証方法 |
|------|------|----------|
| **P1実装完了** | REQ-SHARE-*, REQ-ONTO-*の実装完了 | ユニットテスト合格 |
| **統合テスト** | E2Eテスト全合格 | npm run test:e2e |
| **ドキュメント** | APIリファレンス完成 | docs/API-REFERENCE.md更新 |
| **後方互換** | v1.4.x APIとの互換性確認 | 互換性テスト合格 |

### Phase 4 → リリース基準（Stabilization → Release）

| 基準 | 条件 | 検証方法 |
|------|------|----------|
| **全テスト合格** | 850+テスト全合格 | npm run test |
| **カバレッジ** | 全体40%以上 | vitest --coverage |
| **セキュリティ** | npm audit 脆弱性なし | npm audit |
| **ドキュメント** | CHANGELOG, README更新 | ドキュメントレビュー |
| **パフォーマンス** | 全NFR目標達成 | ベンチマークレポート |

---

## Architecture Decision Records

| ADR | タイトル | 状態 |
|-----|---------|------|
| [ADR-0001](../../docs/adr/0001-real-time-pattern-learning-architecture-for-v1-5-0.md) | Real-time Pattern Learning Architecture | accepted |
| [ADR-0002](../../docs/adr/0002-pattern-sharing-protocol-for-cross-team-collaborat.md) | Pattern Sharing Protocol | accepted |
| [ADR-0003](../../docs/adr/0003-owl-2-rl-implementation-strategy-for-advanced-infe.md) | OWL 2 RL Implementation Strategy | accepted |

---

## Next Steps

1. [x] ADR作成（3件） ✅
2. [x] 品質ゲート定義 ✅
3. [ ] 詳細設計（クラス図）
4. [ ] テスト計画作成
5. [ ] プロトタイプ実装

