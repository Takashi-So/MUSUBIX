# DES-PHASE2-001: Phase 2 Advanced Learning 設計ドキュメント

**バージョン**: 1.0  
**作成日**: 2026-01-08  
**ステータス**: Draft  
**トレーサビリティ**: REQ-PHASE2-001

---

## 1. 概要

Phase 2「Advanced Learning」の設計ドキュメント。3つのパッケージの詳細設計をC4モデルで記述する。

### 1.1 パッケージ構成

| パッケージ | 役割 | 要件トレース |
|-----------|------|-------------|
| `@nahisaho/musubix-library-learner` | DreamCoder式階層的抽象化 | REQ-LL-001〜004 |
| `@nahisaho/musubix-neural-search` | Neural誘導探索 | REQ-NS-001〜004 |
| `@nahisaho/musubix-synthesis` | プログラム合成DSL | REQ-SYN-001〜004 |

---

## 2. C4 Context Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           External Systems                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐               │
│  │  Developer   │    │   VS Code    │    │  CI/CD       │               │
│  │  (User)      │    │   Extension  │    │  Pipeline    │               │
│  └──────┬───────┘    └──────┬───────┘    └──────┬───────┘               │
│         │                   │                   │                        │
│         └───────────────────┴───────────────────┘                        │
│                             │                                            │
│                             ▼                                            │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                    MUSUBIX Phase 2 System                         │   │
│  │  ┌────────────────────────────────────────────────────────────┐  │   │
│  │  │  musubix-library-learner                                   │  │   │
│  │  │  (階層的抽象化・ライブラリ学習)                             │  │   │
│  │  └────────────────────────────────────────────────────────────┘  │   │
│  │                             │                                     │   │
│  │                             ▼                                     │   │
│  │  ┌────────────────────────────────────────────────────────────┐  │   │
│  │  │  musubix-neural-search                                     │  │   │
│  │  │  (Neural誘導探索・プルーニング)                            │  │   │
│  │  └────────────────────────────────────────────────────────────┘  │   │
│  │                             │                                     │   │
│  │                             ▼                                     │   │
│  │  ┌────────────────────────────────────────────────────────────┐  │   │
│  │  │  musubix-synthesis                                         │  │   │
│  │  │  (DSLベースプログラム合成)                                 │  │   │
│  │  └────────────────────────────────────────────────────────────┘  │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                             │                                            │
│                             ▼                                            │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                    Phase 1 Packages                               │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐            │   │
│  │  │ musubix-dfg  │  │ musubix-lean │  │ yata-scale   │            │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘            │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 3. Package 1: musubix-library-learner

### 3.1 Container Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      musubix-library-learner                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Abstraction Engine                            │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ PatternMiner  │  │ Abstractor    │  │ TypeAnalyzer  │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ パターン検出   │  │ 階層的抽象化   │  │ 型指向探索    │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Library Manager                               │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ LibraryStore  │  │ Consolidator  │  │ Pruner        │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ パターン保存   │  │ 統合・圧縮    │  │ 減衰・削除    │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    E-Graph Optimizer                             │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ EGraphBuilder │  │ EqualityRules │  │ Extractor     │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ E-graph構築   │  │ 等価性ルール   │  │ 最適表現抽出  │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Component Design

#### 3.2.1 AbstractionEngine

```typescript
// src/abstraction/index.ts

/**
 * パターンマイナー - コードからパターンを検出
 * REQ-LL-001: 階層的抽象化
 */
export interface PatternMiner {
  /** コードコーパスからパターンを抽出 */
  mine(corpus: CodeCorpus): Promise<PatternCandidate[]>;
  
  /** 頻度閾値の設定 */
  setMinOccurrences(count: number): void;
}

/**
 * 抽象化エンジン - パターンを階層的に抽象化
 * REQ-LL-001: 階層的抽象化
 */
export interface Abstractor {
  /** レベル1: 具体的パターン */
  extractConcretePatterns(candidates: PatternCandidate[]): ConcretePattern[];
  
  /** レベル2: パラメータ化テンプレート */
  parameterize(patterns: ConcretePattern[]): ParameterizedTemplate[];
  
  /** レベル3: 高次抽象概念 */
  generalize(templates: ParameterizedTemplate[]): AbstractConcept[];
}

/**
 * 型アナライザー - 型情報による探索空間削減
 * REQ-LL-003: 型指向探索
 */
export interface TypeAnalyzer {
  /** 型互換性チェック */
  isCompatible(source: TypeSignature, target: TypeSignature): boolean;
  
  /** 型ベースフィルタリング */
  filterByType(candidates: PatternCandidate[], expectedType: TypeSignature): PatternCandidate[];
  
  /** 型スコアリング */
  scoreByTypeMatch(candidate: PatternCandidate, context: TypeContext): number;
}
```

#### 3.2.2 LibraryManager

```typescript
// src/library/index.ts

/**
 * ライブラリストア - パターンの永続化
 * REQ-LL-002: ライブラリ成長
 */
export interface LibraryStore {
  /** パターン追加 */
  add(pattern: LearnedPattern): Promise<void>;
  
  /** パターン取得 */
  get(id: PatternId): Promise<LearnedPattern | null>;
  
  /** パターン検索 */
  search(query: PatternQuery): Promise<LearnedPattern[]>;
  
  /** 全パターン取得 */
  getAll(): Promise<LearnedPattern[]>;
}

/**
 * コンソリデーター - 類似パターンの統合
 * REQ-LL-002: ライブラリ成長
 */
export interface Consolidator {
  /** 類似パターンの検出 */
  findSimilar(patterns: LearnedPattern[]): SimilarityCluster[];
  
  /** クラスターの統合 */
  merge(cluster: SimilarityCluster): LearnedPattern;
  
  /** ライブラリ全体の統合 */
  consolidateLibrary(store: LibraryStore): Promise<ConsolidationReport>;
}

/**
 * プルーナー - 未使用パターンの削除
 * REQ-LL-002: ライブラリ成長
 */
export interface Pruner {
  /** 使用頻度に基づく減衰 */
  applyDecay(store: LibraryStore, decayRate: number): Promise<void>;
  
  /** 閾値以下のパターン削除 */
  prune(store: LibraryStore, threshold: number): Promise<PruneReport>;
}
```

#### 3.2.3 EGraphOptimizer

```typescript
// src/egraph/index.ts

/**
 * E-Graph - 等価性グラフ
 * REQ-LL-004: E-graph最適化
 */
export interface EGraph {
  /** ノード追加 */
  add(node: ENode): EClassId;
  
  /** 等価性マージ */
  merge(id1: EClassId, id2: EClassId): EClassId;
  
  /** 等価クラス取得 */
  getEClass(id: EClassId): EClass;
}

/**
 * 等価性ルール - 書き換えルール
 */
export interface EqualityRule {
  name: string;
  pattern: Pattern;
  replacement: Pattern;
  condition?: (match: Match) => boolean;
}

/**
 * E-Graphビルダー
 */
export interface EGraphBuilder {
  /** パターンからE-Graph構築 */
  build(patterns: LearnedPattern[]): EGraph;
  
  /** ルール適用（等価性飽和） */
  saturate(graph: EGraph, rules: EqualityRule[]): EGraph;
}

/**
 * 最適表現抽出器
 */
export interface Extractor {
  /** コスト関数に基づく最適表現抽出 */
  extract(graph: EGraph, costFn: CostFunction): OptimalExpression;
}
```

### 3.3 ディレクトリ構造

```
packages/library-learner/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── src/
│   ├── index.ts
│   ├── types.ts
│   ├── errors.ts
│   ├── abstraction/
│   │   ├── index.ts
│   │   ├── PatternMiner.ts
│   │   ├── Abstractor.ts
│   │   └── TypeAnalyzer.ts
│   ├── library/
│   │   ├── index.ts
│   │   ├── LibraryStore.ts
│   │   ├── Consolidator.ts
│   │   └── Pruner.ts
│   ├── egraph/
│   │   ├── index.ts
│   │   ├── EGraph.ts
│   │   ├── EGraphBuilder.ts
│   │   ├── EqualityRules.ts
│   │   └── Extractor.ts
│   └── LibraryLearner.ts      # 高レベルAPI
└── tests/
    ├── abstraction/
    ├── library/
    └── egraph/
```

---

## 4. Package 2: musubix-neural-search

### 4.1 Container Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      musubix-neural-search                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Neural Scorer                                 │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ EmbeddingModel│  │ BranchScorer  │  │ ContextEncoder│        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ 埋め込み生成   │  │ 分岐スコア    │  │ コンテキスト  │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Search Engine                                 │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ BeamSearch    │  │ BestFirst     │  │ PriorityQueue │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ ビーム探索    │  │ 最良優先探索   │  │ 優先度キュー  │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Learning Module                               │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ TrajectoryLog │  │ OnlineLearner │  │ ModelUpdater  │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ 探索履歴記録   │  │ オンライン学習 │  │ モデル更新    │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 4.2 Component Design

#### 4.2.1 NeuralScorer

```typescript
// src/scorer/index.ts

/**
 * 埋め込みモデル - コード/仕様の埋め込み生成
 * REQ-NS-001: 分岐スコアリング
 */
export interface EmbeddingModel {
  /** コードの埋め込み生成 */
  embedCode(code: string): Promise<Float32Array>;
  
  /** 仕様の埋め込み生成 */
  embedSpec(spec: Specification): Promise<Float32Array>;
  
  /** 類似度計算 */
  similarity(a: Float32Array, b: Float32Array): number;
}

/**
 * 分岐スコアラー - 探索分岐のスコアリング
 * REQ-NS-001: 分岐スコアリング
 */
export interface BranchScorer {
  /** 分岐の成功確率を予測 */
  score(branch: SearchBranch, context: SearchContext): Promise<number>;
  
  /** バッチスコアリング */
  scoreBatch(branches: SearchBranch[], context: SearchContext): Promise<number[]>;
}

/**
 * コンテキストエンコーダー - 探索コンテキストのエンコード
 */
export interface ContextEncoder {
  /** 現在の探索状態をエンコード */
  encode(state: SearchState): Float32Array;
  
  /** 仕様をエンコード */
  encodeSpec(spec: Specification): Float32Array;
}
```

#### 4.2.2 SearchEngine

```typescript
// src/search/index.ts

/**
 * 探索ノード
 */
export interface SearchNode {
  id: string;
  state: SearchState;
  score: number;
  parent: SearchNode | null;
  children: SearchNode[];
  depth: number;
}

/**
 * ビーム探索 - ビーム幅制限付き探索
 * REQ-NS-002: 探索優先順位付け
 */
export interface BeamSearch {
  /** ビーム探索実行 */
  search(
    initial: SearchState,
    goal: GoalPredicate,
    expand: ExpandFunction,
    options: BeamSearchOptions
  ): Promise<SearchResult>;
}

export interface BeamSearchOptions {
  beamWidth: number;
  maxDepth: number;
  timeout: number;
  scorer: BranchScorer;
}

/**
 * 最良優先探索
 * REQ-NS-002: 探索優先順位付け
 */
export interface BestFirstSearch {
  /** 最良優先探索実行 */
  search(
    initial: SearchState,
    goal: GoalPredicate,
    expand: ExpandFunction,
    heuristic: HeuristicFunction
  ): Promise<SearchResult>;
}

/**
 * プルーニングマネージャー
 * REQ-NS-003: 学習ベースプルーニング
 */
export interface PruningManager {
  /** プルーニング判定 */
  shouldPrune(node: SearchNode, context: SearchContext): boolean;
  
  /** 閾値の動的調整 */
  adjustThreshold(feedback: PruneFeedback): void;
  
  /** 誤プルーニング検出 */
  detectFalsePositive(prunedNode: SearchNode, actualResult: boolean): void;
}
```

#### 4.2.3 LearningModule

```typescript
// src/learning/index.ts

/**
 * 探索軌跡 - 探索履歴の記録
 * REQ-NS-004: 探索履歴学習
 */
export interface SearchTrajectory {
  id: string;
  spec: Specification;
  nodes: SearchNode[];
  success: boolean;
  duration: number;
  timestamp: Date;
}

/**
 * 軌跡ログ - 探索履歴の永続化
 */
export interface TrajectoryLog {
  /** 軌跡の保存 */
  save(trajectory: SearchTrajectory): Promise<void>;
  
  /** 軌跡の取得 */
  get(id: string): Promise<SearchTrajectory | null>;
  
  /** 成功軌跡の取得 */
  getSuccessful(limit: number): Promise<SearchTrajectory[]>;
}

/**
 * オンライン学習器 - 探索からの継続的学習
 * REQ-NS-004: 探索履歴学習
 */
export interface OnlineLearner {
  /** 軌跡からの学習 */
  learn(trajectory: SearchTrajectory): Promise<void>;
  
  /** バッチ学習 */
  learnBatch(trajectories: SearchTrajectory[]): Promise<void>;
  
  /** 学習進捗取得 */
  getProgress(): LearningProgress;
}

/**
 * モデル更新器 - スコアラーモデルの更新
 */
export interface ModelUpdater {
  /** モデルのファインチューニング */
  update(model: EmbeddingModel, data: TrainingData): Promise<EmbeddingModel>;
  
  /** チェックポイント保存 */
  saveCheckpoint(model: EmbeddingModel, path: string): Promise<void>;
  
  /** チェックポイント復元 */
  loadCheckpoint(path: string): Promise<EmbeddingModel>;
}
```

### 4.3 ディレクトリ構造

```
packages/neural-search/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── src/
│   ├── index.ts
│   ├── types.ts
│   ├── errors.ts
│   ├── scorer/
│   │   ├── index.ts
│   │   ├── EmbeddingModel.ts
│   │   ├── BranchScorer.ts
│   │   └── ContextEncoder.ts
│   ├── search/
│   │   ├── index.ts
│   │   ├── BeamSearch.ts
│   │   ├── BestFirstSearch.ts
│   │   ├── PriorityQueue.ts
│   │   └── PruningManager.ts
│   ├── learning/
│   │   ├── index.ts
│   │   ├── TrajectoryLog.ts
│   │   ├── OnlineLearner.ts
│   │   └── ModelUpdater.ts
│   └── NeuralSearch.ts        # 高レベルAPI
└── tests/
    ├── scorer/
    ├── search/
    └── learning/
```

---

## 5. Package 3: musubix-synthesis

### 5.1 Container Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      musubix-synthesis                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    DSL Framework                                 │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ DSLBuilder    │  │ TypeSystem    │  │ Semantics     │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ DSL定義       │  │ 型システム    │  │ 実行意味論    │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Synthesis Engine                              │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ PBESynthesizer│  │ WitnessEngine │  │ VersionSpace  │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ 例示合成      │  │ Witness関数   │  │ バージョン空間│        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Rule Learning                                 │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐        │    │
│  │  │ RuleExtractor │  │ RuleLibrary   │  │ MetaLearner   │        │    │
│  │  │               │  │               │  │               │        │    │
│  │  │ ルール抽出    │  │ ルールライブラリ│  │ メタ学習      │        │    │
│  │  └───────────────┘  └───────────────┘  └───────────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 5.2 Component Design

#### 5.2.1 DSLFramework

```typescript
// src/dsl/index.ts

/**
 * DSL演算子定義
 * REQ-SYN-001: DSL定義フレームワーク
 */
export interface Operator {
  name: string;
  inputTypes: TypeSignature[];
  outputType: TypeSignature;
  semantics: (...args: any[]) => any;
}

/**
 * DSLビルダー - 宣言的DSL定義
 * REQ-SYN-001: DSL定義フレームワーク
 */
export interface DSLBuilder {
  /** 演算子追加 */
  addOperator(
    name: string,
    inputTypes: TypeSignature[],
    outputType: TypeSignature,
    semantics?: (...args: any[]) => any
  ): DSLBuilder;
  
  /** 定数追加 */
  addConstant(name: string, type: TypeSignature, value: any): DSLBuilder;
  
  /** 型追加 */
  addType(name: string, definition: TypeDefinition): DSLBuilder;
  
  /** DSL構築 */
  build(): DSL;
}

/**
 * DSL - ドメイン固有言語
 */
export interface DSL {
  name: string;
  operators: Map<string, Operator>;
  constants: Map<string, Constant>;
  types: Map<string, TypeDefinition>;
  
  /** プログラムの実行 */
  execute(program: Program, input: any): any;
  
  /** プログラムの検証 */
  validate(program: Program): ValidationResult;
}

/**
 * 型システム
 */
export interface TypeSystem {
  /** 型チェック */
  check(program: Program): TypeCheckResult;
  
  /** 型推論 */
  infer(expression: Expression): TypeSignature;
  
  /** 型互換性 */
  isSubtype(sub: TypeSignature, sup: TypeSignature): boolean;
}
```

#### 5.2.2 SynthesisEngine

```typescript
// src/synthesis/index.ts

/**
 * 入出力例
 */
export interface Example {
  input: any;
  output: any;
}

/**
 * PBE合成器 - 例示からの合成
 * REQ-SYN-003: 例示合成 (PBE)
 */
export interface PBESynthesizer {
  /** 例示からプログラム合成 */
  synthesize(
    dsl: DSL,
    examples: Example[],
    options?: SynthesisOptions
  ): Promise<SynthesisResult>;
  
  /** 曖昧性解決 */
  disambiguate(
    candidates: Program[],
    additionalExample: Example
  ): Program[];
}

export interface SynthesisOptions {
  maxDepth: number;
  timeout: number;
  useNeuralGuidance: boolean;
  neuralSearch?: NeuralSearch;
}

export interface SynthesisResult {
  success: boolean;
  program?: Program;
  candidates?: Program[];
  duration: number;
  searchNodes: number;
}

/**
 * Witness関数 - 演繹的合成
 * REQ-SYN-002: Witness関数
 */
export interface WitnessFunction {
  operator: string;
  
  /** 出力仕様から入力仕様を逆算 */
  inverse(
    outputSpec: Specification,
    argIndex: number
  ): Specification[];
}

/**
 * Witnessエンジン
 */
export interface WitnessEngine {
  /** Witness関数の登録 */
  register(witness: WitnessFunction): void;
  
  /** 仕様分解 */
  decompose(
    operator: string,
    outputSpec: Specification
  ): DecomposedSpec[];
  
  /** 演繹的合成 */
  synthesizeDeductively(
    dsl: DSL,
    spec: Specification
  ): Promise<Program>;
}

/**
 * バージョン空間 - 候補プログラムの効率的表現
 */
export interface VersionSpace {
  /** 空間への追加 */
  add(program: Program): void;
  
  /** 例による絞り込み */
  refine(example: Example): VersionSpace;
  
  /** 単一プログラムへの収束判定 */
  isConverged(): boolean;
  
  /** プログラム取得 */
  getProgram(): Program | null;
  
  /** 候補数取得 */
  size(): number;
}
```

#### 5.2.3 RuleLearning

```typescript
// src/rules/index.ts

/**
 * 合成ルール
 * REQ-SYN-004: 合成ルール学習
 */
export interface SynthesisRule {
  id: string;
  name: string;
  pattern: SpecPattern;
  template: ProgramTemplate;
  confidence: number;
  usageCount: number;
}

/**
 * ルール抽出器 - 成功パターンからのルール抽出
 */
export interface RuleExtractor {
  /** 成功合成からルール抽出 */
  extract(
    spec: Specification,
    program: Program,
    searchTrace: SearchTrajectory
  ): SynthesisRule[];
  
  /** パターン一般化 */
  generalize(rules: SynthesisRule[]): SynthesisRule[];
}

/**
 * ルールライブラリ - ルールの永続化と検索
 */
export interface RuleLibrary {
  /** ルール追加 */
  add(rule: SynthesisRule): Promise<void>;
  
  /** 仕様にマッチするルール検索 */
  match(spec: Specification): Promise<SynthesisRule[]>;
  
  /** ルール使用記録 */
  recordUsage(ruleId: string, success: boolean): Promise<void>;
  
  /** 低信頼度ルールの削除 */
  prune(threshold: number): Promise<void>;
}

/**
 * メタ学習器 - ルールの継続的改善
 */
export interface MetaLearner {
  /** 合成結果からの学習 */
  learn(result: SynthesisResult, usedRules: SynthesisRule[]): Promise<void>;
  
  /** ルール信頼度の更新 */
  updateConfidence(ruleId: string, success: boolean): Promise<void>;
  
  /** 新ルールの提案 */
  suggestRules(library: RuleLibrary): Promise<SynthesisRule[]>;
}
```

### 5.3 ディレクトリ構造

```
packages/synthesis/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── src/
│   ├── index.ts
│   ├── types.ts
│   ├── errors.ts
│   ├── dsl/
│   │   ├── index.ts
│   │   ├── DSLBuilder.ts
│   │   ├── DSL.ts
│   │   ├── TypeSystem.ts
│   │   └── Semantics.ts
│   ├── synthesis/
│   │   ├── index.ts
│   │   ├── PBESynthesizer.ts
│   │   ├── WitnessEngine.ts
│   │   ├── VersionSpace.ts
│   │   └── Enumerator.ts
│   ├── rules/
│   │   ├── index.ts
│   │   ├── RuleExtractor.ts
│   │   ├── RuleLibrary.ts
│   │   └── MetaLearner.ts
│   └── ProgramSynthesizer.ts  # 高レベルAPI
└── tests/
    ├── dsl/
    ├── synthesis/
    └── rules/
```

---

## 6. 高レベルAPI設計

### 6.1 LibraryLearner

```typescript
// packages/library-learner/src/LibraryLearner.ts

import type { LibraryStore, Abstractor, TypeAnalyzer, EGraph } from './types';

export interface LibraryLearnerConfig {
  abstractionLevels: number;
  minOccurrences: number;
  decayRate: number;
  pruneThreshold: number;
  useEGraph: boolean;
}

export class LibraryLearner {
  constructor(config: LibraryLearnerConfig);
  
  /** コードコーパスからの学習 */
  async learnFromCorpus(corpus: CodeCorpus): Promise<LearnResult>;
  
  /** 増分学習 */
  async learnIncremental(code: string): Promise<void>;
  
  /** ライブラリを使った合成 */
  async synthesize(
    spec: Specification,
    options?: SynthesizeOptions
  ): Promise<SynthesisResult>;
  
  /** ライブラリ取得 */
  getLibrary(): LibraryStore;
  
  /** 統計情報 */
  getStats(): LibraryStats;
}
```

### 6.2 NeuralSearch

```typescript
// packages/neural-search/src/NeuralSearch.ts

import type { EmbeddingModel, BranchScorer, TrajectoryLog } from './types';

export interface NeuralSearchConfig {
  modelPath?: string;
  beamWidth: number;
  maxDepth: number;
  pruneThreshold: number;
  enableLearning: boolean;
}

export class NeuralSearch {
  constructor(config: NeuralSearchConfig);
  
  /** Neural誘導探索 */
  async search(
    initial: SearchState,
    goal: GoalPredicate,
    expand: ExpandFunction
  ): Promise<SearchResult>;
  
  /** 分岐スコアリング */
  async scoreBranches(
    branches: SearchBranch[],
    context: SearchContext
  ): Promise<number[]>;
  
  /** 探索からの学習 */
  async learnFromTrajectory(trajectory: SearchTrajectory): Promise<void>;
  
  /** モデル保存 */
  async saveModel(path: string): Promise<void>;
  
  /** モデル読み込み */
  async loadModel(path: string): Promise<void>;
}
```

### 6.3 ProgramSynthesizer

```typescript
// packages/synthesis/src/ProgramSynthesizer.ts

import type { DSL, WitnessEngine, RuleLibrary, NeuralSearch } from './types';

export interface SynthesizerConfig {
  dsl: DSL;
  maxDepth: number;
  timeout: number;
  useWitness: boolean;
  useNeuralGuidance: boolean;
  neuralSearch?: NeuralSearch;
  libraryLearner?: LibraryLearner;
}

export class ProgramSynthesizer {
  constructor(config: SynthesizerConfig);
  
  /** 例示からの合成 */
  async synthesizeFromExamples(
    examples: Example[]
  ): Promise<SynthesisResult>;
  
  /** 仕様からの合成 */
  async synthesizeFromSpec(
    spec: Specification
  ): Promise<SynthesisResult>;
  
  /** 曖昧性解決 */
  async disambiguate(
    candidates: Program[],
    example: Example
  ): Promise<Program[]>;
  
  /** 合成結果の検証 */
  async verify(
    program: Program,
    examples: Example[]
  ): Promise<VerificationResult>;
  
  /** ルールの学習 */
  async learnRules(
    result: SynthesisResult
  ): Promise<void>;
}
```

---

## 7. トレーサビリティマトリクス

| 要件ID | 設計コンポーネント | テストファイル |
|--------|------------------|--------------|
| REQ-LL-001 | PatternMiner, Abstractor | abstraction/*.test.ts |
| REQ-LL-002 | LibraryStore, Consolidator, Pruner | library/*.test.ts |
| REQ-LL-003 | TypeAnalyzer | abstraction/TypeAnalyzer.test.ts |
| REQ-LL-004 | EGraph, EGraphBuilder, Extractor | egraph/*.test.ts |
| REQ-NS-001 | EmbeddingModel, BranchScorer | scorer/*.test.ts |
| REQ-NS-002 | BeamSearch, BestFirstSearch | search/*.test.ts |
| REQ-NS-003 | PruningManager | search/PruningManager.test.ts |
| REQ-NS-004 | TrajectoryLog, OnlineLearner | learning/*.test.ts |
| REQ-SYN-001 | DSLBuilder, DSL, TypeSystem | dsl/*.test.ts |
| REQ-SYN-002 | WitnessFunction, WitnessEngine | synthesis/Witness*.test.ts |
| REQ-SYN-003 | PBESynthesizer, VersionSpace | synthesis/*.test.ts |
| REQ-SYN-004 | RuleExtractor, RuleLibrary, MetaLearner | rules/*.test.ts |

---

## 8. 技術的決定事項

### 8.1 ADR-001: Embeddingモデル選定

**決定**: `@xenova/transformers` (ONNX Runtime) を使用

**理由**:
- Node.js環境でのローカル実行
- 軽量モデル（<100MB）
- GPUオプショナル

**代替案**: OpenAI Embeddings API（却下：レイテンシ、コスト）

### 8.2 ADR-002: E-Graph実装

**決定**: 独自軽量実装

**理由**:
- egg (Rust) はNode.jsバインディング複雑
- パターン最適化用途に特化

**代替案**: egg-wasm（却下：サイズ、複雑性）

### 8.3 ADR-003: 永続化

**決定**: `better-sqlite3` + JSON

**理由**:
- 既存yata-localとの一貫性
- 軽量、高速

---

## 9. 次のステップ

1. **設計レビュー**: 本ドキュメントのレビュー
2. **実装フェーズ1**: musubix-library-learner (100テスト)
3. **実装フェーズ2**: musubix-neural-search (80テスト)
4. **実装フェーズ3**: musubix-synthesis (120テスト)
5. **統合テスト**: パッケージ間連携テスト

---

**承認**:

- [ ] 設計レビュー完了
- [ ] アーキテクチャ承認
- [ ] 実装開始承認

**次のステップ**: 実装開始（musubix-library-learner）
