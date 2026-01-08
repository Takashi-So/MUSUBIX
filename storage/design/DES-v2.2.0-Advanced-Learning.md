# MUSUBIX v2.2.0 設計書 - Advanced Learning Enhancement

| 項目 | 内容 |
|------|------|
| **ドキュメントID** | DES-v2.2.0-Advanced-Learning |
| **バージョン** | 1.1.0 |
| **作成日** | 2026-01-08 |
| **ステータス** | レビュー済み |
| **対応要件** | REQ-v2.2.0-Advanced-Learning |

---

## 1. 概要

### 1.1 設計方針

- **後方互換性**: 既存API（v2.1.x）との100%互換を維持
- **非破壊的追加**: 新機能は既存インターフェースの拡張として実装
- **段階的強化**: 既存REQ-LL-001〜004、REQ-NS-001、REQ-SYN-001を拡張
- **SOLID原則**: 単一責任、開放閉鎖、依存性逆転を遵守

### 1.2 影響範囲

| パッケージ | 変更ファイル（予定） | 変更種別 |
|-----------|-------------------|---------|
| `@nahisaho/musubix-library-learner` | 8ファイル追加、3ファイル修正 | 拡張 |
| `@nahisaho/musubix-neural-search` | 6ファイル追加、2ファイル修正 | 拡張 |
| `@nahisaho/musubix-synthesis` | 5ファイル追加、2ファイル修正 | 拡張 |
| `@nahisaho/musubix-core` | 2ファイル追加（オーケストレーション） | 新規 |

---

## 2. C4モデル - Context

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              External Systems                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌───────────┐    ┌───────────┐    ┌───────────┐    ┌───────────┐        │
│   │  Developer│    │   IDE     │    │  MCP      │    │  YATA KG  │        │
│   │  (User)   │    │ (VSCode)  │    │  Client   │    │           │        │
│   └─────┬─────┘    └─────┬─────┘    └─────┬─────┘    └─────┬─────┘        │
│         │                │                │                │              │
│         └────────────────┼────────────────┼────────────────┘              │
│                          │                │                               │
│                          ▼                ▼                               │
│         ┌─────────────────────────────────────────────────────────────┐   │
│         │                    MUSUBIX v2.2.0                           │   │
│         │                                                             │   │
│         │  ┌─────────────────────────────────────────────────────┐   │   │
│         │  │           Synthesis Orchestrator (NEW)              │   │   │
│         │  │  REQ-INT-101, REQ-INT-102                          │   │   │
│         │  └───────────────────┬─────────────────────────────────┘   │   │
│         │                      │                                     │   │
│         │    ┌─────────────────┼─────────────────┐                   │   │
│         │    │                 │                 │                   │   │
│         │    ▼                 ▼                 ▼                   │   │
│         │  ┌───────┐     ┌───────┐        ┌───────┐                 │   │
│         │  │Library│     │Neural │        │Synth- │                 │   │
│         │  │Learner│     │Search │        │esis   │                 │   │
│         │  │(v2.2) │     │(v2.2) │        │(v2.2) │                 │   │
│         │  └───────┘     └───────┘        └───────┘                 │   │
│         │                                                             │   │
│         └─────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. C4モデル - Container

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        MUSUBIX v2.2.0 Containers                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                     @nahisaho/musubix-core                          │   │
│  │  ┌──────────────────────────────────────────────────────────────┐   │   │
│  │  │  synthesis/                                                   │   │   │
│  │  │    SynthesisOrchestrator.ts  (NEW - REQ-INT-101)             │   │   │
│  │  │    PipelineConfig.ts         (NEW - REQ-INT-102)             │   │   │
│  │  │    SynthesisCLI.ts           (NEW - REQ-INT-104)             │   │   │
│  │  └──────────────────────────────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                      │                                      │
│         ┌────────────────────────────┼────────────────────────────┐        │
│         │                            │                            │        │
│         ▼                            ▼                            ▼        │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐        │
│  │ library-learner │    │  neural-search  │    │    synthesis    │        │
│  │    (v2.2.0)     │    │    (v2.2.0)     │    │    (v2.2.0)     │        │
│  ├─────────────────┤    ├─────────────────┤    ├─────────────────┤        │
│  │                 │    │                 │    │                 │        │
│  │ [既存]          │    │ [既存]          │    │ [既存]          │        │
│  │ PatternMiner    │    │ BeamSearch      │    │ PBESynthesizer  │        │
│  │ Abstractor      │    │ BranchScorer    │    │ Enumerator      │        │
│  │ EGraph          │    │ PruningManager  │    │ WitnessEngine   │        │
│  │ LibraryStore    │    │                 │    │ VersionSpace    │        │
│  │                 │    │                 │    │                 │        │
│  │ [NEW]           │    │ [NEW]           │    │ [NEW]           │        │
│  │ HierarchyMgr    │    │ AdaptiveBeam    │    │ WitnessEnhanced │        │
│  │ TypePruner      │    │ ContextScorer   │    │ MetaLearner     │        │
│  │ Compressor      │    │ EmbeddingCache  │    │ DSLExtender     │        │
│  │ VersionMgr      │    │ OnlineLearner   │    │ ExampleAnalyzer │        │
│  │ IncrementalUpd  │    │ TrajectoryLog   │    │ ExplainGen      │        │
│  │ MetricsExporter │    │ ModalFusion     │    │                 │        │
│  │                 │    │                 │    │                 │        │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 4. EPIC-LL: Library Learner Enhancement 設計

### 4.1 DES-LL-101: 階層的抽象化エンジン強化

**対応要件**: REQ-LL-101

#### コンポーネント設計

```typescript
// packages/library-learner/src/hierarchy/HierarchyManager.ts

/**
 * DES-LL-101: 階層的抽象化マネージャー
 * 
 * 既存クラス関係: LibraryLearner.extractPatterns() から委譲される新規コンポーネント
 * 依存: PatternMiner, Abstractor (既存)
 * 
 * 3レベル以上の階層的抽象化を管理
 * - Level 1: ConcretePattern (トークンレベル)
 * - Level 2: ParameterizedTemplate (式レベル)  
 * - Level 3: AbstractConcept (関数レベル)
 * - Level 4+: CompositeAbstraction (複合パターン) [NEW]
 */
export interface HierarchyManager {
  /** 階層レベルの追加 */
  addLevel(level: AbstractionLevel): void;
  
  /** コーパスから階層的抽象化を抽出 */
  extractHierarchy(corpus: CodeCorpus): Promise<HierarchyResult>;
  
  /** レベル間の昇格判定 */
  shouldPromote(pattern: LearnedPattern): boolean;
  
  /** 抽象化の深度を取得 */
  getDepth(): number;
}

export interface HierarchyResult {
  levels: Map<number, LearnedPattern[]>;
  promotions: PromotionRecord[];
  metrics: HierarchyMetrics;
}

export interface HierarchyMetrics {
  extractionTimeMs: number;
  patternsPerLevel: number[];
  compressionRatio: number;
}
```

#### シーケンス図

```
Developer          LibraryLearner      HierarchyManager     PatternMiner
    │                    │                    │                  │
    │ learnFromCorpus()  │                    │                  │
    │───────────────────>│                    │                  │
    │                    │ extractHierarchy() │                  │
    │                    │───────────────────>│                  │
    │                    │                    │ mine(level=1)    │
    │                    │                    │─────────────────>│
    │                    │                    │<─────────────────│
    │                    │                    │                  │
    │                    │                    │ [for each level] │
    │                    │                    │ promote()        │
    │                    │                    │─────────┐        │
    │                    │                    │<────────┘        │
    │                    │<───────────────────│                  │
    │                    │                    │                  │
    │<───────────────────│ LearnResult        │                  │
```

---

### 4.2 DES-LL-102: 型主導探索強化

**対応要件**: REQ-LL-102

#### コンポーネント設計

```typescript
// packages/library-learner/src/search/TypeDirectedPruner.ts

/**
 * DES-LL-102: 型主導探索による枝刈り
 * 
 * 型シグネチャを用いて探索空間を90%以上削減
 */
export interface TypeDirectedPruner {
  /** 型コンテキストを設定 */
  setContext(context: TypeContext): void;
  
  /** 候補を型で枝刈り */
  prune(candidates: Program[], targetType: TypeSignature): Program[];
  
  /** 枝刈り統計を取得 */
  getStats(): PruningStats;
}

export interface PruningStats {
  totalCandidates: number;
  prunedCandidates: number;
  reductionRate: number; // 目標: >= 0.90
}

/**
 * 型推論ルール
 */
export interface TypeInferenceRule {
  name: string;
  match: (expr: ASTNode) => boolean;
  infer: (expr: ASTNode, context: TypeContext) => TypeSignature | null;
}
```

---

### 4.3 DES-LL-103: 反復圧縮

**対応要件**: REQ-LL-103

```typescript
// packages/library-learner/src/library/IterativeCompressor.ts

/**
 * DES-LL-103: 反復圧縮アルゴリズム
 * 
 * 類似パターンをマージし、ライブラリサイズを30%以上削減
 */
export interface IterativeCompressor {
  /** 圧縮を実行 */
  compress(library: PatternLibrary): Promise<CompressionResult>;
  
  /** 類似度閾値を設定 */
  setSimilarityThreshold(threshold: number): void;
  
  /** 圧縮をトリガーすべきか判定 */
  shouldCompress(library: PatternLibrary): boolean;
}

export interface CompressionResult {
  originalSize: number;
  compressedSize: number;
  reductionRate: number; // 目標: >= 0.30
  mergedPatterns: MergeRecord[];
  coverage: number; // 目標: >= 0.95
}
```

---

### 4.4 DES-LL-104: E-graph等価性発見強化

**対応要件**: REQ-LL-104

```typescript
// packages/library-learner/src/egraph/RewriteRuleSet.ts

/**
 * DES-LL-104: E-graphリライトルールセット
 * 
 * 50種類以上のリライトルールをサポート
 */
export interface RewriteRuleSet {
  /** ルールを追加 */
  addRule(rule: RewriteRule): void;
  
  /** カテゴリ別ルールを取得 */
  getRulesByCategory(category: RuleCategory): RewriteRule[];
  
  /** 全ルールを適用 */
  applyAll(egraph: EGraph, maxIterations?: number): void;
}

export type RuleCategory = 
  | 'algebraic'    // 代数的: a + 0 = a, a * 1 = a
  | 'boolean'      // Boolean: !(!a) = a, a && true = a
  | 'string'       // 文字列: "".concat(s) = s
  | 'array'        // 配列: [].concat(arr) = arr
  | 'conditional'; // 条件: x ? a : a = a

export interface RewriteRule {
  id: string;
  category: RuleCategory;
  pattern: string;
  replacement: string;
  condition?: (bindings: Map<string, ASTNode>) => boolean;
}

// 50+ルールの例
export const BUILTIN_RULES: RewriteRule[] = [
  // Algebraic (15 rules)
  { id: 'add-zero', category: 'algebraic', pattern: '?a + 0', replacement: '?a' },
  { id: 'mul-one', category: 'algebraic', pattern: '?a * 1', replacement: '?a' },
  { id: 'mul-zero', category: 'algebraic', pattern: '?a * 0', replacement: '0' },
  // ... 12 more
  
  // Boolean (15 rules)
  { id: 'double-neg', category: 'boolean', pattern: '!(!?a)', replacement: '?a' },
  { id: 'and-true', category: 'boolean', pattern: '?a && true', replacement: '?a' },
  // ... 13 more
  
  // String (10 rules)
  { id: 'concat-empty', category: 'string', pattern: '"".concat(?s)', replacement: '?s' },
  // ... 9 more
  
  // Array (5 rules)
  // Conditional (5 rules)
];
```

---

### 4.5 DES-LL-105〜108: その他の設計

```typescript
// DES-LL-105: パターンバージョニング
// packages/library-learner/src/library/PatternVersionManager.ts
export interface PatternVersionManager {
  recordVersion(pattern: LearnedPattern): void;
  rollback(patternId: PatternId, version: number): Promise<LearnedPattern>;
  getHistory(patternId: PatternId): PatternVersion[];
}

// DES-LL-106: ドメイン特化抽象化
// packages/library-learner/src/domain/DomainAwareAbstractor.ts
export interface DomainAwareAbstractor {
  loadOntology(ontologyPath: string): Promise<void>;
  abstractWithDomain(pattern: PatternCandidate, domain: string): LearnedPattern;
}

// DES-LL-107: 増分学習
// packages/library-learner/src/incremental/IncrementalUpdater.ts
export interface IncrementalUpdater {
  update(diff: CodeDiff): Promise<UpdateResult>;
  isIncrementalPossible(diff: CodeDiff): boolean;
}

// DES-LL-108: メトリクス・可視化
// packages/library-learner/src/metrics/MetricsExporter.ts
export interface MetricsExporter {
  export(format: 'json' | 'markdown'): string;
  getMetrics(): LearningMetrics;
}
```

---

## 5. EPIC-NS: Neural Search Guidance 設計

### 5.1 DES-NS-101: 学習ベースプルーニング強化

**対応要件**: REQ-NS-101

```typescript
// packages/neural-search/src/pruning/LearnedPruningPolicy.ts

/**
 * DES-NS-101: 学習済みプルーニングポリシー
 * 
 * 探索ノード数を70%以上削減しながら品質を維持
 */
export interface LearnedPruningPolicy {
  /** ブランチを評価しプルーニング判定 */
  shouldPrune(branch: Branch, context: SearchContext): boolean;
  
  /** ポリシーを更新 */
  updatePolicy(trajectory: Trajectory, outcome: 'success' | 'failure'): void;
  
  /** プルーニング統計を取得 */
  getStats(): PruningPolicyStats;
}

export interface PruningPolicyStats {
  totalEvaluated: number;
  totalPruned: number;
  reductionRate: number; // 目標: >= 0.70
  solutionQuality: number; // 目標: >= 0.95
}

/**
 * プルーニング判定に使用する特徴量
 */
export interface PruningFeatures {
  syntaxValid: boolean;
  typeChecks: boolean;
  specSimilarity: number;
  novelty: number;
  depth: number;
  parentScore: number;
}
```

---

### 5.2 DES-NS-102: 適応的ビーム幅調整

**対応要件**: REQ-NS-102

```typescript
// packages/neural-search/src/search/AdaptiveBeamSearch.ts

/**
 * DES-NS-102: 適応的ビーム幅調整
 * 
 * 探索停滞時にビーム幅を動的に拡大
 */
export interface AdaptiveBeamConfig {
  initialBeamWidth: number;  // デフォルト: 10
  maxBeamWidth: number;      // デフォルト: 100
  stallThreshold: number;    // デフォルト: 10 (反復)
  expansionRate: number;     // デフォルト: 1.5 (50%増加)
}

export class AdaptiveBeamSearch extends BeamSearch {
  private config: AdaptiveBeamConfig;
  private lastBestScore: number = 0;
  private stallCount: number = 0;
  private currentBeamWidth: number;

  constructor(config: AdaptiveBeamConfig) {
    super();
    this.config = config;
    this.currentBeamWidth = config.initialBeamWidth;
  }

  /**
   * 探索停滞を検出しビーム幅を調整
   */
  protected adjustBeamWidth(currentBestScore: number): void {
    if (currentBestScore <= this.lastBestScore) {
      this.stallCount++;
      if (this.stallCount >= this.config.stallThreshold) {
        this.expandBeam();
        this.stallCount = 0;
      }
    } else {
      this.stallCount = 0;
      this.lastBestScore = currentBestScore;
    }
  }

  private expandBeam(): void {
    const newWidth = Math.min(
      Math.floor(this.currentBeamWidth * this.config.expansionRate),
      this.config.maxBeamWidth
    );
    this.currentBeamWidth = newWidth;
  }
}
```

---

### 5.3 DES-NS-103: コンテキスト認識スコアリング強化

**対応要件**: REQ-NS-103

```typescript
// packages/neural-search/src/scorer/ContextAwareScorer.ts

/**
 * DES-NS-103: コンテキスト認識スコアリング
 * 
 * プロジェクトコンテキストを30%以上の重みでスコアに反映
 */
export interface ContextAwareScorer extends IBranchScorer {
  /** プロジェクトコンテキストを設定 */
  setProjectContext(context: ProjectContext): void;
  
  /** スコア内訳を取得 */
  getScoreBreakdown(branch: Branch): ScoreBreakdown;
}

export interface ProjectContext {
  existingPatterns: CodePattern[];
  namingConventions: NamingConvention[];
  typeUsage: Map<string, number>;
  importFrequency: Map<string, number>;
}

export interface ScoreBreakdown {
  specSimilarity: number;      // 仕様との類似度
  syntaxScore: number;         // 構文的品質
  contextScore: number;        // コンテキスト適合度 (目標: >= 0.30 weight)
  noveltyScore: number;        // 新規性
  totalScore: number;
}

export interface ScoreWeightsConfig {
  specSimilarity: number;  // デフォルト: 0.35
  syntaxScore: number;     // デフォルト: 0.20
  contextScore: number;    // デフォルト: 0.30 (REQ-NS-103)
  noveltyScore: number;    // デフォルト: 0.15
}
```

---

### 5.4 DES-NS-104〜107: その他の設計

```typescript
// DES-NS-104: オンライン学習更新
// packages/neural-search/src/learning/OnlineModelUpdater.ts
export interface OnlineModelUpdater {
  recordFeedback(result: SynthesisResult, feedback: 'accept' | 'reject'): void;
  applyUpdates(): Promise<void>;
  getPendingUpdates(): number;
}

// DES-NS-105: 埋め込みキャッシュ
// packages/neural-search/src/cache/EmbeddingCache.ts
export interface EmbeddingCache {
  get(key: string): Embedding | undefined;
  set(key: string, embedding: Embedding): void;
  getHitRate(): number; // 目標: >= 0.80
  readonly maxSize: number; // 10,000
}

// DES-NS-106: マルチモーダル入力
// packages/neural-search/src/fusion/ModalFusion.ts
export interface ModalFusion {
  fuse(
    textEmbedding: Embedding,
    codeEmbedding: Embedding,
    strategy: 'concat' | 'attention' | 'weighted_sum'
  ): Embedding;
}

// DES-NS-107: トラジェクトリログ強化
// packages/neural-search/src/logging/TrajectoryLogger.ts
export interface TrajectoryLogger {
  logBranch(branch: Branch, score: number, pruned: boolean): void;
  export(format: 'json' | 'parquet'): Promise<Buffer>;
}
```

---

## 6. EPIC-SY: Synthesis PBE Enhancement 設計

### 6.1 DES-SY-101: Witness Function強化

**対応要件**: REQ-SY-101

```typescript
// packages/synthesis/src/witness/EnhancedWitnessEngine.ts

/**
 * DES-SY-101: 強化版Witness関数エンジン
 * 
 * 既存クラス関係: WitnessEngine (既存) を拡張
 *   - EnhancedWitnessEngine extends WitnessEngine
 *   - 既存の基本Witness関数を継承し、20+演算子に拡張
 * 
 * 20種類以上のDSL演算子に対応
 */
export interface EnhancedWitnessEngine {
  /** Witness関数を登録 */
  registerWitness(operatorName: string, witness: WitnessFunction): void;
  
  /** 問題を分解 */
  decompose(spec: Specification, operator: Operator): DecomposedSpec[];
  
  /** 登録済み演算子数を取得 */
  getRegisteredOperatorCount(): number; // 目標: >= 20
}

export type WitnessFunction = (
  spec: Specification,
  partialProgram: Program,
  outputIndex: number
) => Specification[];

/**
 * 組み込みWitness関数（20+）
 */
export const BUILTIN_WITNESSES: Map<string, WitnessFunction> = new Map([
  // String operations (8)
  ['concat', concatWitness],
  ['substring', substringWitness],
  ['replace', replaceWitness],
  ['split', splitWitness],
  ['join', joinWitness],
  ['trim', trimWitness],
  ['toUpperCase', toUpperCaseWitness],
  ['toLowerCase', toLowerCaseWitness],
  
  // List operations (6)
  ['map', mapWitness],
  ['filter', filterWitness],
  ['reduce', reduceWitness],
  ['head', headWitness],
  ['tail', tailWitness],
  ['concat_list', concatListWitness],
  
  // Arithmetic (4)
  ['add', addWitness],
  ['subtract', subtractWitness],
  ['multiply', multiplyWitness],
  ['divide', divideWitness],
  
  // Conditional (2)
  ['if', ifWitness],
  ['switch', switchWitness],
]);
```

---

### 6.2 DES-SY-102: バージョン空間代数強化

**対応要件**: REQ-SY-102

```typescript
// packages/synthesis/src/synthesis/EnhancedVersionSpace.ts

/**
 * DES-SY-102: 強化版バージョン空間
 * 
 * O(n log n)の計算量で交差・和集合・否定操作
 */
export interface EnhancedVersionSpace<T> {
  /** 交差 */
  intersect(other: EnhancedVersionSpace<T>): EnhancedVersionSpace<T>;
  
  /** 和集合 */
  union(other: EnhancedVersionSpace<T>): EnhancedVersionSpace<T>;
  
  /** 否定（補集合） */
  negate(): EnhancedVersionSpace<T>;
  
  /** サイズを取得 */
  size(): number;
  
  /** 空かどうか */
  isEmpty(): boolean;
  
  /** イテレート */
  [Symbol.iterator](): Iterator<T>;
}

/**
 * 効率的な実装（B-tree based）
 */
export class BTreeVersionSpace<T> implements EnhancedVersionSpace<T> {
  private root: BTreeNode<T>;
  
  intersect(other: EnhancedVersionSpace<T>): EnhancedVersionSpace<T> {
    // O(n log n) implementation
  }
  
  // ...
}
```

---

### 6.3 DES-SY-103: メタ学習統合

**対応要件**: REQ-SY-103

```typescript
// packages/synthesis/src/meta/MetaLearningEngine.ts

/**
 * DES-SY-103: メタ学習エンジン
 * 
 * 類似タスクの認識とメタ学習戦略の適用で合成時間を50%削減
 */
export interface MetaLearningEngine {
  /** タスク特徴量を抽出 */
  extractTaskFeatures(spec: Specification): TaskFeatures;
  
  /** 類似タスクを検索 */
  findSimilarTasks(features: TaskFeatures): SimilarTask[];
  
  /** メタ学習戦略を適用 */
  applyStrategy(
    spec: Specification,
    strategy: SynthesisStrategy
  ): StrategizedSpec;
  
  /** 成功した合成を記録 */
  recordSuccess(
    spec: Specification,
    program: Program,
    stats: SynthesisStats
  ): void;
}

export interface TaskFeatures {
  inputTypes: TypeSignature[];
  outputType: TypeSignature;
  exampleCount: number;
  complexity: number;
  domainHints: string[];
}

export interface SynthesisStrategy {
  preferredOperators: string[];
  searchOrder: 'top-down' | 'bottom-up' | 'bidirectional';
  maxDepth: number;
  pruningHints: PruningHint[];
}
```

---

### 6.4 DES-SY-104〜106: その他の設計

```typescript
// DES-SY-104: DSL自動拡張
// packages/synthesis/src/dsl/DSLExtender.ts
export interface DSLExtender {
  analyzeGap(spec: Specification, dsl: IDSL): GapAnalysis;
  suggestOperators(gap: GapAnalysis): OperatorSuggestion[];
}

// DES-SY-105: 例示品質評価
// packages/synthesis/src/analysis/ExampleAnalyzer.ts
export interface ExampleAnalyzer {
  analyzeQuality(examples: Example[]): QualityReport;
  suggestAdditionalExamples(examples: Example[]): Example[];
  detectAmbiguity(examples: Example[]): AmbiguityReport;
}

// DES-SY-106: 説明生成
// packages/synthesis/src/explain/ExplanationGenerator.ts
export interface ExplanationGenerator {
  generate(program: Program): NaturalLanguageExplanation;
  getConfidence(): number;
}
```

---

## 7. EPIC-INT: Integration & Orchestration 設計

### 7.1 DES-INT-101: 統合オーケストレーション

**対応要件**: REQ-INT-101

```typescript
// packages/core/src/synthesis/SynthesisOrchestrator.ts

/**
 * DES-INT-101: 合成オーケストレーター
 * 
 * 3パッケージを統合したE2E合成フロー
 */
export interface SynthesisOrchestrator {
  /** 自然言語仕様から合成 */
  synthesizeFromNL(
    spec: string,
    options?: OrchestratorOptions
  ): Promise<SynthesisResult>;
  
  /** PBE合成（ライブラリ活用） */
  synthesizeWithLibrary(
    spec: Specification,
    library: PatternLibrary
  ): Promise<SynthesisResult>;
  
  /** パイプライン構成を設定 */
  setPipeline(config: PipelineConfig): void;
}

export interface OrchestratorOptions {
  useLibrary: boolean;
  useNeuralSearch: boolean;
  pipelinePreset: 'fast' | 'accurate' | 'balanced';
  timeout: number;
}

/**
 * オーケストレーションフロー
 * 
 * 1. 自然言語 → 構造化仕様 (NL Parser)
 * 2. ライブラリから関連パターン検索 (Library Learner)
 * 3. Neural Searchで探索誘導 (Neural Search)
 * 4. PBE合成実行 (Synthesis)
 * 5. 結果のランキング・フィルタリング
 */
```

### 7.2 DES-INT-102: パイプライン構成

**対応要件**: REQ-INT-102

```typescript
// packages/core/src/synthesis/PipelineConfig.ts

export interface PipelineConfig {
  name: string;
  stages: PipelineStage[];
  parallelism: number;
  timeout: number;
}

export type PipelineStage =
  | { type: 'library'; config: LibraryStageConfig }
  | { type: 'neural'; config: NeuralStageConfig }
  | { type: 'synthesis'; config: SynthesisStageConfig };

/**
 * プリセット構成
 */
export const PRESETS: Record<string, PipelineConfig> = {
  fast: {
    name: 'fast',
    stages: [
      { type: 'synthesis', config: { maxDepth: 3, timeout: 5000 } },
    ],
    parallelism: 1,
    timeout: 10000,
  },
  accurate: {
    name: 'accurate',
    stages: [
      { type: 'library', config: { useTypeDirected: true } },
      { type: 'neural', config: { beamWidth: 50, useContext: true } },
      { type: 'synthesis', config: { maxDepth: 8, maxCandidates: 100 } },
    ],
    parallelism: 4,
    timeout: 60000,
  },
  balanced: {
    name: 'balanced',
    stages: [
      { type: 'library', config: { useTypeDirected: true } },
      { type: 'neural', config: { beamWidth: 20, useContext: true } },
      { type: 'synthesis', config: { maxDepth: 5, maxCandidates: 20 } },
    ],
    parallelism: 2,
    timeout: 30000,
  },
};
```

---

### 7.3 DES-INT-103: MCPツール統合

**対応要件**: REQ-INT-103

```typescript
// packages/mcp-server/src/tools/synthesis-tools.ts

/**
 * DES-INT-103: 合成関連MCPツール
 * 
 * 5つの新規ツールを追加
 */
export const SYNTHESIS_TOOLS: MCPTool[] = [
  {
    name: 'synthesis_from_nl',
    description: '自然言語仕様からコードを合成',
    parameters: {
      spec: { type: 'string', description: '自然言語仕様' },
      pipeline: { type: 'string', enum: ['fast', 'accurate', 'balanced'], default: 'balanced' },
      timeout: { type: 'number', default: 30000 },
    },
    handler: synthesisFromNLHandler,
  },
  {
    name: 'synthesis_from_examples',
    description: '入出力例からコードを合成（PBE）',
    parameters: {
      examples: { type: 'array', items: { input: 'any', output: 'any' } },
      hints: { type: 'string', optional: true },
    },
    handler: synthesisFromExamplesHandler,
  },
  {
    name: 'library_query',
    description: '学習済みパターンライブラリを検索',
    parameters: {
      query: { type: 'string' },
      limit: { type: 'number', default: 10 },
    },
    handler: libraryQueryHandler,
  },
  {
    name: 'synthesis_explain',
    description: '合成されたコードの説明を生成',
    parameters: {
      code: { type: 'string' },
      detail: { type: 'string', enum: ['brief', 'detailed'], default: 'brief' },
    },
    handler: synthesisExplainHandler,
  },
  {
    name: 'synthesis_feedback',
    description: '合成結果へのフィードバックを記録',
    parameters: {
      resultId: { type: 'string' },
      feedback: { type: 'string', enum: ['accept', 'reject', 'modify'] },
      comment: { type: 'string', optional: true },
    },
    handler: synthesisFeedbackHandler,
  },
];

/**
 * 合成プロンプト定義
 */
// packages/mcp-server/src/prompts/synthesis-prompts.ts
export const SYNTHESIS_PROMPTS: MCPPrompt[] = [
  {
    name: 'synthesis_spec_generation',
    description: '機能説明から合成用仕様を生成',
    template: `以下の機能説明から、MUSUBIX合成エンジン用の構造化仕様を生成してください:

機能説明: {{description}}

出力形式:
- 入出力例（3件以上）
- 型制約
- エッジケース`,
  },
  {
    name: 'synthesis_review',
    description: '合成されたコードのレビュー',
    template: `以下の合成コードをレビューしてください:

仕様: {{spec}}
合成コード: {{code}}

レビュー観点:
- 仕様との適合性
- コード品質
- 改善提案`,
  },
];
```

---

### 7.4 DES-INT-104: CLI統合

**対応要件**: REQ-INT-104

```typescript
// packages/core/src/cli/SynthesisCLI.ts

/**
 * DES-INT-104: 合成CLIコマンド
 * 
 * 既存CLIに統合される新規サブコマンド
 */
export interface SynthesisCLICommands {
  /**
   * npx musubix synthesize <spec-file>
   * 仕様ファイルからコードを合成
   */
  synthesize: {
    args: ['specFile: string'];
    options: {
      output: { alias: 'o', type: 'string', description: '出力ファイルパス' };
      pipeline: { alias: 'p', type: 'string', default: 'balanced' };
      timeout: { alias: 't', type: 'number', default: 30000 };
      explain: { alias: 'e', type: 'boolean', default: false };
    };
  };

  /**
   * npx musubix synthesize:pbe <examples-file>
   * 入出力例ファイルからPBE合成
   */
  'synthesize:pbe': {
    args: ['examplesFile: string'];
    options: {
      output: { alias: 'o', type: 'string' };
      maxCandidates: { alias: 'm', type: 'number', default: 10 };
    };
  };

  /**
   * npx musubix library:learn <corpus-dir>
   * コーパスからライブラリを学習
   */
  'library:learn': {
    args: ['corpusDir: string'];
    options: {
      output: { alias: 'o', type: 'string', default: '.musubix/library' };
      incremental: { alias: 'i', type: 'boolean', default: false };
    };
  };

  /**
   * npx musubix library:query <query>
   * ライブラリを検索
   */
  'library:query': {
    args: ['query: string'];
    options: {
      limit: { alias: 'l', type: 'number', default: 10 };
      format: { alias: 'f', type: 'string', enum: ['json', 'table'], default: 'table' };
    };
  };

  /**
   * npx musubix library:stats
   * ライブラリ統計を表示
   */
  'library:stats': {
    args: [];
    options: {
      format: { alias: 'f', type: 'string', enum: ['json', 'markdown'], default: 'markdown' };
    };
  };
}

/**
 * CLI実装クラス
 */
export class SynthesisCLI {
  constructor(
    private orchestrator: SynthesisOrchestrator,
    private libraryLearner: ILibraryLearner
  ) {}

  async synthesize(specFile: string, options: SynthesizeOptions): Promise<void> {
    const spec = await this.loadSpec(specFile);
    const result = await this.orchestrator.synthesizeFromNL(spec, {
      pipelinePreset: options.pipeline as 'fast' | 'accurate' | 'balanced',
      timeout: options.timeout,
    });
    
    if (options.output) {
      await writeFile(options.output, result.code);
    } else {
      console.log(result.code);
    }
    
    if (options.explain) {
      console.log('\n--- Explanation ---');
      console.log(result.explanation);
    }
  }

  // 他のコマンド実装...
}
```

---

## 8. 新規ファイル一覧

### 8.1 library-learner

| ファイルパス | 対応設計 | 説明 |
|-------------|---------|------|
| `src/hierarchy/HierarchyManager.ts` | DES-LL-101 | 階層管理 |
| `src/search/TypeDirectedPruner.ts` | DES-LL-102 | 型枝刈り |
| `src/library/IterativeCompressor.ts` | DES-LL-103 | 反復圧縮 |
| `src/egraph/RewriteRuleSet.ts` | DES-LL-104 | リライトルール |
| `src/library/PatternVersionManager.ts` | DES-LL-105 | バージョン管理 |
| `src/domain/DomainAwareAbstractor.ts` | DES-LL-106 | ドメイン特化 |
| `src/incremental/IncrementalUpdater.ts` | DES-LL-107 | 増分更新 |
| `src/metrics/MetricsExporter.ts` | DES-LL-108 | メトリクス |

### 8.2 neural-search

| ファイルパス | 対応設計 | 説明 |
|-------------|---------|------|
| `src/pruning/LearnedPruningPolicy.ts` | DES-NS-101 | 学習プルーニング |
| `src/search/AdaptiveBeamSearch.ts` | DES-NS-102 | 適応ビーム |
| `src/scorer/ContextAwareScorer.ts` | DES-NS-103 | コンテキストスコア |
| `src/learning/OnlineModelUpdater.ts` | DES-NS-104 | オンライン学習 |
| `src/cache/EmbeddingCache.ts` | DES-NS-105 | 埋め込みキャッシュ |
| `src/fusion/ModalFusion.ts` | DES-NS-106 | モーダル融合 |
| `src/logging/TrajectoryLogger.ts` | DES-NS-107 | トラジェクトリログ |

### 8.3 synthesis

| ファイルパス | 対応設計 | 説明 |
|-------------|---------|------|
| `src/witness/EnhancedWitnessEngine.ts` | DES-SY-101 | 強化Witness |
| `src/synthesis/EnhancedVersionSpace.ts` | DES-SY-102 | 強化バージョン空間 |
| `src/meta/MetaLearningEngine.ts` | DES-SY-103 | メタ学習 |
| `src/dsl/DSLExtender.ts` | DES-SY-104 | DSL拡張 |
| `src/analysis/ExampleAnalyzer.ts` | DES-SY-105 | 例示分析 |
| `src/explain/ExplanationGenerator.ts` | DES-SY-106 | 説明生成 |

### 8.4 core（オーケストレーション）

| ファイルパス | 対応設計 | 説明 |
|-------------|---------|------|
| `src/synthesis/SynthesisOrchestrator.ts` | DES-INT-101 | オーケストレーター |
| `src/synthesis/PipelineConfig.ts` | DES-INT-102 | パイプライン構成 |
| `src/cli/SynthesisCLI.ts` | DES-INT-104 | 合成CLI |

### 8.5 mcp-server（MCPツール）

| ファイルパス | 対応設計 | 説明 |
|-------------|---------|------|
| `src/tools/synthesis-tools.ts` | DES-INT-103 | 合成MCPツール |
| `src/prompts/synthesis-prompts.ts` | DES-INT-103 | 合成プロンプト |

---

## 9. トレーサビリティ

### 9.1 要件→設計マッピング

| 要件ID | 設計ID | コンポーネント |
|--------|--------|---------------|
| REQ-LL-101 | DES-LL-101 | HierarchyManager |
| REQ-LL-102 | DES-LL-102 | TypeDirectedPruner |
| REQ-LL-103 | DES-LL-103 | IterativeCompressor |
| REQ-LL-104 | DES-LL-104 | RewriteRuleSet |
| REQ-LL-105 | DES-LL-105 | PatternVersionManager |
| REQ-LL-106 | DES-LL-106 | DomainAwareAbstractor |
| REQ-LL-107 | DES-LL-107 | IncrementalUpdater |
| REQ-LL-108 | DES-LL-108 | MetricsExporter |
| REQ-NS-101 | DES-NS-101 | LearnedPruningPolicy |
| REQ-NS-102 | DES-NS-102 | AdaptiveBeamSearch |
| REQ-NS-103 | DES-NS-103 | ContextAwareScorer |
| REQ-NS-104 | DES-NS-104 | OnlineModelUpdater |
| REQ-NS-105 | DES-NS-105 | EmbeddingCache |
| REQ-NS-106 | DES-NS-106 | ModalFusion |
| REQ-NS-107 | DES-NS-107 | TrajectoryLogger |
| REQ-SY-101 | DES-SY-101 | EnhancedWitnessEngine |
| REQ-SY-102 | DES-SY-102 | EnhancedVersionSpace |
| REQ-SY-103 | DES-SY-103 | MetaLearningEngine |
| REQ-SY-104 | DES-SY-104 | DSLExtender |
| REQ-SY-105 | DES-SY-105 | ExampleAnalyzer |
| REQ-SY-106 | DES-SY-106 | ExplanationGenerator |
| REQ-INT-101 | DES-INT-101 | SynthesisOrchestrator |
| REQ-INT-102 | DES-INT-102 | PipelineConfig |
| REQ-INT-103 | DES-INT-103 | MCP Tools (mcp-server) |
| REQ-INT-104 | DES-INT-104 | SynthesisCLI (core/cli) |

---

## 10. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-08 | - |
| レビュアー | | | |
| 承認者 | | | |

---

## 変更履歴

| バージョン | 日付 | 変更内容 | 変更者 |
|-----------|------|---------|--------|
| 1.0.0 | 2026-01-08 | 初版作成 | AI Agent |
| 1.1.0 | 2026-01-08 | レビュー指摘対応: DES-INT-103/104追加、ファイル一覧補完、既存クラス関係明記 | AI Agent |

---

**Document ID**: DES-v2.2.0-Advanced-Learning  
**Classification**: Internal  
**憲法条項準拠**: Article V (Traceability), Article VII (Design Patterns)
