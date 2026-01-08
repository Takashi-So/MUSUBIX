# MUSUBIX v2.2.0 タスク分解書 - Advanced Learning Enhancement

| 項目 | 内容 |
|------|------|
| **ドキュメントID** | TSK-v2.2.0-Advanced-Learning |
| **バージョン** | 1.1.0 |
| **作成日** | 2026-01-08 |
| **ステータス** | レビュー済み |
| **対応設計** | DES-v2.2.0-Advanced-Learning |
| **対応要件** | REQ-v2.2.0-Advanced-Learning |

---

## 1. タスク概要

### 1.1 サマリー

| 項目 | 数 |
|------|---|
| **総タスク数** | 29 |
| **P0タスク** | 14 |
| **P1タスク** | 11 |
| **P2タスク** | 4 |
| **新規ファイル** | 24 |
| **修正ファイル** | 9 |
| **推定工数** | 約70時間 |

### 1.2 実装順序

```
Phase A: 基盤コンポーネント（P0）
├── TSK-LL-101〜104: Library Learner基盤
├── TSK-NS-101〜103: Neural Search基盤
└── TSK-SY-101〜102: Synthesis基盤

Phase B: 統合コンポーネント（P0）
├── TSK-INT-101〜102: オーケストレーター
└── TSK-LL-107: 増分学習

Phase C: 拡張コンポーネント（P1）
├── TSK-LL-105〜106: パターン管理
├── TSK-NS-104〜107: 探索強化
└── TSK-SY-103〜105: 合成強化

Phase D: ユーザーインターフェース（P1/P2）
├── TSK-INT-103〜104: MCP/CLI
├── TSK-LL-108: メトリクス
└── TSK-SY-106: 説明生成
```

---

## 2. EPIC-LL: Library Learner Enhancement タスク

### TSK-LL-101: HierarchyManager 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-101 |
| **対応設計** | DES-LL-101 |
| **対応要件** | REQ-LL-101 |
| **優先度** | P0 |
| **推定工数** | 3時間 |
| **依存** | なし |

**実装内容**:
1. `packages/library-learner/src/hierarchy/HierarchyManager.ts` を作成
2. `HierarchyManager` インターフェースと実装クラス
3. 3レベル以上の階層的抽象化を管理
4. `PatternMiner`, `Abstractor` への委譲実装

**受け入れ基準**:
- [ ] `HierarchyManager` インターフェース定義
- [ ] `DefaultHierarchyManager` クラス実装
- [ ] `extractHierarchy()` メソッドが3レベル以上を抽出
- [ ] `shouldPromote()` による昇格判定
- [ ] ユニットテスト（10件以上）
- [ ] 1000 LOCあたり10秒以内の処理時間

**テストファイル**: `packages/library-learner/src/hierarchy/__tests__/HierarchyManager.test.ts`

---

### TSK-LL-102: TypeDirectedPruner 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-102 |
| **対応設計** | DES-LL-102 |
| **対応要件** | REQ-LL-102 |
| **優先度** | P0 |
| **推定工数** | 3時間 |
| **依存** | なし |

**実装内容**:
1. `packages/library-learner/src/search/TypeDirectedPruner.ts` を作成
2. 型シグネチャによる探索空間枝刈り
3. TypeScriptの型システムとの互換性

**受け入れ基準**:
- [ ] `TypeDirectedPruner` インターフェース定義
- [ ] `prune()` メソッドで90%以上の探索空間削減
- [ ] `PruningStats` による統計取得
- [ ] ユニットテスト（8件以上）
- [ ] 削減率のベンチマークテスト

**テストファイル**: `packages/library-learner/src/search/__tests__/TypeDirectedPruner.test.ts`

---

### TSK-LL-103: IterativeCompressor 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-103 |
| **対応設計** | DES-LL-103 |
| **対応要件** | REQ-LL-103 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | TSK-LL-101 |

**実装内容**:
1. `packages/library-learner/src/library/IterativeCompressor.ts` を作成
2. 類似パターンのマージアルゴリズム
3. 30%以上のサイズ削減、95%カバレッジ維持

**受け入れ基準**:
- [ ] `IterativeCompressor` インターフェース定義
- [ ] `compress()` メソッドで30%以上削減
- [ ] `shouldCompress()` による自動トリガー（100パターン以上）
- [ ] カバレッジ95%以上を維持
- [ ] ユニットテスト（6件以上）

**テストファイル**: `packages/library-learner/src/library/__tests__/IterativeCompressor.test.ts`

---

### TSK-LL-104: RewriteRuleSet 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-104 |
| **対応設計** | DES-LL-104 |
| **対応要件** | REQ-LL-104 |
| **優先度** | P0 |
| **推定工数** | 4時間 |
| **依存** | なし |

**実装内容**:
1. `packages/library-learner/src/egraph/RewriteRuleSet.ts` を作成
2. 50種類以上のリライトルール（代数、Boolean、文字列、配列、条件）
3. 既存 `EGraph` クラスとの統合

**受け入れ基準**:
- [ ] `RewriteRuleSet` インターフェース定義
- [ ] `BUILTIN_RULES` に50種類以上のルール
- [ ] カテゴリ別ルール取得 `getRulesByCategory()`
- [ ] 既存EGraphへの適用 `applyAll()`
- [ ] ユニットテスト（15件以上、各カテゴリ3件）

**テストファイル**: `packages/library-learner/src/egraph/__tests__/RewriteRuleSet.test.ts`

---

### TSK-LL-105: PatternVersionManager 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-105 |
| **対応設計** | DES-LL-105 |
| **対応要件** | REQ-LL-105 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | TSK-LL-101 |

**実装内容**:
1. `packages/library-learner/src/library/PatternVersionManager.ts` を作成
2. パターンのバージョン履歴管理
3. ロールバック機能

**受け入れ基準**:
- [ ] `PatternVersionManager` インターフェース定義
- [ ] `recordVersion()` でバージョン記録
- [ ] `rollback()` で任意バージョンへ復元
- [ ] `getHistory()` で履歴取得
- [ ] ユニットテスト（5件以上）

**テストファイル**: `packages/library-learner/src/library/__tests__/PatternVersionManager.test.ts`

---

### TSK-LL-106: DomainAwareAbstractor 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-106 |
| **対応設計** | DES-LL-106 |
| **対応要件** | REQ-LL-106 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | TSK-LL-101 |

**実装内容**:
1. `packages/library-learner/src/domain/DomainAwareAbstractor.ts` を作成
2. オントロジーからの制約読み取り
3. ドメイン概念を反映した抽象化

**受け入れ基準**:
- [ ] `DomainAwareAbstractor` インターフェース定義
- [ ] `loadOntology()` でオントロジー読み込み
- [ ] `abstractWithDomain()` でドメイン特化抽象化
- [ ] ユニットテスト（5件以上）

**テストファイル**: `packages/library-learner/src/domain/__tests__/DomainAwareAbstractor.test.ts`

---

### TSK-LL-107: IncrementalUpdater 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-107 |
| **対応設計** | DES-LL-107 |
| **対応要件** | REQ-LL-107 |
| **優先度** | P0 |
| **推定工数** | 3時間 |
| **依存** | TSK-LL-101, TSK-LL-105 |

**実装内容**:
1. `packages/library-learner/src/incremental/IncrementalUpdater.ts` を作成
2. 完全再計算なしの増分更新
3. 500 LOC以下で5秒以内

**受け入れ基準**:
- [ ] `IncrementalUpdater` インターフェース定義
- [ ] `update()` で増分更新
- [ ] `isIncrementalPossible()` で判定
- [ ] 500 LOC以下で5秒以内の処理時間
- [ ] ユニットテスト（6件以上）
- [ ] パフォーマンステスト

**テストファイル**: `packages/library-learner/src/incremental/__tests__/IncrementalUpdater.test.ts`

---

### TSK-LL-108: MetricsExporter 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-108 |
| **対応設計** | DES-LL-108 |
| **対応要件** | REQ-LL-108 |
| **優先度** | P2 |
| **推定工数** | 1時間 |
| **依存** | TSK-LL-101〜107 |

**実装内容**:
1. `packages/library-learner/src/metrics/MetricsExporter.ts` を作成
2. JSON/Markdownエクスポート
3. パターン使用頻度、圧縮率、探索削減率

**受け入れ基準**:
- [ ] `MetricsExporter` インターフェース定義
- [ ] `export('json')` でJSON出力
- [ ] `export('markdown')` でMarkdown出力
- [ ] ユニットテスト（4件以上）

**テストファイル**: `packages/library-learner/src/metrics/__tests__/MetricsExporter.test.ts`

---

### TSK-LL-109: LibraryLearner 統合

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-LL-109 |
| **対応設計** | DES-LL-101〜108 |
| **優先度** | P0 |
| **推定工数** | 2時間 |
| **依存** | TSK-LL-101〜108 |

**実装内容**:
1. `packages/library-learner/src/LibraryLearner.ts` を修正
2. 新コンポーネントの統合
3. `index.ts` のエクスポート更新

**受け入れ基準**:
- [ ] 既存APIとの100%後方互換
- [ ] 新コンポーネントへの委譲実装
- [ ] 統合テスト（5件以上）

**テストファイル**: `packages/library-learner/src/__tests__/LibraryLearner.integration.test.ts`

---

## 3. EPIC-NS: Neural Search Guidance タスク

### TSK-NS-101: LearnedPruningPolicy 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-101 |
| **対応設計** | DES-NS-101 |
| **対応要件** | REQ-NS-101 |
| **優先度** | P0 |
| **推定工数** | 3時間 |
| **依存** | なし |

**実装内容**:
1. `packages/neural-search/src/pruning/LearnedPruningPolicy.ts` を作成
2. 学習済みプルーニングポリシー
3. 70%以上の探索ノード削減

**受け入れ基準**:
- [ ] `LearnedPruningPolicy` インターフェース定義
- [ ] `shouldPrune()` でプルーニング判定
- [ ] `updatePolicy()` でポリシー更新
- [ ] 70%以上の削減率
- [ ] ソリューション品質95%以上維持
- [ ] ユニットテスト（8件以上）

**テストファイル**: `packages/neural-search/src/pruning/__tests__/LearnedPruningPolicy.test.ts`

---

### TSK-NS-102: AdaptiveBeamSearch 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-102 |
| **対応設計** | DES-NS-102 |
| **対応要件** | REQ-NS-102 |
| **優先度** | P0 |
| **推定工数** | 3時間 |
| **依存** | なし |

**実装内容**:
1. `packages/neural-search/src/search/AdaptiveBeamSearch.ts` を作成
2. 既存 `BeamSearch` を継承
3. 探索停滞時のビーム幅動的調整

**受け入れ基準**:
- [ ] `AdaptiveBeamSearch extends BeamSearch`
- [ ] `adjustBeamWidth()` で動的調整
- [ ] 停滞検出（10反復改善なし）
- [ ] 50%ビーム幅増加、最大100
- [ ] ユニットテスト（8件以上）

**テストファイル**: `packages/neural-search/src/search/__tests__/AdaptiveBeamSearch.test.ts`

---

### TSK-NS-103: ContextAwareScorer 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-103 |
| **対応設計** | DES-NS-103 |
| **対応要件** | REQ-NS-103 |
| **優先度** | P0 |
| **推定工数** | 3時間 |
| **依存** | なし |

**実装内容**:
1. `packages/neural-search/src/scorer/ContextAwareScorer.ts` を作成
2. プロジェクトコンテキストを30%以上の重みで反映
3. 既存 `IBranchScorer` を実装

**受け入れ基準**:
- [ ] `ContextAwareScorer implements IBranchScorer`
- [ ] `setProjectContext()` でコンテキスト設定
- [ ] `getScoreBreakdown()` で内訳取得
- [ ] コンテキストスコア30%以上の重み
- [ ] ユニットテスト（8件以上）

**テストファイル**: `packages/neural-search/src/scorer/__tests__/ContextAwareScorer.test.ts`

---

### TSK-NS-104: OnlineModelUpdater 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-104 |
| **対応設計** | DES-NS-104 |
| **対応要件** | REQ-NS-104 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | TSK-NS-101 |

**実装内容**:
1. `packages/neural-search/src/learning/OnlineModelUpdater.ts` を作成
2. accept/rejectフィードバック収集
3. 3回以内のモデル更新反映

**受け入れ基準**:
- [ ] `OnlineModelUpdater` インターフェース定義
- [ ] `recordFeedback()` でフィードバック記録
- [ ] `applyUpdates()` でモデル更新
- [ ] 3回以内に反映
- [ ] ユニットテスト（5件以上）

**テストファイル**: `packages/neural-search/src/learning/__tests__/OnlineModelUpdater.test.ts`

---

### TSK-NS-105: EmbeddingCache 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-105 |
| **対応設計** | DES-NS-105 |
| **対応要件** | REQ-NS-105 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | なし |

**実装内容**:
1. `packages/neural-search/src/cache/EmbeddingCache.ts` を作成
2. LRUキャッシュ（最大10,000エントリ）
3. 80%以上のヒット率目標

**受け入れ基準**:
- [ ] `EmbeddingCache` インターフェース定義
- [ ] LRU eviction実装
- [ ] `getHitRate()` でヒット率取得
- [ ] maxSize: 10,000
- [ ] ユニットテスト（6件以上）

**テストファイル**: `packages/neural-search/src/cache/__tests__/EmbeddingCache.test.ts`

---

### TSK-NS-106: ModalFusion 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-106 |
| **対応設計** | DES-NS-106 |
| **対応要件** | REQ-NS-106 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | TSK-NS-105 |

**実装内容**:
1. `packages/neural-search/src/fusion/ModalFusion.ts` を作成
2. テキスト/コード埋め込みの融合
3. concat/attention/weighted_sum戦略

**受け入れ基準**:
- [ ] `ModalFusion` インターフェース定義
- [ ] 3つの融合戦略実装
- [ ] ユニットテスト（6件以上）

**テストファイル**: `packages/neural-search/src/fusion/__tests__/ModalFusion.test.ts`

---

### TSK-NS-107: TrajectoryLogger 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-107 |
| **対応設計** | DES-NS-107 |
| **対応要件** | REQ-NS-107 |
| **優先度** | P2 |
| **推定工数** | 1時間 |
| **依存** | TSK-NS-101〜102 |

**実装内容**:
1. `packages/neural-search/src/logging/TrajectoryLogger.ts` を作成
2. 探索軌跡のログ
3. JSON/Parquetエクスポート

**受け入れ基準**:
- [ ] `TrajectoryLogger` インターフェース定義
- [ ] `logBranch()` でブランチ記録
- [ ] `export()` でJSON/Parquet出力
- [ ] ユニットテスト（4件以上）

**テストファイル**: `packages/neural-search/src/logging/__tests__/TrajectoryLogger.test.ts`

---

### TSK-NS-108: BeamSearch 統合

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-NS-108 |
| **対応設計** | DES-NS-101〜107 |
| **優先度** | P0 |
| **推定工数** | 2時間 |
| **依存** | TSK-NS-101〜106 |

> **注**: TSK-NS-107（TrajectoryLogger, P2）はオプショナル。統合時に未完了でも進行可能。

**実装内容**:
1. `packages/neural-search/src/BeamSearch.ts` を修正
2. 新コンポーネントの統合
3. `index.ts` のエクスポート更新

**受け入れ基準**:
- [ ] 既存APIとの100%後方互換
- [ ] 新コンポーネントへの委譲実装
- [ ] 統合テスト（5件以上）

**テストファイル**: `packages/neural-search/src/__tests__/BeamSearch.integration.test.ts`

---

## 4. EPIC-SY: Synthesis PBE Enhancement タスク

### TSK-SY-101: EnhancedWitnessEngine 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-SY-101 |
| **対応設計** | DES-SY-101 |
| **対応要件** | REQ-SY-101 |
| **優先度** | P0 |
| **推定工数** | 4時間 |
| **依存** | なし |

**実装内容**:
1. `packages/synthesis/src/witness/EnhancedWitnessEngine.ts` を作成
2. 既存 `WitnessEngine` を継承
3. 20種類以上のWitness関数

**受け入れ基準**:
- [ ] `EnhancedWitnessEngine extends WitnessEngine`
- [ ] `BUILTIN_WITNESSES` に20種類以上
- [ ] String(8), List(6), Arithmetic(4), Conditional(2)
- [ ] `registerWitness()` でカスタム登録
- [ ] ユニットテスト（12件以上）

**テストファイル**: `packages/synthesis/src/witness/__tests__/EnhancedWitnessEngine.test.ts`

---

### TSK-SY-102: EnhancedVersionSpace 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-SY-102 |
| **対応設計** | DES-SY-102 |
| **対応要件** | REQ-SY-102 |
| **優先度** | P0 |
| **推定工数** | 3時間 |
| **依存** | なし |

**実装内容**:
1. `packages/synthesis/src/synthesis/EnhancedVersionSpace.ts` を作成
2. B-treeベースの効率的実装
3. O(n log n)の交差・和集合・否定

**受け入れ基準**:
- [ ] `EnhancedVersionSpace<T>` インターフェース定義
- [ ] `BTreeVersionSpace` クラス実装
- [ ] `intersect()`, `union()`, `negate()` メソッド
- [ ] O(n log n)の計算量
- [ ] ユニットテスト（10件以上）

**テストファイル**: `packages/synthesis/src/synthesis/__tests__/EnhancedVersionSpace.test.ts`

---

### TSK-SY-103: MetaLearningEngine 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-SY-103 |
| **対応設計** | DES-SY-103 |
| **対応要件** | REQ-SY-103 |
| **優先度** | P1 |
| **推定工数** | 3時間 |
| **依存** | TSK-SY-101, TSK-SY-102 |

**実装内容**:
1. `packages/synthesis/src/meta/MetaLearningEngine.ts` を作成
2. 類似タスク認識
3. 合成時間50%削減

**受け入れ基準**:
- [ ] `MetaLearningEngine` インターフェース定義
- [ ] `extractTaskFeatures()` で特徴量抽出
- [ ] `findSimilarTasks()` で類似タスク検索
- [ ] `applyStrategy()` で戦略適用
- [ ] 50%以上の合成時間削減
- [ ] ユニットテスト（8件以上）

**テストファイル**: `packages/synthesis/src/meta/__tests__/MetaLearningEngine.test.ts`

---

### TSK-SY-104: DSLExtender 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-SY-104 |
| **対応設計** | DES-SY-104 |
| **対応要件** | REQ-SY-104 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | TSK-SY-101 |

**実装内容**:
1. `packages/synthesis/src/dsl/DSLExtender.ts` を作成
2. DSL表現力ギャップ分析
3. 演算子提案

**受け入れ基準**:
- [ ] `DSLExtender` インターフェース定義
- [ ] `analyzeGap()` でギャップ分析
- [ ] `suggestOperators()` で演算子提案
- [ ] ユニットテスト（5件以上）

**テストファイル**: `packages/synthesis/src/dsl/__tests__/DSLExtender.test.ts`

---

### TSK-SY-105: ExampleAnalyzer 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-SY-105 |
| **対応設計** | DES-SY-105 |
| **対応要件** | REQ-SY-105 |
| **優先度** | P1 |
| **推定工数** | 2時間 |
| **依存** | なし |

**実装内容**:
1. `packages/synthesis/src/analysis/ExampleAnalyzer.ts` を作成
2. 入出力例の品質評価
3. 追加例示の提案

**受け入れ基準**:
- [ ] `ExampleAnalyzer` インターフェース定義
- [ ] `analyzeQuality()` で品質評価
- [ ] `suggestAdditionalExamples()` で追加提案
- [ ] `detectAmbiguity()` で曖昧性検出
- [ ] ユニットテスト（6件以上）

**テストファイル**: `packages/synthesis/src/analysis/__tests__/ExampleAnalyzer.test.ts`

---

### TSK-SY-106: ExplanationGenerator 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-SY-106 |
| **対応設計** | DES-SY-106 |
| **対応要件** | REQ-SY-106 |
| **優先度** | P2 |
| **推定工数** | 2時間 |
| **依存** | TSK-SY-101 |

**実装内容**:
1. `packages/synthesis/src/explain/ExplanationGenerator.ts` を作成
2. 合成コードの自然言語説明
3. 信頼度スコア

**受け入れ基準**:
- [ ] `ExplanationGenerator` インターフェース定義
- [ ] `generate()` で説明生成
- [ ] `getConfidence()` で信頼度取得
- [ ] ユニットテスト（4件以上）

**テストファイル**: `packages/synthesis/src/explain/__tests__/ExplanationGenerator.test.ts`

---

### TSK-SY-107: PBESynthesizer 統合

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-SY-107 |
| **対応設計** | DES-SY-101〜106 |
| **優先度** | P0 |
| **推定工数** | 2時間 |
| **依存** | TSK-SY-101〜106 |

**実装内容**:
1. `packages/synthesis/src/PBESynthesizer.ts` を修正
2. 新コンポーネントの統合
3. `index.ts` のエクスポート更新

**受け入れ基準**:
- [ ] 既存APIとの100%後方互換
- [ ] 新コンポーネントへの委譲実装
- [ ] 統合テスト（5件以上）

**テストファイル**: `packages/synthesis/src/__tests__/PBESynthesizer.integration.test.ts`

---

## 5. EPIC-INT: Integration & Orchestration タスク

### TSK-INT-101: SynthesisOrchestrator 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-INT-101 |
| **対応設計** | DES-INT-101 |
| **対応要件** | REQ-INT-101 |
| **優先度** | P0 |
| **推定工数** | 4時間 |
| **依存** | TSK-LL-109, TSK-NS-108, TSK-SY-107 |

**実装内容**:
1. `packages/core/src/synthesis/SynthesisOrchestrator.ts` を作成
2. 3パッケージ統合のE2E合成フロー
3. NL → 構造化仕様 → ライブラリ → 探索 → 合成

**受け入れ基準**:
- [ ] `SynthesisOrchestrator` インターフェース定義
- [ ] `synthesizeFromNL()` で自然言語から合成
- [ ] `synthesizeWithLibrary()` でライブラリ活用合成
- [ ] 3パッケージの連携動作
- [ ] ユニットテスト（8件以上）
- [ ] E2E統合テスト（3件以上）

**テストファイル**: `packages/core/src/synthesis/__tests__/SynthesisOrchestrator.test.ts`

---

### TSK-INT-102: PipelineConfig 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-INT-102 |
| **対応設計** | DES-INT-102 |
| **対応要件** | REQ-INT-102 |
| **優先度** | P0 |
| **推定工数** | 2時間 |
| **依存** | なし |

**実装内容**:
1. `packages/core/src/synthesis/PipelineConfig.ts` を作成
2. 3つのプリセット（fast, accurate, balanced）
3. カスタムパイプライン構成

**受け入れ基準**:
- [ ] `PipelineConfig` 型定義
- [ ] `PipelineStage` 型定義
- [ ] `PRESETS` 定数（3プリセット）
- [ ] ユニットテスト（5件以上）

**テストファイル**: `packages/core/src/synthesis/__tests__/PipelineConfig.test.ts`

---

### TSK-INT-103: MCP Synthesis Tools 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-INT-103 |
| **対応設計** | DES-INT-103 |
| **対応要件** | REQ-INT-103 |
| **優先度** | P1 |
| **推定工数** | 3時間 |
| **依存** | TSK-INT-101 |

**実装内容**:
1. `packages/mcp-server/src/tools/synthesis-tools.ts` を作成
2. `packages/mcp-server/src/prompts/synthesis-prompts.ts` を作成
3. 5つのMCPツール、2つのプロンプト

**受け入れ基準**:
- [ ] `SYNTHESIS_TOOLS` に5ツール定義
- [ ] `SYNTHESIS_PROMPTS` に2プロンプト定義
- [ ] 既存MCPサーバーへの統合
- [ ] ユニットテスト（7件以上）

**テストファイル**: `packages/mcp-server/src/tools/__tests__/synthesis-tools.test.ts`

---

### TSK-INT-104: SynthesisCLI 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-INT-104 |
| **対応設計** | DES-INT-104 |
| **対応要件** | REQ-INT-104 |
| **優先度** | P1 |
| **推定工数** | 3時間 |
| **依存** | TSK-INT-101 |

**実装内容**:
1. `packages/core/src/cli/SynthesisCLI.ts` を作成
2. 5つのCLIコマンド
3. 既存CLIへの統合

**受け入れ基準**:
- [ ] `synthesize` コマンド実装
- [ ] `synthesize:pbe` コマンド実装
- [ ] `library:learn` コマンド実装
- [ ] `library:query` コマンド実装
- [ ] `library:stats` コマンド実装
- [ ] 既存CLIへの統合
- [ ] ユニットテスト（5件以上）

**テストファイル**: `packages/core/src/cli/__tests__/SynthesisCLI.test.ts`

---

## 6. トレーサビリティマトリクス

### 6.1 要件 → 設計 → タスク

| 要件ID | 設計ID | タスクID | 優先度 |
|--------|--------|---------|--------|
| REQ-LL-101 | DES-LL-101 | TSK-LL-101 | P0 |
| REQ-LL-102 | DES-LL-102 | TSK-LL-102 | P0 |
| REQ-LL-103 | DES-LL-103 | TSK-LL-103 | P1 |
| REQ-LL-104 | DES-LL-104 | TSK-LL-104 | P0 |
| REQ-LL-105 | DES-LL-105 | TSK-LL-105 | P1 |
| REQ-LL-106 | DES-LL-106 | TSK-LL-106 | P1 |
| REQ-LL-107 | DES-LL-107 | TSK-LL-107 | P0 |
| REQ-LL-108 | DES-LL-108 | TSK-LL-108 | P2 |
| - | DES-LL-* | TSK-LL-109 | P0 |
| REQ-NS-101 | DES-NS-101 | TSK-NS-101 | P0 |
| REQ-NS-102 | DES-NS-102 | TSK-NS-102 | P0 |
| REQ-NS-103 | DES-NS-103 | TSK-NS-103 | P0 |
| REQ-NS-104 | DES-NS-104 | TSK-NS-104 | P1 |
| REQ-NS-105 | DES-NS-105 | TSK-NS-105 | P1 |
| REQ-NS-106 | DES-NS-106 | TSK-NS-106 | P1 |
| REQ-NS-107 | DES-NS-107 | TSK-NS-107 | P2 |
| - | DES-NS-* | TSK-NS-108 | P0 |
| REQ-SY-101 | DES-SY-101 | TSK-SY-101 | P0 |
| REQ-SY-102 | DES-SY-102 | TSK-SY-102 | P0 |
| REQ-SY-103 | DES-SY-103 | TSK-SY-103 | P1 |
| REQ-SY-104 | DES-SY-104 | TSK-SY-104 | P1 |
| REQ-SY-105 | DES-SY-105 | TSK-SY-105 | P1 |
| REQ-SY-106 | DES-SY-106 | TSK-SY-106 | P2 |
| - | DES-SY-* | TSK-SY-107 | P0 |
| REQ-INT-101 | DES-INT-101 | TSK-INT-101 | P0 |
| REQ-INT-102 | DES-INT-102 | TSK-INT-102 | P0 |
| REQ-INT-103 | DES-INT-103 | TSK-INT-103 | P1 |
| REQ-INT-104 | DES-INT-104 | TSK-INT-104 | P1 |

---

## 7. 依存関係グラフ

```
Phase A: 基盤（並列実行可能）
┌──────────────────────────────────────────────────────────────────────────┐
│                                                                          │
│  TSK-LL-101 ──┐                                                         │
│  TSK-LL-102   │                                                         │
│  TSK-LL-104 ──┼──→ TSK-LL-103 ──→ TSK-LL-105                           │
│               │                   TSK-LL-106                           │
│               └──→ TSK-LL-107 ──→ TSK-LL-108                           │
│                                                                          │
│  TSK-NS-101 ──→ TSK-NS-104                                              │
│  TSK-NS-102 ──→ TSK-NS-107                                              │
│  TSK-NS-103                                                              │
│  TSK-NS-105 ──→ TSK-NS-106                                              │
│                                                                          │
│  TSK-SY-101 ──┬──→ TSK-SY-103                                           │
│  TSK-SY-102 ──┘    TSK-SY-104                                           │
│  TSK-SY-105        TSK-SY-106                                           │
│                                                                          │
│  TSK-INT-102 (独立)                                                     │
│                                                                          │
└──────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
Phase B: 統合（順次実行）
┌──────────────────────────────────────────────────────────────────────────┐
│                                                                          │
│  TSK-LL-109 ──┐                                                         │
│  TSK-NS-108 ──┼──→ TSK-INT-101 ──→ TSK-INT-103                         │
│  TSK-SY-107 ──┘                   TSK-INT-104                          │
│                                                                          │
└──────────────────────────────────────────────────────────────────────────┘
```

---

## 8. 実行計画

### 8.1 推奨実行順序

| Day | タスク | 推定時間 | 累計 |
|-----|--------|---------|------|
| 1 | TSK-LL-101, TSK-LL-102, TSK-LL-104, TSK-INT-102 | 12h | 12h |
| 2 | TSK-NS-101, TSK-NS-102, TSK-NS-103, TSK-NS-105 | 11h | 23h |
| 3 | TSK-SY-101, TSK-SY-102, TSK-SY-105 | 9h | 32h |
| 4 | TSK-LL-103, TSK-LL-105, TSK-LL-106, TSK-LL-107 | 9h | 41h |
| 5 | TSK-NS-104, TSK-NS-106, TSK-SY-103, TSK-SY-104 | 9h | 50h |
| 6 | TSK-LL-108, TSK-NS-107, TSK-SY-106 | 4h | 54h |
| 7 | TSK-LL-109, TSK-NS-108, TSK-SY-107 | 6h | 60h |
| 8 | TSK-INT-101 | 4h | 64h |
| 9 | TSK-INT-103, TSK-INT-104 | 6h | 70h |

### 8.2 クリティカルパス

```
TSK-LL-101 → TSK-LL-107 → TSK-LL-109 → TSK-INT-101 → TSK-INT-103
   3h           3h            2h           4h            3h
                                                    = 15h
```

---

## 9. リスクと対策

| リスク | 影響 | 確率 | 対策 |
|--------|------|------|------|
| 既存API互換性問題 | 高 | 中 | 統合タスクで回帰テスト実施 |
| パフォーマンス目標未達 | 中 | 中 | ベンチマークテストを早期実施 |
| 依存パッケージ更新 | 低 | 低 | package.jsonをロック |

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
| 1.1.0 | 2026-01-08 | レビュー指摘対応: サマリー数値修正、工数統一、TSK-NS-108依存調整 | AI Agent |

---

**Document ID**: TSK-v2.2.0-Advanced-Learning  
**Classification**: Internal  
**憲法条項準拠**: Article V (Traceability), Article III (Test-First)
