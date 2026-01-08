# MUSUBIX v2.2.0 要件定義書 - Advanced Learning Enhancement

| 項目 | 内容 |
|------|------|
| **ドキュメントID** | REQ-v2.2.0-Advanced-Learning |
| **バージョン** | 1.1.0 |
| **作成日** | 2026-01-08 |
| **最終更新** | 2026-01-08 |
| **ステータス** | レビュー済み |
| **優先度** | P0 (Critical) |

---

## 1. エグゼクティブサマリー

### 1.1 背景

MUSUBIX v2.0.0でDeep Symbolic Integration（DFG/CFG、Lean 4、YATA Scale）、v2.1.0でSecurity Enhancement（EPICs 1-4）が完了した。v2.2.0ではロードマップPhase 2「Advanced Learning」として、既存の3つの学習関連パッケージを強化する：

| パッケージ | 現状（v2.1.x実装済み） | v2.2.0目標 |
|-----------|----------------------|-----------|
| `@nahisaho/musubix-library-learner` | REQ-LL-001〜004: 基本パターンマイニング、E-graph最適化 | DreamCoder型階層的抽象化の完全実装 |
| `@nahisaho/musubix-neural-search` | REQ-NS-001: 分岐スコアリング、ビーム探索 | 学習ベースプルーニング、適応的探索 |
| `@nahisaho/musubix-synthesis` | REQ-SYN-001: DSLビルダー、PBE合成 | Witness Function強化、メタ学習統合 |

> **注**: 本要件定義では既存実装（REQ-LL-001〜004, REQ-NS-001, REQ-SYN-001）との競合を避けるため、  
> 新規要件には **1xx番台** のIDを使用する（REQ-LL-101〜, REQ-NS-101〜, REQ-SY-101〜）

### 1.2 目標

- **ライブラリ学習削減率**: 10^6+ 探索空間削減
- **PBE合成成功率**: >80%（現状推定: 60%）
- **探索効率向上**: 3倍以上の速度改善
- **API互換性**: v2.1.xとの100%後方互換

### 1.3 KPI測定方法

| KPI | 測定方法 | ベースライン | 目標値 |
|-----|---------|-------------|--------|
| 探索空間削減率 | `(untyped_nodes - typed_nodes) / untyped_nodes` | 0% | 90%+ |
| PBE成功率 | `successful_syntheses / total_attempts` on benchmark suite | 60% | 80%+ |
| 探索速度改善 | `baseline_time / optimized_time` on standard tasks | 1.0x | 3.0x+ |
| ライブラリ圧縮率 | `compressed_size / original_size` | 100% | 70%以下 |
| キャッシュヒット率 | `cache_hits / (cache_hits + cache_misses)` | N/A | 80%+ |

**ベンチマークスイート**: `packages/synthesis/benchmarks/` に標準テストケース100件を用意

---

## 2. 要件一覧

### 2.1 EPIC概要

| EPIC ID | 名称 | 対象パッケージ | 要件数 | 既存REQとの関係 |
|---------|------|---------------|--------|----------------|
| EPIC-LL | Library Learner Enhancement | `@nahisaho/musubix-library-learner` | 8 | REQ-LL-001〜004を拡張 |
| EPIC-NS | Neural Search Guidance | `@nahisaho/musubix-neural-search` | 7 | REQ-NS-001を拡張 |
| EPIC-SY | Synthesis PBE Enhancement | `@nahisaho/musubix-synthesis` | 6 | REQ-SYN-001を拡張 |
| EPIC-INT | Integration & Orchestration | 複合 | 4 | 新規 |

**合計**: 25要件（新規ID: REQ-LL-101〜, REQ-NS-101〜, REQ-SY-101〜, REQ-INT-101〜）

---

## 3. EPIC-LL: Library Learner Enhancement

> **既存実装**: REQ-LL-001（階層的抽象化）、REQ-LL-002（ライブラリ成長）、REQ-LL-003（型指向探索）、REQ-LL-004（E-graph最適化）

### 3.1 機能要件

#### REQ-LL-101: 階層的抽象化エンジン強化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-101 |
| **優先度** | P0 |
| **ステータス** | 新規（REQ-LL-001を拡張） |

**EARS形式**:
> WHEN the library learner processes a code corpus with repeated patterns, THE system SHALL extract hierarchical abstractions at minimum 3 levels of granularity (token, expression, function) within 10 seconds per 1000 LOC.

**受け入れ基準**:
- [ ] 3レベル以上の階層的抽象化を抽出できる
- [ ] 1000 LOCあたり10秒以内で処理完了
- [ ] 抽出されたパターンは再利用可能な形式で保存される

---

#### REQ-LL-102: 型主導探索強化（Type-Directed Search Enhancement）

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-102 |
| **優先度** | P0 |
| **ステータス** | 新規（REQ-LL-003を拡張） |

**EARS形式**:
> WHILE the system is synthesizing code from library primitives, THE system SHALL use type signatures to prune the search space, reducing exploration by at least 90% compared to untyped enumeration.

**受け入れ基準**:
- [ ] 型シグネチャに基づく探索空間の枝刈りを実装
- [ ] 型無し列挙と比較して90%以上の探索空間削減
- [ ] TypeScriptの型システムと互換

---

#### REQ-LL-103: 反復圧縮（Iterative Compression）

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-103 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> WHEN the library contains more than 100 patterns, THE system SHALL perform iterative compression to merge similar patterns, achieving at least 30% reduction in library size while maintaining 95% pattern coverage.

**受け入れ基準**:
- [ ] 100パターン以上で自動圧縮トリガー
- [ ] 30%以上のライブラリサイズ削減
- [ ] 95%以上のパターンカバレッジ維持

---

#### REQ-LL-104: E-graph等価性発見強化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-104 |
| **優先度** | P0 |
| **ステータス** | 強化（REQ-LL-004を拡張） |

**EARS形式**:
> WHEN analyzing code expressions, THE system SHALL use E-graph rewriting to discover semantically equivalent forms, supporting at least 50 rewrite rules including algebraic, Boolean, and string operations.

**受け入れ基準**:
- [ ] 50種類以上のリライトルール実装
- [ ] 代数的、Boolean、文字列操作を含む
- [ ] 等価クラスの効率的なマージ

---

#### REQ-LL-105: パターンバージョニング

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-105 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL maintain version history for each pattern in the library, supporting rollback to previous versions and tracking evolution metrics.

**受け入れ基準**:
- [ ] パターンのバージョン履歴を保持
- [ ] 任意のバージョンへのロールバック機能
- [ ] 進化メトリクス（使用頻度、精度変化）の追跡

---

#### REQ-LL-106: ドメイン特化抽象化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-106 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> WHERE a domain-specific ontology is available, THE system SHALL generate domain-aware abstractions that respect semantic constraints defined in the ontology.

**受け入れ基準**:
- [ ] オントロジーからの制約読み取り
- [ ] ドメイン概念を反映した抽象化生成
- [ ] 62ドメイン対応（既存MUSUBIXドメイン）

---

#### REQ-LL-107: 増分学習サポート

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-107 |
| **優先度** | P0 |
| **ステータス** | 新規 |

**EARS形式**:
> WHEN new code is added to the corpus, THE system SHALL update the pattern library incrementally without requiring full re-computation, completing updates within 5 seconds for changes under 500 LOC.

**受け入れ基準**:
- [ ] 完全再計算なしの増分更新
- [ ] 500 LOC以下の変更に対し5秒以内
- [ ] ライブラリ整合性の維持

---

#### REQ-LL-108: 学習メトリクス・可視化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-LL-108 |
| **優先度** | P2 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL provide comprehensive learning metrics including pattern usage frequency, compression ratio, and exploration reduction rate, exportable in JSON and Markdown formats.

**受け入れ基準**:
- [ ] パターン使用頻度の追跡
- [ ] 圧縮率と探索削減率の計算
- [ ] JSON/Markdown形式でのエクスポート

---

## 4. EPIC-NS: Neural Search Guidance

> **既存実装**: REQ-NS-001（分岐スコアリング）

### 4.1 機能要件

#### REQ-NS-101: 学習ベースプルーニング強化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-NS-101 |
| **優先度** | P0 |
| **ステータス** | 強化（REQ-NS-001を拡張） |

**EARS形式**:
> WHILE exploring the search space, THE system SHALL use learned pruning policies to eliminate low-potential branches, achieving at least 70% reduction in explored nodes while maintaining solution quality.

**受け入れ基準**:
- [ ] 学習済みプルーニングポリシーの適用
- [ ] 探索ノード数70%以上削減
- [ ] ソリューション品質の維持（95%以上）

---

#### REQ-NS-102: 適応的ビーム幅調整

| 項目 | 内容 |
|------|------|
| **ID** | REQ-NS-102 |
| **優先度** | P0 |
| **ステータス** | 新規 |

**EARS形式**:
> WHEN search progress stalls (no improvement for 10 iterations), THE system SHALL dynamically increase beam width by 50% up to a maximum of 100 beams to escape local optima.

**受け入れ基準**:
- [ ] 探索停滞の自動検出
- [ ] ビーム幅の動的調整（50%増加）
- [ ] 最大100ビームの制限

---

#### REQ-NS-103: コンテキスト認識スコアリング強化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-NS-103 |
| **優先度** | P0 |
| **ステータス** | 強化（REQ-NS-001を拡張） |

**EARS形式**:
> WHEN scoring candidate solutions, THE system SHALL incorporate project context (existing code patterns, naming conventions, type usage) with at least 0.3 weight contribution to the final score.

**受け入れ基準**:
- [ ] プロジェクトコンテキストの取り込み
- [ ] スコア寄与度30%以上
- [ ] 既存コードパターンとの整合性評価

---

#### REQ-NS-104: オンライン学習更新

| 項目 | 内容 |
|------|------|
| **ID** | REQ-NS-104 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> WHEN a user accepts or rejects a synthesis result, THE system SHALL update the scoring model online, reflecting the feedback within the next 3 search operations.

**受け入れ基準**:
- [ ] accept/rejectフィードバックの収集
- [ ] 3回の探索以内でモデル更新反映
- [ ] プライバシー保護（ローカルストレージのみ）

---

#### REQ-NS-105: 埋め込みキャッシュ

| 項目 | 内容 |
|------|------|
| **ID** | REQ-NS-105 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL cache computed embeddings with LRU eviction policy, supporting up to 10,000 entries and achieving 80% cache hit rate for repeated queries.

**受け入れ基準**:
- [ ] LRU方式の埋め込みキャッシュ
- [ ] 10,000エントリ容量
- [ ] 80%以上のキャッシュヒット率

---

#### REQ-NS-106: マルチモーダル入力サポート

| 項目 | 内容 |
|------|------|
| **ID** | REQ-NS-106 |
| **優先度** | P2 |
| **ステータス** | 新規 |

**EARS形式**:
> WHERE input includes both natural language description and code examples, THE system SHALL combine embeddings from both modalities with configurable fusion strategy (concat, attention, or weighted sum).

**受け入れ基準**:
- [ ] 自然言語+コード例の複合入力
- [ ] 3種類の融合戦略（concat, attention, weighted sum）
- [ ] 融合戦略の設定可能性

---

#### REQ-NS-107: 探索トラジェクトリログ強化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-NS-107 |
| **優先度** | P1 |
| **ステータス** | 強化 |

**EARS形式**:
> THE system SHALL log complete search trajectories including all explored branches, scores, and pruning decisions, exportable for analysis and model training.

**受け入れ基準**:
- [ ] 探索分岐の完全ログ
- [ ] スコアとプルーニング決定の記録
- [ ] 分析・学習用エクスポート機能

---

## 5. EPIC-SY: Synthesis PBE Enhancement

> **既存実装**: REQ-SYN-001（DSL Definition Framework）

### 5.1 機能要件

#### REQ-SY-101: Witness Function強化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-SY-101 |
| **優先度** | P0 |
| **ステータス** | 強化（REQ-SYN-001を拡張） |

**EARS形式**:
> WHEN synthesizing from input-output examples, THE system SHALL use witness functions to decompose the problem, supporting at least 20 DSL operators with custom witness implementations.

**受け入れ基準**:
- [ ] 20種類以上のDSL演算子対応
- [ ] カスタムWitness関数の実装
- [ ] 問題分解の自動化

---

#### REQ-SY-102: バージョン空間代数強化

| 項目 | 内容 |
|------|------|
| **ID** | REQ-SY-102 |
| **優先度** | P0 |
| **ステータス** | 強化 |

**EARS形式**:
> THE system SHALL maintain version spaces for partial programs, supporting intersection, union, and negation operations with O(n log n) complexity for n candidate programs.

**受け入れ基準**:
- [ ] バージョン空間の交差・和集合・否定操作
- [ ] O(n log n)の計算量
- [ ] 部分プログラムの効率的管理

---

#### REQ-SY-103: メタ学習統合

| 項目 | 内容 |
|------|------|
| **ID** | REQ-SY-103 |
| **優先度** | P0 |
| **ステータス** | 新規 |

**EARS形式**:
> WHEN similar synthesis tasks are encountered, THE system SHALL apply meta-learned strategies from previous successful syntheses, reducing average synthesis time by at least 50%.

**受け入れ基準**:
- [ ] 類似タスクの自動認識
- [ ] メタ学習戦略の適用
- [ ] 合成時間50%以上削減

---

#### REQ-SY-104: DSL自動拡張

| 項目 | 内容 |
|------|------|
| **ID** | REQ-SY-104 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> WHEN synthesis fails due to missing operators, THE system SHALL suggest DSL extensions based on the gap analysis, providing at least 3 candidate operator definitions.

**受け入れ基準**:
- [ ] 合成失敗時のギャップ分析
- [ ] 3つ以上の演算子候補提案
- [ ] 提案の優先順位付け

---

#### REQ-SY-105: 例示の品質評価

| 項目 | 内容 |
|------|------|
| **ID** | REQ-SY-105 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> WHEN input-output examples are provided, THE system SHALL evaluate example quality and suggest additional examples that would improve synthesis precision, identifying ambiguous cases.

**受け入れ基準**:
- [ ] 例示の曖昧性検出
- [ ] 追加例の自動提案
- [ ] 精度向上への貢献度評価

---

#### REQ-SY-106: 合成結果の説明生成

| 項目 | 内容 |
|------|------|
| **ID** | REQ-SY-106 |
| **優先度** | P2 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL generate human-readable explanations for synthesized programs, describing the transformation logic in natural language with confidence scores.

**受け入れ基準**:
- [ ] 自然言語での説明生成
- [ ] 変換ロジックの記述
- [ ] 信頼度スコアの付与

---

## 6. EPIC-INT: Integration & Orchestration

### 6.1 機能要件

#### REQ-INT-101: 3パッケージ統合オーケストレーション

| 項目 | 内容 |
|------|------|
| **ID** | REQ-INT-101 |
| **優先度** | P0 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL provide unified orchestration API that coordinates library-learner, neural-search, and synthesis packages, enabling end-to-end program synthesis from natural language specifications.

**受け入れ基準**:
- [ ] 統一オーケストレーションAPI
- [ ] 3パッケージの協調動作
- [ ] 自然言語→プログラム合成のE2Eフロー

---

#### REQ-INT-102: パイプライン構成

| 項目 | 内容 |
|------|------|
| **ID** | REQ-INT-102 |
| **優先度** | P0 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL support configurable synthesis pipelines with at least 3 predefined configurations: fast (speed priority), accurate (quality priority), and balanced (default).

**受け入れ基準**:
- [ ] 3種類のプリセット構成
- [ ] カスタムパイプライン定義
- [ ] 動的な構成切り替え

---

#### REQ-INT-103: MCP Toolsへのエクスポート

| 項目 | 内容 |
|------|------|
| **ID** | REQ-INT-103 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL expose core synthesis capabilities as MCP tools, integrating with the existing musubix-mcp-server infrastructure.

**受け入れ基準**:
- [ ] MCPツールとしてのエクスポート
- [ ] 既存MCPサーバーとの統合
- [ ] ツールドキュメント生成

---

#### REQ-INT-104: CLI拡張

| 項目 | 内容 |
|------|------|
| **ID** | REQ-INT-104 |
| **優先度** | P1 |
| **ステータス** | 新規 |

**EARS形式**:
> THE system SHALL provide CLI commands for synthesis operations: `musubix synth pbe`, `musubix synth from-spec`, and `musubix synth learn`, following existing CLI conventions.

**受け入れ基準**:
- [ ] `musubix synth pbe` - PBE合成
- [ ] `musubix synth from-spec` - 仕様からの合成
- [ ] `musubix synth learn` - ライブラリ学習

---

## 7. 非機能要件

### 7.1 性能要件

| ID | 要件 | 基準 |
|----|------|------|
| NFR-001 | 合成レイテンシ | 単純タスク < 2秒、複雑タスク < 30秒 |
| NFR-002 | メモリ使用量 | ライブラリ10,000パターンで < 500MB |
| NFR-003 | 並列処理 | 最大8並列ビーム探索 |

### 7.2 互換性要件

| ID | 要件 | 基準 |
|----|------|------|
| NFR-004 | API後方互換性 | v2.1.x APIとの100%互換 |
| NFR-005 | Node.jsバージョン | 20.0.0以上 |
| NFR-006 | TypeScriptバージョン | 5.3以上 |

### 7.3 テスト要件

| ID | 要件 | 基準 |
|----|------|------|
| NFR-007 | ユニットテストカバレッジ | 80%以上 |
| NFR-008 | 統合テスト | 全EPICに対する統合テスト |
| NFR-009 | ベンチマークテスト | 性能回帰の自動検出 |

---

## 8. トレーサビリティ

### 8.1 既存要件との関係

| 既存要件ID | パッケージ | 拡張要件ID |
|-----------|-----------|-----------|
| REQ-LL-001 | library-learner/types.ts | REQ-LL-101（階層的抽象化強化） |
| REQ-LL-002 | library-learner/types.ts | - |
| REQ-LL-003 | library-learner/types.ts | REQ-LL-102（型主導探索強化） |
| REQ-LL-004 | library-learner/types.ts | REQ-LL-104（E-graph強化） |
| REQ-NS-001 | neural-search/types.ts | REQ-NS-101, REQ-NS-103 |
| REQ-SYN-001 | synthesis/types.ts | REQ-SY-101（Witness強化） |

### 8.2 要件→設計マッピング（予定）

| 要件ID | 設計ID（予定） |
|--------|--------------|
| REQ-LL-101〜108 | DES-LL-* |
| REQ-NS-101〜107 | DES-NS-* |
| REQ-SY-101〜106 | DES-SY-* |
| REQ-INT-101〜104 | DES-INT-* |

### 8.3 依存関係（詳細）

```
EPIC-INT (統合) ─────────────────────────────────────────────
    │
    ├── REQ-INT-101 ← REQ-INT-102 (パイプライン構成が先)
    │       │
    │       ├── depends on: EPIC-LL, EPIC-NS, EPIC-SY (全P0完了後)
    │       │
    │       └── REQ-INT-103 ← REQ-INT-104 (MCPが先、CLIが後)
    │
EPIC-LL (Library Learner) ─────────────────────────────────────
    │
    ├── REQ-LL-101 (階層的抽象化) ← 基盤、最初に実装
    │       │
    │       ├── REQ-LL-102 (型主導探索) ← 101に依存
    │       │       │
    │       │       └── REQ-LL-103 (反復圧縮) ← 102に依存
    │       │
    │       └── REQ-LL-104 (E-graph) ← 101と並行可能
    │
    ├── REQ-LL-105 (バージョニング) ← 独立、任意タイミング
    ├── REQ-LL-106 (ドメイン特化) ← 101完了後
    ├── REQ-LL-107 (増分学習) ← 101, 102完了後
    └── REQ-LL-108 (メトリクス) ← 最後、全機能完了後
    │
EPIC-NS (Neural Search) ─────────────────────────────────────
    │
    ├── REQ-NS-101 (プルーニング) ← 基盤、最初に実装
    │       │
    │       ├── REQ-NS-102 (適応ビーム幅) ← 101に依存
    │       │
    │       └── REQ-NS-103 (コンテキストスコア) ← 101と並行可能
    │
    ├── REQ-NS-104 (オンライン学習) ← 101完了後
    ├── REQ-NS-105 (キャッシュ) ← 独立、任意タイミング
    ├── REQ-NS-106 (マルチモーダル) ← 103完了後
    └── REQ-NS-107 (トラジェクトリログ) ← 101完了後
    │
EPIC-SY (Synthesis) ─────────────────────────────────────────
    │
    ├── REQ-SY-101 (Witness強化) ← 基盤、最初に実装
    │       │
    │       ├── REQ-SY-102 (バージョン空間) ← 101と並行可能
    │       │
    │       └── REQ-SY-103 (メタ学習) ← 101, 102完了後
    │
    ├── REQ-SY-104 (DSL拡張) ← 101完了後
    ├── REQ-SY-105 (例示品質) ← 101完了後
    └── REQ-SY-106 (説明生成) ← 103完了後
```

### 8.4 実装順序（推奨）

| フェーズ | 要件ID | 理由 |
|---------|--------|------|
| 1 | REQ-LL-101, REQ-NS-101, REQ-SY-101 | 各EPICの基盤 |
| 2 | REQ-LL-102, REQ-LL-104, REQ-NS-102, REQ-NS-103, REQ-SY-102 | P0要件 |
| 3 | REQ-LL-107, REQ-SY-103 | 残りのP0 |
| 4 | REQ-INT-101, REQ-INT-102 | 統合P0 |
| 5 | P1要件（LL-103,105,106, NS-104,105,107, SY-104,105, INT-103,104） | |
| 6 | P2要件（LL-108, NS-106, SY-106） | |

---

## 9. リスクと緩和策

| リスク | 影響度 | 発生確率 | 緩和策 |
|--------|-------|---------|--------|
| E-graph実装の複雑さ | 高 | 中 | 既存egg-rsの調査、段階的実装 |
| 性能目標未達 | 高 | 低 | 早期ベンチマーク、プロファイリング |
| API互換性破壊 | 高 | 低 | 非破壊的追加のみ、deprecation期間設定 |
| テスト不足 | 中 | 中 | TDDの徹底、カバレッジ監視 |

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
| 1.1.0 | 2026-01-08 | レビュー指摘対応: 要件ID体系を1xx番台に変更、KPI測定方法追加、依存関係詳細化、既存REQとの関係明記 | AI Agent |

---

**Document ID**: REQ-v2.2.0-Advanced-Learning  
**Classification**: Internal  
**憲法条項準拠**: Article IV (EARS Format), Article V (Traceability)
