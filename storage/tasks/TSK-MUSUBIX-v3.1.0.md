# MUSUBIX v3.1.0 タスク分解書

**文書ID**: TSK-MUSUBIX-v3.1.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-13  
**ステータス**: Draft  
**参照文書**: REQ-MUSUBIX-v3.1.0.md, DES-MUSUBIX-v3.1.0.md

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.1.0の実装タスクを分解・定義する。15設計（DES-*）から導出された実装タスクを、依存関係と実行順序を考慮して記述する。

### 1.2 タスクID体系

```
TSK-<カテゴリ>-<連番>-<サブタスク>
```

例: `TSK-CLI-001-1`（CLI機能の1番目のタスクの1番目のサブタスク）

### 1.3 工数見積もり基準

| サイズ | 工数 | 説明 |
|--------|------|------|
| S | 1-2時間 | 単一ファイルの小修正 |
| M | 2-4時間 | 複数ファイルまたは新規コンポーネント |
| L | 4-8時間 | 複数コンポーネント連携 |
| XL | 8時間以上 | 大規模な機能追加 |

---

## 2. タスク一覧（サマリー）

| タスクID | 名称 | 設計ID | 優先度 | サイズ | 依存 |
|----------|------|--------|--------|--------|------|
| TSK-CLI-001 | initパス正規化 | DES-CLI-001 | P0 | M | - |
| TSK-CLI-002 | feedbackガイダンス | DES-CLI-002 | P1 | M | - |
| TSK-CLI-003 | scaffoldドメインモデル | DES-CLI-003 | P1 | L | TSK-PAT-001 |
| TSK-VAL-001 | Markdown内EARS検出 | DES-VAL-001 | P0 | M | - |
| TSK-VAL-002 | 設計トレーサビリティ | DES-VAL-002 | P1 | M | - |
| TSK-LRN-001 | パターン推薦 | DES-LRN-001 | P1 | M | - |
| TSK-LRN-002 | ドメイン固有パターン | DES-LRN-002 | P1 | M | TSK-LRN-001 |
| TSK-PAT-001 | 同時実行パターン | DES-PAT-001 | P0 | M | - |
| TSK-PAT-002 | 時間制約パターン | DES-PAT-002 | P1 | M | - |
| TSK-GEN-001 | VO自動生成 | DES-GEN-001 | P1 | L | - |
| TSK-GEN-002 | Status Transition Map | DES-GEN-002 | P1 | M | - |
| TSK-TST-001 | 状態遷移テスト生成 | DES-TST-001 | P1 | M | TSK-GEN-002 |
| TSK-TST-002 | カウンターリセット | DES-TST-002 | P0 | S | - |
| TSK-NFR-001 | アクショナブルエラー | DES-NFR-001 | P1 | M | - |
| TSK-NFR-002 | 性能最適化 | DES-NFR-002 | P2 | L | - |

**合計工数見積もり**: 約40-60時間

---

## 3. 実行フェーズ

### フェーズ1: P0タスク（必須）

| 順序 | タスクID | 名称 | 依存 |
|------|----------|------|------|
| 1 | TSK-CLI-001 | initパス正規化 | - |
| 2 | TSK-VAL-001 | Markdown内EARS検出 | - |
| 3 | TSK-PAT-001 | 同時実行パターン | - |
| 4 | TSK-TST-002 | カウンターリセット | - |

### フェーズ2: P1タスク（重要）

| 順序 | タスクID | 名称 | 依存 |
|------|----------|------|------|
| 5 | TSK-CLI-002 | feedbackガイダンス | - |
| 6 | TSK-VAL-002 | 設計トレーサビリティ | - |
| 7 | TSK-PAT-002 | 時間制約パターン | - |
| 8 | TSK-LRN-001 | パターン推薦 | - |
| 9 | TSK-LRN-002 | ドメイン固有パターン | TSK-LRN-001 |
| 10 | TSK-GEN-001 | VO自動生成 | - |
| 11 | TSK-GEN-002 | Status Transition Map | - |
| 12 | TSK-TST-001 | 状態遷移テスト生成 | TSK-GEN-002 |
| 13 | TSK-CLI-003 | scaffoldドメインモデル | TSK-PAT-001 |
| 14 | TSK-NFR-001 | アクショナブルエラー | - |

### フェーズ3: P2タスク（任意）

| 順序 | タスクID | 名称 | 依存 |
|------|----------|------|------|
| 15 | TSK-NFR-002 | 性能最適化 | - |

---

## 4. タスク詳細

---

### 4.1 CLI機能タスク

---

#### TSK-CLI-001: initコマンドパス正規化

| 属性 | 値 |
|------|-----|
| **ID** | TSK-CLI-001 |
| **設計ID** | DES-CLI-001 |
| **要件ID** | REQ-CLI-001 |
| **優先度** | P0 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-CLI-001-1 | `normalizePath()` 関数実装 | 1h | AI Agent |
| TSK-CLI-001-2 | `isAbsolutePath()` 関数実装 | 0.5h | AI Agent |
| TSK-CLI-001-3 | `validatePath()` エラーメッセージ改善 | 0.5h | AI Agent |
| TSK-CLI-001-4 | 既存テストに絶対パスケース追加 | 1h | AI Agent |
| TSK-CLI-001-5 | 統合テスト実行・確認 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/cli/commands/init.ts      # 主な修正
packages/core/src/cli/commands/init.test.ts # テスト追加
```

**テスト観点**:

- [ ] 絶対パス `/home/user/project` → 正しく解決
- [ ] 相対パス `./project` → cwd + project に解決
- [ ] `--force` オプション併用時の動作
- [ ] 無効パス（存在しない親ディレクトリ）のエラーメッセージ

**受入基準チェック**:

- [ ] AC-001-1: 絶対パステスト合格
- [ ] AC-001-2: 相対パステスト合格
- [ ] AC-001-3: --forceテスト合格
- [ ] AC-001-4: エラーメッセージテスト合格

---

#### TSK-CLI-002: feedbackコマンドガイダンス

| 属性 | 値 |
|------|-----|
| **ID** | TSK-CLI-002 |
| **設計ID** | DES-CLI-002 |
| **要件ID** | REQ-CLI-002 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-CLI-002-1 | Commander `-a` エイリアス追加 | 0.5h | AI Agent |
| TSK-CLI-002-2 | `showGuidance()` 関数実装 | 1h | AI Agent |
| TSK-CLI-002-3 | `InteractiveFeedbackBuilder` クラス実装 | 1.5h | AI Agent |
| TSK-CLI-002-4 | ユニットテスト追加 | 0.5h | AI Agent |
| TSK-CLI-002-5 | 手動動作確認 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/cli/commands/learn.ts           # 主な修正
packages/core/src/cli/commands/learn.test.ts      # テスト追加
packages/core/src/cli/interactive-builder.ts      # 新規作成
```

**テスト観点**:

- [ ] 必須オプション不足時のガイダンス表示
- [ ] `-a design` エイリアス動作
- [ ] `--interactive` モード起動・入力フロー

**受入基準チェック**:

- [ ] AC-002-1: ガイダンス表示テスト合格
- [ ] AC-002-2: エイリアステスト合格
- [ ] AC-002-3: インタラクティブモードテスト合格

---

#### TSK-CLI-003: scaffoldドメインモデル生成

| 属性 | 値 |
|------|-----|
| **ID** | TSK-CLI-003 |
| **設計ID** | DES-CLI-003 |
| **要件ID** | REQ-CLI-003 |
| **優先度** | P1 |
| **サイズ** | L（4-8時間） |
| **依存タスク** | TSK-PAT-001（パターン定義を使用） |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-CLI-003-1 | `EntityTemplateFactory` クラス実装 | 2h | AI Agent |
| TSK-CLI-003-2 | `PatternApplicator` クラス実装 | 1.5h | AI Agent |
| TSK-CLI-003-3 | テストファイルテンプレート実装 | 1h | AI Agent |
| TSK-CLI-003-4 | CLI `scaffold domain-model` コマンド追加 | 1h | AI Agent |
| TSK-CLI-003-5 | ユニットテスト追加 | 1h | AI Agent |
| TSK-CLI-003-6 | E2Eテスト（実際のファイル生成確認） | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/cli/commands/scaffold.ts           # 修正
packages/core/src/codegen/entity-template-factory.ts # 新規作成
packages/core/src/codegen/pattern-applicator.ts      # 新規作成
packages/core/src/codegen/templates/entity.ts        # 新規作成
packages/core/src/codegen/templates/entity.test.ts   # 新規作成
```

**テスト観点**:

- [ ] エンティティファイル生成（`src/domain/<entity>.ts`）
- [ ] テストファイル生成（`src/domain/<entity>.test.ts`）
- [ ] BP-CODE-001〜005パターン適用確認
- [ ] 複数エンティティ一括生成

**受入基準チェック**:

- [ ] AC-003-1: エンティティファイル生成
- [ ] AC-003-2: テストファイル生成
- [ ] AC-003-3: Result型適用確認
- [ ] AC-003-4: Branded ID適用確認
- [ ] AC-003-5: beforeEach + resetCounter確認

---

### 4.2 検証機能タスク

---

#### TSK-VAL-001: Markdown内EARS検出

| 属性 | 値 |
|------|-----|
| **ID** | TSK-VAL-001 |
| **設計ID** | DES-VAL-001 |
| **要件ID** | REQ-VAL-001 |
| **優先度** | P0 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-VAL-001-1 | `MarkdownEarsParser` クラス実装 | 1.5h | AI Agent |
| TSK-VAL-001-2 | テーブル行パース実装 | 0.5h | AI Agent |
| TSK-VAL-001-3 | 箇条書きパース実装 | 0.5h | AI Agent |
| TSK-VAL-001-4 | コードブロックスキップ実装 | 0.5h | AI Agent |
| TSK-VAL-001-5 | 既存 `EarsValidator` への統合 | 0.5h | AI Agent |
| TSK-VAL-001-6 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/validators/markdown-ears-parser.ts  # 新規作成
packages/core/src/validators/ears-validator.ts        # 修正
packages/core/src/validators/ears-validator.test.ts   # テスト追加
```

**テスト観点**:

- [ ] テーブル形式 `| REQ-001 | WHEN... |` 検出
- [ ] 箇条書き形式 `- WHEN...` 検出
- [ ] コードブロック内は検出対象外
- [ ] 行番号・パターン種別の正確性

**受入基準チェック**:

- [ ] AC-004-1: テーブル形式テスト合格
- [ ] AC-004-2: 箇条書き形式テスト合格
- [ ] AC-004-3: コードブロックスキップテスト合格
- [ ] AC-004-4: 検出結果の正確性テスト合格

---

#### TSK-VAL-002: 設計トレーサビリティ検証

| 属性 | 値 |
|------|-----|
| **ID** | TSK-VAL-002 |
| **設計ID** | DES-VAL-002 |
| **要件ID** | REQ-VAL-002 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-VAL-002-1 | `TraceabilityValidator` クラス実装 | 1.5h | AI Agent |
| TSK-VAL-002-2 | `DesignValidateCommand` 実装 | 1h | AI Agent |
| TSK-VAL-002-3 | CLI `design validate` コマンド追加 | 0.5h | AI Agent |
| TSK-VAL-002-4 | ユニットテスト追加 | 0.5h | AI Agent |
| TSK-VAL-002-5 | 実プロジェクトでの動作確認 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/validators/traceability-validator.ts # 新規作成
packages/core/src/cli/commands/design.ts               # 修正
packages/core/src/cli/commands/design.test.ts          # テスト追加
```

**テスト観点**:

- [ ] 孤立要件（orphan requirements）検出
- [ ] 過剰設計（orphan designs）検出
- [ ] カバレッジ計算の正確性

**受入基準チェック**:

- [ ] AC-005-1: コマンド実行可能
- [ ] AC-005-2: 孤立要件リスト表示
- [ ] AC-005-3: 過剰設計リスト表示
- [ ] AC-005-4: カバレッジ%表示

---

### 4.3 学習機能タスク

---

#### TSK-LRN-001: パターン推薦ガイダンス

| 属性 | 値 |
|------|-----|
| **ID** | TSK-LRN-001 |
| **設計ID** | DES-LRN-001 |
| **要件ID** | REQ-LRN-001 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-LRN-001-1 | `PatternRecommender` クラス実装 | 1.5h | AI Agent |
| TSK-LRN-001-2 | ファイルタイプ分析ロジック | 0.5h | AI Agent |
| TSK-LRN-001-3 | 信頼度スコアによるランキング | 0.5h | AI Agent |
| TSK-LRN-001-4 | スニペット生成ロジック | 0.5h | AI Agent |
| TSK-LRN-001-5 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/learning/pattern-recommender.ts      # 新規作成
packages/core/src/learning/pattern-recommender.test.ts # 新規作成
```

**テスト観点**:

- [ ] エンティティファイル作成時に推薦表示
- [ ] 信頼度スコアによるソートの正確性
- [ ] コードスニペットの生成品質
- [ ] 推薦理由の明確性

**受入基準チェック**:

- [ ] AC-006-1: 新規エンティティ作成時に推薦表示
- [ ] AC-006-2: 信頼度スコア含む
- [ ] AC-006-3: コードスニペット例提供

---

#### TSK-LRN-002: ドメイン固有パターン学習

| 属性 | 値 |
|------|-----|
| **ID** | TSK-LRN-002 |
| **設計ID** | DES-LRN-002 |
| **要件ID** | REQ-LRN-002 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | TSK-LRN-001 |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-LRN-002-1 | `DomainPatternClassifier` クラス実装 | 1h | AI Agent |
| TSK-LRN-002-2 | `DomainRegistry` クラス実装 | 1h | AI Agent |
| TSK-LRN-002-3 | ドメインタグ付与ロジック | 0.5h | AI Agent |
| TSK-LRN-002-4 | ドメインベース推薦ロジック | 0.5h | AI Agent |
| TSK-LRN-002-5 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/learning/domain-pattern-classifier.ts # 新規作成
packages/core/src/learning/domain-registry.ts           # 新規作成
```

**テスト観点**:

- [ ] パターン3回使用時のドメイン分類
- [ ] ドメインタグの正確な付与
- [ ] 類似ドメイン判定の信頼度
- [ ] ドメインベース推薦の適切性

**受入基準チェック**:

- [ ] AC-007-1: パターンにドメインタグ付与
- [ ] AC-007-2: ドメインベース推薦機能
- [ ] AC-007-3: 類似ドメイン判定80%以上

---

### 4.4 パターンライブラリタスク

---

#### TSK-PAT-001: 同時実行パターン追加

| 属性 | 値 |
|------|-----|
| **ID** | TSK-PAT-001 |
| **設計ID** | DES-PAT-001 |
| **要件ID** | REQ-PAT-001 |
| **優先度** | P0 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-PAT-001-1 | PAT-CONC-001: Optimistic Locking 定義 | 0.5h | AI Agent |
| TSK-PAT-001-2 | PAT-CONC-002: Pessimistic Locking 定義 | 0.5h | AI Agent |
| TSK-PAT-001-3 | PAT-CONC-003: Hold Pattern 定義 | 0.5h | AI Agent |
| TSK-PAT-001-4 | PAT-CONC-004: Idempotency Key 定義 | 0.5h | AI Agent |
| TSK-PAT-001-5 | パターンカタログへの登録 | 0.5h | AI Agent |
| TSK-PAT-001-6 | ガイダンスドキュメント作成 | 0.5h | AI Agent |
| TSK-PAT-001-7 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/pattern-mcp/src/patterns/concurrency/index.ts           # 新規作成
packages/pattern-mcp/src/patterns/concurrency/optimistic-lock.ts # 新規作成
packages/pattern-mcp/src/patterns/concurrency/pessimistic-lock.ts# 新規作成
packages/pattern-mcp/src/patterns/concurrency/hold-pattern.ts    # 新規作成
packages/pattern-mcp/src/patterns/concurrency/idempotency-key.ts # 新規作成
docs/patterns/concurrency.md                                      # 新規作成
```

**テスト観点**:

- [ ] `learn patterns --category concurrency` で4パターン表示
- [ ] 各パターンのテンプレートコード取得
- [ ] ガイダンスドキュメント存在確認

**受入基準チェック**:

- [ ] AC-008-1: 4パターン表示
- [ ] AC-008-2: テンプレートコード取得可能
- [ ] AC-008-3: ガイダンスドキュメント存在

---

#### TSK-PAT-002: 時間制約パターン追加

| 属性 | 値 |
|------|-----|
| **ID** | TSK-PAT-002 |
| **設計ID** | DES-PAT-002 |
| **要件ID** | REQ-PAT-002 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-PAT-002-1 | PAT-TIME-001: Expiry Check 定義 | 0.5h | AI Agent |
| TSK-PAT-002-2 | PAT-TIME-002: Scheduled Action 定義 | 0.5h | AI Agent |
| TSK-PAT-002-3 | PAT-TIME-003: Interval Management 定義 | 0.5h | AI Agent |
| TSK-PAT-002-4 | PAT-TIME-004: Streak Calculation 定義 | 0.5h | AI Agent |
| TSK-PAT-002-5 | パターンカタログへの登録 | 0.5h | AI Agent |
| TSK-PAT-002-6 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/pattern-mcp/src/patterns/time/index.ts        # 新規作成
packages/pattern-mcp/src/patterns/time/expiry-check.ts # 新規作成
packages/pattern-mcp/src/patterns/time/scheduled.ts    # 新規作成
packages/pattern-mcp/src/patterns/time/interval.ts     # 新規作成
packages/pattern-mcp/src/patterns/time/streak.ts       # 新規作成
```

---

### 4.5 コード生成タスク

---

#### TSK-GEN-001: Value Object自動生成

| 属性 | 値 |
|------|-----|
| **ID** | TSK-GEN-001 |
| **設計ID** | DES-GEN-001 |
| **要件ID** | REQ-GEN-001 |
| **優先度** | P1 |
| **サイズ** | L（4-8時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-GEN-001-1 | `ValueObjectGenerator` クラス実装 | 1.5h | AI Agent |
| TSK-GEN-001-2 | `VOTemplateRegistry` クラス実装 | 1h | AI Agent |
| TSK-GEN-001-3 | id タイプテンプレート | 0.5h | AI Agent |
| TSK-GEN-001-4 | money タイプテンプレート | 0.5h | AI Agent |
| TSK-GEN-001-5 | その他タイプテンプレート（temperature, weight, duration, percentage） | 1h | AI Agent |
| TSK-GEN-001-6 | CLI `codegen vo` コマンド追加 | 0.5h | AI Agent |
| TSK-GEN-001-7 | ユニットテスト追加 | 1h | AI Agent |

**変更ファイル**:

```
packages/core/src/codegen/vo-generator.ts              # 新規作成
packages/core/src/codegen/vo-template-registry.ts      # 新規作成
packages/core/src/codegen/templates/vo/               # 新規ディレクトリ
packages/core/src/cli/commands/codegen.ts             # 修正
```

---

#### TSK-GEN-002: Status Transition Map生成

| 属性 | 値 |
|------|-----|
| **ID** | TSK-GEN-002 |
| **設計ID** | DES-GEN-002 |
| **要件ID** | REQ-GEN-002 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-GEN-002-1 | `StatusTransitionGenerator` クラス実装 | 1h | AI Agent |
| TSK-GEN-002-2 | `validStatusTransitions` マップ生成 | 0.5h | AI Agent |
| TSK-GEN-002-3 | `transitionStatus()` 関数生成 | 0.5h | AI Agent |
| TSK-GEN-002-4 | Mermaid図生成 | 0.5h | AI Agent |
| TSK-GEN-002-5 | CLI `codegen status` コマンド追加 | 0.5h | AI Agent |
| TSK-GEN-002-6 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/codegen/status-generator.ts          # 新規作成
packages/core/src/cli/commands/codegen.ts             # 修正
```

---

### 4.6 テスト生成タスク

---

#### TSK-TST-001: Status Transitionテスト生成

| 属性 | 値 |
|------|-----|
| **ID** | TSK-TST-001 |
| **設計ID** | DES-TST-001 |
| **要件ID** | REQ-TST-001 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | TSK-GEN-002（状態遷移マップ生成を使用） |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-TST-001-1 | `StatusTransitionTestGenerator` クラス実装 | 1h | AI Agent |
| TSK-TST-001-2 | 有効遷移テスト生成 | 0.5h | AI Agent |
| TSK-TST-001-3 | 無効遷移テスト生成 | 0.5h | AI Agent |
| TSK-TST-001-4 | 終端状態テスト生成 | 0.5h | AI Agent |
| TSK-TST-001-5 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/codegen/test-generator.ts            # 修正
packages/core/src/codegen/test-generator.test.ts       # テスト追加
```

---

#### TSK-TST-002: カウンターリセット自動挿入

| 属性 | 値 |
|------|-----|
| **ID** | TSK-TST-002 |
| **設計ID** | DES-TST-002 |
| **要件ID** | REQ-TST-002 |
| **優先度** | P0 |
| **サイズ** | S（1-2時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-TST-002-1 | `TestFileDecorator` クラス実装 | 0.5h | AI Agent |
| TSK-TST-002-2 | カウンターリセット検出ロジック | 0.5h | AI Agent |
| TSK-TST-002-3 | beforeEach挿入ロジック | 0.5h | AI Agent |
| TSK-TST-002-4 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/codegen/test-file-decorator.ts       # 新規作成
packages/core/src/codegen/test-generator.ts            # 修正
```

**テスト観点**:

- [ ] beforeEachブロック生成
- [ ] resetCounter呼び出し挿入
- [ ] テスト間独立性

**受入基準チェック**:

- [ ] AC-013-1: beforeEach生成確認
- [ ] AC-013-2: resetCounter呼び出し確認
- [ ] AC-013-3: テスト間干渉なし確認

---

### 4.7 非機能要件タスク

---

#### TSK-NFR-001: アクショナブルエラーメッセージ

| 属性 | 値 |
|------|-----|
| **ID** | TSK-NFR-001 |
| **設計ID** | DES-NFR-001 |
| **要件ID** | REQ-NFR-001 |
| **優先度** | P1 |
| **サイズ** | M（2-4時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-NFR-001-1 | `ActionableError` クラス実装 | 1h | AI Agent |
| TSK-NFR-001-2 | `ErrorFormatter` クラス実装 | 1h | AI Agent |
| TSK-NFR-001-3 | 既存CLIコマンドへの統合 | 0.5h | AI Agent |
| TSK-NFR-001-4 | ユニットテスト追加 | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/error/actionable-error.ts            # 新規作成
packages/core/src/error/error-formatter.ts             # 新規作成
packages/core/src/cli/commands/*.ts                    # 各コマンド修正
```

---

#### TSK-NFR-002: コマンド応答性能

| 属性 | 値 |
|------|-----|
| **ID** | TSK-NFR-002 |
| **設計ID** | DES-NFR-002 |
| **要件ID** | REQ-NFR-002 |
| **優先度** | P2 |
| **サイズ** | L（4-8時間） |
| **依存タスク** | なし |

**サブタスク**:

| サブID | 内容 | 工数 | 担当 |
|--------|------|------|------|
| TSK-NFR-002-1 | ベースライン性能計測 | 1h | AI Agent |
| TSK-NFR-002-2 | Lazy Loading実装 | 1.5h | AI Agent |
| TSK-NFR-002-3 | 並列処理実装 | 1.5h | AI Agent |
| TSK-NFR-002-4 | キャッシュ実装 | 1h | AI Agent |
| TSK-NFR-002-5 | 性能テスト追加 | 1h | AI Agent |
| TSK-NFR-002-6 | 改善後の計測・レポート | 0.5h | AI Agent |

**変更ファイル**:

```
packages/core/src/cli/performance.ts                   # 新規作成
packages/core/src/cli/lazy-loader.ts                   # 新規作成
packages/core/src/learning/pattern-cache.ts            # 新規作成
```

---

## 5. 依存関係図

```
Phase 1 (P0):
  TSK-CLI-001 ─────┐
  TSK-VAL-001 ─────┤
  TSK-PAT-001 ─────┤──▶ Phase 1 Complete
  TSK-TST-002 ─────┘

Phase 2 (P1):
  TSK-CLI-002 ─────────────────────────┐
  TSK-VAL-002 ─────────────────────────┤
  TSK-PAT-002 ─────────────────────────┤
  TSK-LRN-001 ──▶ TSK-LRN-002 ─────────┤
  TSK-GEN-001 ─────────────────────────┤──▶ Phase 2 Complete
  TSK-GEN-002 ──▶ TSK-TST-001 ─────────┤
  TSK-PAT-001 ──▶ TSK-CLI-003 ─────────┤
  TSK-NFR-001 ─────────────────────────┘

Phase 3 (P2):
  TSK-NFR-002 ──▶ Phase 3 Complete
```

---

## 6. リスク・課題

| # | リスク | 影響度 | 対策 |
|---|--------|--------|------|
| 1 | TSK-CLI-003のパターン適用が複雑化 | 中 | TSK-PAT-001を先に完了させ、パターン定義を確定 |
| 2 | TSK-VAL-001のMarkdownパース精度 | 中 | 実際の要件ドキュメントでの検証を重視 |
| 3 | TSK-NFR-002の性能目標未達 | 低 | P2のため、未達でもリリースブロッカーにならない |

---

## 7. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-13 | 初版作成 - DES-MUSUBIX-v3.1.0に基づくタスク分解 | AI Agent |
| 1.1 | 2026-01-13 | レビュー修正: TSK-CLI/VAL/LRNサブタスクに担当者設定 | AI Agent |
| 1.2 | 2026-01-13 | レビュー修正: 全サブタスクに担当者設定完了 | AI Agent |

---

## 8. 承認

| 役割 | 氏名 | 署名 | 日付 |
|------|------|------|------|
| 作成者 | AI Agent | - | 2026-01-13 |
| レビュアー | | | |
| 承認者 | | | |

---

**文書終端**
