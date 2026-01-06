# MUSUBIX v1.7.5 要件定義書

**文書ID**: REQ-MUSUBIX-175  
**バージョン**: 1.1.0  
**作成日**: 2026-01-06  
**ステータス**: Reviewed

---

## 1. 概要

### 1.1 目的

MUSUBIX v1.7.5は**Formal Verification（形式検証）** の導入により、LLM生成コードの数学的正しさを保証する機能を追加する。これにより「証明付きコード」の実現を目指す。

### 1.2 スコープ

| 項目 | 内容 |
|------|------|
| **コードネーム** | Formal Verification Edition |
| **主要機能** | Z3 SMTソルバー統合、EARS→形式仕様変換、双方向トレーサビリティDB |
| **新規パッケージ** | `@nahisaho/musubix-formal-verify` |
| **対象ユーザー** | AIコーディングエージェント、品質保証チーム |

### 1.2.1 リリース計画

| バージョン | スコープ | 要件数 |
|--------------|--------|--------|
| **v1.7.5** | P0要件（コア機能） | 9 |
| v1.8.0 | P1要件（拡張機能） | 7 |
| v1.8.5 | P2要件（Nice-to-have） | 3 |

> ℹ️ **注**: 本文書はv1.7.5のP0要件に焦点。P1/P2は参考情報として記載。

### 1.3 背景

v1.7.0までの実装:
- ✅ Pattern Library Learning MCP（pattern-mcp）
- ✅ Ontology Reasoning MCP（ontology-mcp）
- ✅ Confidence-Based Routing（core/symbolic）
- ✅ Semantic Code Filter（HallucinationDetector, SecurityScanner）

v1.7.5で追加:
- ❌ Formal Verification MCP（Z3統合）
- ❌ EARS→形式仕様変換エンジン
- ❌ 双方向トレーサビリティDB

### 1.4 既存機能との関係

| 既存クラス | パッケージ | v1.7.5での扱い |
|-----------|------------|-----------------|
| `EarsToFormalSpecConverter` | core/symbolic | 拡張（SMT-LIB完全対応） |
| `VerificationConditionGenerator` | core/symbolic | 拡張（WP計算追加） |
| `Z3Adapter` | core/symbolic | 置換（z3-wasm対応） |
| `HallucinationDetector` | core/symbolic | 統合（検証結果連携） |

### 1.5 技術調査結果

#### Z3バインディング評価

| 候補 | 評価 | 推奨 | 理由 |
|------|------|------|------|
| z3-solver (npm) | ❌ | 非推奨 | メンテナンス不活発、Node 20未対応 |
| **z3-wasm** | ✅ | **推奨** | ブラウザ/Node両対応、純JS |
| 外部Z3プロセス | △ | フォールバック | 環境依存、インストール必要 |

**決定**: z3-wasmを第一候補とし、外部プロセス起動をフォールバックとする。

---

## 2. 機能要件

### 2.1 Formal Verification MCP Server（REQ-FV-*）

#### REQ-FV-001: Z3 SMTソルバー統合

| 項目 | 内容 |
|------|------|
| **ID** | REQ-FV-001 |
| **優先度** | P0（必須） |
| **カテゴリ** | 形式検証 |

**EARS形式要件**:

> **WHEN** LLM generates code with preconditions and postconditions,  
> **THE** FormalVerificationService **SHALL** verify the code against the conditions using Z3 SMT solver within 10 seconds.

**受け入れ基準**:
- [ ] z3-solver npmパッケージを統合
- [ ] 検証結果（valid/invalid/unknown）を返却
- [ ] 反例（counterexample）を生成
- [ ] タイムアウト10秒で unknown を返却

---

#### REQ-FV-002: 事前条件検証

| 項目 | 内容 |
|------|------|
| **ID** | REQ-FV-002 |
| **優先度** | P0（必須） |
| **カテゴリ** | 形式検証 |

**EARS形式要件**:

> **WHEN** user invokes `verify_precondition` tool,  
> **THE** FormalVerificationService **SHALL** verify that the function's preconditions are satisfiable and return validation result with proof or counterexample.

**受け入れ基準**:
- [ ] EARS形式の事前条件を受け入れ
- [ ] SMT-LIB2形式に変換
- [ ] Z3で充足可能性を判定
- [ ] 充足不能の場合、反例を生成

---

#### REQ-FV-003: 事後条件検証

| 項目 | 内容 |
|------|------|
| **ID** | REQ-FV-003 |
| **優先度** | P0（必須） |
| **カテゴリ** | 形式検証 |

**EARS形式要件**:

> **WHEN** user invokes `verify_postcondition` tool,  
> **THE** FormalVerificationService **SHALL** verify that the function establishes its postconditions given the preconditions are satisfied.

**受け入れ基準**:
- [ ] Hoare論理に基づく検証
- [ ] {P} code {Q} の妥当性判定
- [ ] 不成立の場合、違反パスを特定

---

#### REQ-FV-004: 不変条件検証

| 項目 | 内容 |
|------|------|
| **ID** | REQ-FV-004 |
| **優先度** | P1（重要） |
| **カテゴリ** | 形式検証 |

**EARS形式要件**:

> **WHEN** user invokes `verify_invariant` tool with loop or class code,  
> **THE** FormalVerificationService **SHALL** verify that the invariant is maintained throughout execution.

**受け入れ基準**:
- [ ] ループ不変条件の検証
- [ ] クラス不変条件の検証
- [ ] 違反箇所の特定

---

#### REQ-FV-005: 検証条件自動生成

| 項目 | 内容 |
|------|------|
| **ID** | REQ-FV-005 |
| **優先度** | P1（重要） |
| **カテゴリ** | 形式検証 |

**EARS形式要件**:

> **WHEN** user invokes `generate_verification_conditions` tool with code and EARS specification,  
> **THE** FormalVerificationService **SHALL** automatically generate verification conditions (VCs) from the code.

**受け入れ基準**:
- [ ] 最弱事前条件（WP）計算
- [ ] 検証条件のSMT-LIB2出力
- [ ] 人間可読な説明生成

---

### 2.2 EARS→形式仕様変換（REQ-E2F-*）

#### REQ-E2F-001: EARS→SMT-LIB変換

| 項目 | 内容 |
|------|------|
| **ID** | REQ-E2F-001 |
| **優先度** | P0（必須） |
| **カテゴリ** | 仕様変換 |

**EARS形式要件**:

> **THE** EarsToFormalConverter **SHALL** convert EARS format requirements to SMT-LIB2 format with 100% syntactic coverage of the 5 EARS patterns.

**受け入れ基準**:
- [ ] Ubiquitous → 述語論理式
- [ ] Event-driven → 時相論理式（trigger → response）
- [ ] State-driven → 状態述語（state → invariant）
- [ ] Unwanted → 否定述語（NOT behavior）
- [ ] Optional → 条件式（condition → action）

---

#### REQ-E2F-002: 時相論理（LTL）サポート

| 項目 | 内容 |
|------|------|
| **ID** | REQ-E2F-002 |
| **優先度** | P1（重要） |
| **カテゴリ** | 仕様変換 |

**EARS形式要件**:

> **WHEN** EARS requirement contains temporal constraints (e.g., "within 3 seconds"),  
> **THE** EarsToFormalConverter **SHALL** generate LTL (Linear Temporal Logic) formulas.

**受け入れ基準**:
- [ ] G (globally), F (finally), X (next), U (until) 演算子
- [ ] 有界時相論理（bounded LTL）サポート
- [ ] LTL→SMT-LIB変換（有界モデル検査用）

---

#### REQ-E2F-003: 型制約抽出

| 項目 | 内容 |
|------|------|
| **ID** | REQ-E2F-003 |
| **優先度** | P1（重要） |
| **カテゴリ** | 仕様変換 |

**EARS形式要件**:

> **THE** EarsToFormalConverter **SHALL** extract type constraints from EARS requirements and generate SMT-LIB type assertions.

**受け入れ基準**:
- [ ] 数値範囲制約（e.g., "between 1 and 100"）
- [ ] 文字列制約（e.g., "non-empty", "email format"）
- [ ] 列挙型制約（e.g., "one of: active, inactive, pending"）

---

### 2.3 双方向トレーサビリティDB（REQ-TDB-*）

#### REQ-TDB-001: グラフデータベース統合

| 項目 | 内容 |
|------|------|
| **ID** | REQ-TDB-001 |
| **優先度** | P0（必須） |
| **カテゴリ** | トレーサビリティ |

**EARS形式要件**:

> **THE** TraceabilityDBService **SHALL** store traceability links in a graph database format supporting bidirectional traversal.

**受け入れ基準**:
- [ ] SQLiteベースのグラフストレージ（yata-localと統合）
- [ ] ノード: Requirement, Design, Code, Test
- [ ] エッジ: DESIGNED_BY, IMPLEMENTED_BY, TESTED_BY, VERIFIES
- [ ] 双方向クエリ（親→子、子→親）

---

#### REQ-TDB-002: 影響分析クエリ

| 項目 | 内容 |
|------|------|
| **ID** | REQ-TDB-002 |
| **優先度** | P0（必須） |
| **カテゴリ** | トレーサビリティ |

**EARS形式要件**:

> **WHEN** user queries impact analysis for a requirement change,  
> **THE** TraceabilityDBService **SHALL** return all affected designs, code files, and tests within 1 second.

**受け入れ基準**:
- [ ] 推移閉包クエリ（transitive closure）
- [ ] 変更影響の視覚化（Mermaid図生成）
- [ ] 影響度スコア算出

---

#### REQ-TDB-003: カバレッジ分析

| 項目 | 内容 |
|------|------|
| **ID** | REQ-TDB-003 |
| **優先度** | P1（重要） |
| **カテゴリ** | トレーサビリティ |

**EARS形式要件**:

> **THE** TraceabilityDBService **SHALL** calculate and report traceability coverage metrics:  
> - Requirements with no design (orphan requirements)  
> - Designs with no code (unimplemented designs)  
> - Code with no tests (untested code)  
> - Tests with no requirement linkage (orphan tests)

**受け入れ基準**:
- [ ] 未設計要件の検出
- [ ] 未実装設計の検出
- [ ] 未テストコードの検出
- [ ] 孤立テストの検出
- [ ] カバレッジ率レポート生成

---

#### REQ-TDB-004: 自動リンク検出

| 項目 | 内容 |
|------|------|
| **ID** | REQ-TDB-004 |
| **優先度** | P2（任意） |
| **カテゴリ** | トレーサビリティ |

**EARS形式要件**:

> **WHEN** new code or test file is added to the project,  
> **THE** TraceabilityDBService **SHALL** automatically suggest potential traceability links based on naming conventions and content analysis.

**受け入れ基準**:
- [ ] REQ-*, DES-*, TSK-* 参照の自動検出
- [ ] @requirement, @design タグの解析
- [ ] 類似度ベースのリンク提案（信頼度付き）

---

### 2.4 MCPツール拡張（REQ-MCP-*）

#### REQ-MCP-001: 形式検証ツール

| 項目 | 内容 |
|------|------|
| **ID** | REQ-MCP-001 |
| **優先度** | P0（必須） |
| **カテゴリ** | MCP |

**EARS形式要件**:

> **THE** MCP Server **SHALL** provide the following formal verification tools:  
> - `verify_precondition`: Verify function preconditions  
> - `verify_postcondition`: Verify function postconditions  
> - `verify_invariant`: Verify loop/class invariants  
> - `generate_vcs`: Generate verification conditions

**受け入れ基準**:
- [ ] 4つの新規MCPツール
- [ ] JSON Schema入出力定義
- [ ] エラーハンドリング（タイムアウト、Z3エラー）

---

#### REQ-MCP-002: EARS変換ツール

| 項目 | 内容 |
|------|------|
| **ID** | REQ-MCP-002 |
| **優先度** | P0（必須） |
| **カテゴリ** | MCP |

**EARS形式要件**:

> **THE** MCP Server **SHALL** provide the following EARS conversion tools:  
> - `ears_to_smt`: Convert EARS to SMT-LIB2  
> - `ears_to_ltl`: Convert EARS to LTL formula  
> - `extract_constraints`: Extract type constraints from EARS

**受け入れ基準**:
- [ ] 3つの新規MCPツール
- [ ] 変換結果の説明生成
- [ ] 変換不能な場合のエラーメッセージ

---

#### REQ-MCP-003: トレーサビリティDBツール

| 項目 | 内容 |
|------|------|
| **ID** | REQ-MCP-003 |
| **優先度** | P0（必須） |
| **カテゴリ** | MCP |

**EARS形式要件**:

> **THE** MCP Server **SHALL** provide the following traceability database tools:  
> - `trace_add_link`: Add traceability link  
> - `trace_query`: Query traceability graph  
> - `trace_impact`: Analyze change impact  
> - `trace_coverage`: Report traceability coverage

**受け入れ基準**:
- [ ] 4つの新規MCPツール
- [ ] グラフ可視化出力（Mermaid）
- [ ] レポート出力（Markdown/JSON）

---

## 3. 非機能要件

### 3.1 パフォーマンス（REQ-NFR-PERF-*）

#### REQ-NFR-PERF-001: 検証時間

> **THE** formal verification **SHALL** complete within 10 seconds for functions with up to 100 lines of code.

#### REQ-NFR-PERF-002: トレーサビリティクエリ時間

> **THE** traceability query **SHALL** return results within 1 second for graphs with up to 10,000 nodes.

### 3.2 信頼性（REQ-NFR-REL-*）

#### REQ-NFR-REL-001: Z3障害時のグレースフル デグラデーション

> **WHEN** Z3 solver fails or times out,  
> **THE** system **SHALL** return `unknown` status with partial analysis results, **NOT** crash.

### 3.3 拡張性（REQ-NFR-EXT-*）

#### REQ-NFR-EXT-001: カスタム検証ルール

> **THE** formal verification system **SHALL** support user-defined verification rules in YAML format.

---

## 4. 制約条件

### 4.1 技術的制約

| 制約 | 詳細 |
|------|------|
| **Z3バインディング** | z3-wasm（推奨）または外部Z3プロセス（フォールバック） |
| **グラフDB** | SQLiteベース（外部DBサーバー不要） |
| **Node.jsバージョン** | >= 20.0.0 |

### 4.2 憲法準拠

| 条項 | 準拠方法 |
|------|----------|
| **I. Library-First** | `formal-verify` パッケージとして独立実装 |
| **II. CLI Interface** | `npx musubix verify` コマンド提供 |
| **III. Test-First** | 全機能にユニットテスト先行 |
| **IV. EARS Format** | 本要件書自体がEARS形式 |
| **V. Traceability** | 本パッケージ自身でトレーサビリティ検証 |

---

## 5. 要件一覧

### 5.1 v1.7.5 スコープ（P0要件: 9件）

| ID | タイトル | 優先度 | カテゴリ |
|----|----------|--------|----------|
| REQ-FV-001 | Z3 SMTソルバー統合 | **P0** | 形式検証 |
| REQ-FV-002 | 事前条件検証 | **P0** | 形式検証 |
| REQ-FV-003 | 事後条件検証 | **P0** | 形式検証 |
| REQ-E2F-001 | EARS→SMT-LIB変換 | **P0** | 仕様変換 |
| REQ-TDB-001 | グラフデータベース統合 | **P0** | トレーサビリティ |
| REQ-TDB-002 | 影響分析クエリ | **P0** | トレーサビリティ |
| REQ-MCP-001 | 形式検証ツール | **P0** | MCP |
| REQ-MCP-002 | EARS変換ツール | **P0** | MCP |
| REQ-MCP-003 | トレーサビリティDBツール | **P0** | MCP |

### 5.2 v1.8.0 スコープ（P1要件: 7件）

| ID | タイトル | 優先度 | カテゴリ |
|----|----------|--------|----------|
| REQ-FV-004 | 不変条件検証 | P1 | 形式検証 |
| REQ-FV-005 | 検証条件自動生成 | P1 | 形式検証 |
| REQ-E2F-002 | 時相論理（LTL）サポート | P1 | 仕様変換 |
| REQ-E2F-003 | 型制約抽出 | P1 | 仕様変換 |
| REQ-TDB-003 | カバレッジ分析 | P1 | トレーサビリティ |
| REQ-NFR-PERF-001 | 検証時間 | P1 | 非機能 |
| REQ-NFR-PERF-002 | トレーサビリティクエリ時間 | P1 | 非機能 |

### 5.3 v1.8.5 スコープ（P2要件: 3件）

| ID | タイトル | 優先度 | カテゴリ |
|----|----------|--------|----------|
| REQ-TDB-004 | 自動リンク検出 | P2 | トレーサビリティ |
| REQ-NFR-REL-001 | グレースフル デグラデーション | P2 | 非機能 |
| REQ-NFR-EXT-001 | カスタム検証ルール | P2 | 非機能 |

### 5.4 要件サマリ

| 優先度 | 要件数 | リリース |
|--------|--------|----------|
| **P0** | 9 | v1.7.5 |
| P1 | 7 | v1.8.0 |
| P2 | 3 | v1.8.5 |
| **総計** | **19** | - |

---

## 6. 依存関係

### 6.1 外部依存

| パッケージ | 用途 | バージョン |
|-----------|------|-----------|
| z3-solver | SMTソルバー | ^4.x |
| better-sqlite3 | グラフDB基盤 | ^9.x |

### 6.2 内部依存

| パッケージ | 依存理由 |
|-----------|----------|
| @nahisaho/musubix-core | EARS検証、コード解析 |
| @nahisaho/yata-local | グラフストレージ基盤 |
| @nahisaho/musubix-mcp-server | MCPツール統合 |

---

## 7. リスク

| リスク | 影響 | 緩和策 |
|--------|------|--------|
| Z3統合の複雑さ | 高 | z3-wasmフォールバック、段階的導入 |
| 検証時間の超過 | 中 | タイムアウト設定、並列検証 |
| LTL変換の不完全性 | 中 | サポート範囲の明示、手動指定オプション |

---

## 8. テスト戦略

### 8.1 テストカテゴリ

| カテゴリ | 目標テスト数 | カバレッジ目標 | 対象要件 |
|----------|-------------|---------------|----------|
| Z3統合テスト | 30+ | 85% | REQ-FV-001〜003 |
| EARS変換テスト | 25+ | 90% | REQ-E2F-001 |
| トレーサビリティDBテスト | 20+ | 85% | REQ-TDB-001、002 |
| MCPツールテスト | 15+ | 80% | REQ-MCP-001〜003 |
| **合計** | **90+** | **85%** | - |

### 8.2 テスト方針

1. **Test-First**: 全P0要件に対してテスト先行開発
2. **プロパティベースドテスト**: Z3検証結果の網羅的検証
3. **統合テスト**: MCPツール経由のエンドツーエンド検証
4. **パフォーマンステスト**: 10秒タイムアウトの検証

---

## 9. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| プロダクトオーナー | | | |
| テックリード | | | |
| QAリード | | | |

---

**次のステップ**: 設計書（DES-MUSUBIX-175）の作成

---

**Document ID**: REQ-MUSUBIX-175  
**Traceability**: → DES-MUSUBIX-175, TSK-MUSUBIX-175
