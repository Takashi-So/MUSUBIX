# MUSUBIX Phase 3 タスク定義書（学習・推論拡張）

**文書ID**: TSK-PHASE3-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-05  
**ステータス**: Draft  
**設計書**: DES-PATTERN-001 / DES-ONTO-001 / DES-WAKE-001 / DES-SDD-ONTO-001

---

## 1. タスク概要

### 1.0 タスクID運用

- 本書（TSK-PHASE3-001）内で `TSK-PATTERN-*` / `TSK-ONTO-*` / `TSK-WAKE-*` / `TSK-SDD-ONTO-*` を定義する（個別の `TSK-XXX-YYY.md` は作成しない）
- Phase 3設計書（DES-PATTERN-001 / DES-ONTO-001 / DES-WAKE-001 / DES-SDD-ONTO-001）のトレーサビリティ表に出現するタスクIDは、すべて本書で定義済み

### 1.1 対象スコープ

- Pattern Library Learning MCP（REQ-PATTERN-001）
- Ontology Reasoning MCP（REQ-ONTO-001）
- Wake-Sleep学習エンジン（REQ-WAKE-001）
- SDDオントロジー構築（REQ-SDD-ONTO-001）

### 1.2 前提・制約

- Node.js >= 20 / TypeScript / npm workspaces
- ローカルファースト（外部送信なし）
- テストはVitestを使用
- 9憲法条項（とくに第I/II/III/V条）を満たすこと

### 1.3 スプリント案（最小）

| スプリント | 期間 | 目的 | 主な成果物 |
|-----------|------|------|------------|
| S1 | 3日 | 基盤（雛形・永続・最小P0の土台） | 各領域の骨格 + 永続化（ローカル） + ビルド/テストが通る |
| S2 | 4日 | P0（コア機能を動かす） | Pattern抽出/抽象化/類似度、Ontology推論/クエリ、Wake/Sleep基礎、SDDコア/主要TTL |
| S3 | 4日 | P0完了＋P1/品質（制約・検証・補助機能） | Wakeサイクル/制限、Ontology整合・エラー、SDDバリデーション/推論、Patternクラスター/圧縮 |
| S4 | 2日 | 統合（CLI/MCP/E2E/追跡） | MCPツール疎通、CLI導線、Traceability検証 |

### 1.3.1 タスクサマリー（見積の俯瞰）

| 区分 | P0合計 | P1合計 | 合計 |
|------|--------|--------|------|
| Pattern | 44h | 12h | 56h |
| Ontology | 46h | 22h | 68h |
| Wake | 42h | 20h | 62h |
| SDD Ontology | 34h | 14h | 48h |
| **小計** | **166h** | **68h** | **234h** |
| 横断（推奨） | - | - | 20h |
| **合計** | - | - | **254h** |

### 1.3.2 スプリント別合計見積（h）

| スプリント | 合計 | 備考 |
|-----------|------|------|
| S1 | 62h | 基盤/永続/外部通信なしの土台 |
| S2 | 80h | P0中心（推論・抽象化・基礎TTL） |
| S3 | 96h | P1＋品質ゲート（制限/検証/圧縮） |
| S4 | 16h | CLI/MCP/Traceability |

### 1.4 スプリント別タスク割当（依存関係順・P0優先）

| スプリント | タスク（完了順の目安） |
|-----------|------------------------|
| S1 | TSK-PHASE3-INT-001, TSK-PATTERN-001, TSK-PATTERN-005, TSK-PATTERN-007, TSK-ONTO-001, TSK-ONTO-008, TSK-WAKE-001, TSK-SDD-ONTO-001 |
| S2 | TSK-PATTERN-002, TSK-PATTERN-003, TSK-ONTO-004, TSK-ONTO-002, TSK-ONTO-003, TSK-WAKE-002, TSK-SDD-ONTO-002, TSK-SDD-ONTO-003, TSK-SDD-ONTO-004 |
| S3 | TSK-WAKE-003, TSK-WAKE-007, TSK-WAKE-004, TSK-WAKE-005, TSK-WAKE-006, TSK-ONTO-006, TSK-ONTO-005, TSK-ONTO-007, TSK-PATTERN-004, TSK-PATTERN-006, TSK-SDD-ONTO-007, TSK-SDD-ONTO-005, TSK-SDD-ONTO-006 |
| S4 | TSK-PHASE3-INT-002, TSK-PHASE3-INT-003, TSK-PHASE3-INT-004 |

### 1.5 スプリント完了条件（最小）

#### S1 完了条件

- `npm run build` と `npm run test` が通る（少なくとも追加パッケージの雛形テストが成功）（TSK-PHASE3-INT-001）（受入:6）
- Pattern: 最小入力で抽出が実行でき、保存・読込できる（TSK-PATTERN-001, TSK-PATTERN-005）（受入:2.2）
- Ontology: ストア作成/保存/読込ができ、外部通信なし方針がテストで担保される（TSK-ONTO-001, TSK-ONTO-008）（受入:3.2）
- Wake: サンプル入力で起動し、統計（成功数など）の最小結果を返す（TSK-WAKE-001）（受入:4.2）
- SDD Ontology: コアTTLがパース可能で、最低1つのクラスと関係が存在する（TSK-SDD-ONTO-001）（受入:5.2）

#### S2 完了条件

- Pattern: 抽象化と類似度が動作し、同一入力に対して再現性のある結果が得られる（TSK-PATTERN-002, TSK-PATTERN-003）（受入:2.2）
- Ontology: SELECT/ASKが動作し、推論と整合チェックが動く（TSK-ONTO-004, TSK-ONTO-002, TSK-ONTO-003）（受入:3.2）
- Wake: Sleepが動作し、Sleepで新規パターン（または抽象化）が追加される（TSK-WAKE-002）（受入:4.2）
- SDD Ontology: EARS/トレーサビリティ/憲法条項が参照可能になる（TSK-SDD-ONTO-002, TSK-SDD-ONTO-003, TSK-SDD-ONTO-004）（受入:5.2）

#### S3 完了条件

- Wake: 収束判定と安全停止（制限超過時）が動作し状態が保持される（TSK-WAKE-003, TSK-WAKE-007）（受入:4.2）
- Ontology: 無効クエリで行/列を返し、マッピング/インポートが動く（TSK-ONTO-007, TSK-ONTO-005, TSK-ONTO-006）（受入:3.2）
- Pattern: クラスターと圧縮が動作し、結果が永続化される（TSK-PATTERN-004, TSK-PATTERN-006）（受入:2.2）
- SDD Ontology: バリデーションとギャップ/違反検出の最小ルールが動く（TSK-SDD-ONTO-007, TSK-SDD-ONTO-006）（受入:5.2）

#### S4 完了条件

- CLI: 各機能への入口がCLIから到達できる（TSK-PHASE3-INT-002）（受入:6）
- MCP: stdio経由のE2Eで最低1ツールが成功する（TSK-PHASE3-INT-003）（受入:6）
- Traceability: Phase 3のREQ↔DES↔TSKが機械的に検証できる（TSK-PHASE3-INT-004）（受入:6）

---

## 2. Pattern Library Learning MCP（REQ-PATTERN-001）

### 2.1 実装タスク

| タスクID | タスク名 | 対応要件 | 優先度 | 見積 | 依存 |
|---------|---------|---------|--------|------|------|
| TSK-PATTERN-001 | パターン抽出（AST生成＋繰り返し検出） | REQ-PATTERN-001-F001 | P0 | 12h | - |
| TSK-PATTERN-002 | パターン抽象化（Anti-unification） | REQ-PATTERN-001-F002 | P0 | 10h | TSK-PATTERN-001 |
| TSK-PATTERN-003 | 類似度計算（特徴抽出＋コサイン） | REQ-PATTERN-001-F003 | P0 | 8h | TSK-PATTERN-001 |
| TSK-PATTERN-004 | クラスタリング（HDBSCAN/DBSCAN） | REQ-PATTERN-001-F004 | P1 | 6h | TSK-PATTERN-003 |
| TSK-PATTERN-005 | ライブラリ管理（JSON永続化＋CRUD＋I/O） | REQ-PATTERN-001-F005 | P0 | 8h | TSK-PATTERN-001 |
| TSK-PATTERN-006 | ライブラリ圧縮（冗長検出＋マージ＋要約） | REQ-PATTERN-001-F006 | P1 | 6h | TSK-PATTERN-002, TSK-PATTERN-003, TSK-PATTERN-005 |
| TSK-PATTERN-007 | プライバシー保護（機密フィルター＋外部通信禁止） | REQ-PATTERN-001-F007 | P0 | 6h | TSK-PATTERN-005 |

### 2.2 受入チェック（抜粋）

- TSK-PATTERN-001: Tree-sitterでAST生成→繰り返し構造が抽出できる
- TSK-PATTERN-005: ライブラリの保存/読込/更新がローカルで完結
- TSK-PATTERN-007: 機密パターンが永続化されず、外部通信しない

---

## 3. Ontology Reasoning MCP（REQ-ONTO-001）

### 3.1 実装タスク

| タスクID | タスク名 | 対応要件 | 優先度 | 見積 | 依存 |
|---------|---------|---------|--------|------|------|
| TSK-ONTO-001 | ドメインオントロジー定義（CRUD＋永続化） | REQ-ONTO-001-F001 | P0 | 10h | - |
| TSK-ONTO-002 | 含意推論（OWL 2 RL ルール＋証明木） | REQ-ONTO-001-F002 | P0 | 12h | TSK-ONTO-001 |
| TSK-ONTO-003 | 一貫性検証（制約違反＋矛盾説明） | REQ-ONTO-001-F003 | P0 | 10h | TSK-ONTO-001, TSK-ONTO-002 |
| TSK-ONTO-004 | SPARQLクエリ（解析＋実行＋JSON返却） | REQ-ONTO-001-F004 | P0 | 10h | TSK-ONTO-001 |
| TSK-ONTO-005 | EARS要件マッピング（パース＋概念対応） | REQ-ONTO-001-F005 | P1 | 8h | TSK-ONTO-001 |
| TSK-ONTO-006 | オントロジーインポート（namespace衝突検出＋マージ） | REQ-ONTO-001-F006 | P1 | 8h | TSK-ONTO-001 |
| TSK-ONTO-007 | クエリエラーハンドリング（行/列＋提案） | REQ-ONTO-001-F007 | P1 | 6h | TSK-ONTO-004 |
| TSK-ONTO-008 | プライバシー保護（ローカル保存＋外部通信禁止） | REQ-ONTO-001-F008 | P0 | 4h | TSK-ONTO-001 |

### 3.2 受入チェック（抜粋）

- TSK-ONTO-002: 代表的な推論（推移・継承・逆関係）が成立し、証明木が出力できる
- TSK-ONTO-004: SELECT/ASK/CONSTRUCTが動作し、推論後ストアに対してクエリ可能
- TSK-ONTO-007: 無効クエリで行/列情報と修正提案が返る

---

## 4. Wake-Sleep学習エンジン（REQ-WAKE-001）

### 4.1 実装タスク

| タスクID | タスク名 | 対応要件 | 優先度 | 見積 | 依存 |
|---------|---------|---------|--------|------|------|
| TSK-WAKE-001 | Wake Phase（列挙探索＋解探索＋統計返却） | REQ-WAKE-001-F001 | P0 | 12h | - |
| TSK-WAKE-002 | Sleep Phase（共通サブ構造＋新規パターン追加＋圧縮） | REQ-WAKE-001-F002 | P0 | 12h | TSK-WAKE-001 |
| TSK-WAKE-003 | 学習サイクル管理（複数サイクル＋収束判定） | REQ-WAKE-001-F003 | P0 | 10h | TSK-WAKE-001, TSK-WAKE-002 |
| TSK-WAKE-004 | 探索戦略（MDL＋短いプログラム優先＋ビーム） | REQ-WAKE-001-F004 | P1 | 8h | TSK-WAKE-001 |
| TSK-WAKE-005 | 抽象化品質評価（汎用性スコア＋フィルター） | REQ-WAKE-001-F005 | P1 | 6h | TSK-WAKE-002 |
| TSK-WAKE-006 | 進捗可視化（ログ＋成功率/成長統計） | REQ-WAKE-001-F006 | P1 | 6h | TSK-WAKE-003 |
| TSK-WAKE-007 | リソース制限（メモリ2GB/CPU連続10分） | REQ-WAKE-001-NF004 | P0 | 8h | TSK-WAKE-003 |

### 4.2 受入チェック（抜粋）

- TSK-WAKE-003: 改善停止（閾値以下）でサイクル停止できる
- TSK-WAKE-007: CPU/メモリ制約で安全停止し、状態が保存される

---

## 5. SDDオントロジー構築（REQ-SDD-ONTO-001）

### 5.1 実装タスク

| タスクID | タスク名 | 対応要件 | 優先度 | 見積 | 依存 |
|---------|---------|---------|--------|------|------|
| TSK-SDD-ONTO-001 | SDDコア概念（4大概念＋サブクラス） | REQ-SDD-ONTO-001-F001 | P0 | 6h | - |
| TSK-SDD-ONTO-002 | EARS形式の形式化（5パターン＋構成要素） | REQ-SDD-ONTO-001-F002 | P0 | 6h | TSK-SDD-ONTO-001 |
| TSK-SDD-ONTO-003 | トレーサビリティ関係（逆関係＋推移性） | REQ-SDD-ONTO-001-F003 | P0 | 6h | TSK-SDD-ONTO-001 |
| TSK-SDD-ONTO-004 | 9憲法条項の形式化（Article I〜IX） | REQ-SDD-ONTO-001-F004 | P0 | 6h | TSK-SDD-ONTO-001 |
| TSK-SDD-ONTO-005 | 設計パターンオントロジー（カテゴリ＋適用関係） | REQ-SDD-ONTO-001-F005 | P1 | 6h | TSK-SDD-ONTO-001 |
| TSK-SDD-ONTO-006 | 推論ルール（検証/ギャップ検出/違反検出） | REQ-SDD-ONTO-001-F006 | P1 | 8h | TSK-SDD-ONTO-002, TSK-SDD-ONTO-003, TSK-SDD-ONTO-004 |
| TSK-SDD-ONTO-007 | オントロジーバリデーション（構文/循環/未定義/整合） | REQ-SDD-ONTO-001-NF006 | P0 | 10h | TSK-SDD-ONTO-001, TSK-SDD-ONTO-002, TSK-SDD-ONTO-003 |

### 5.2 受入チェック（抜粋）

- TSK-SDD-ONTO-001〜003: Turtle/OWLとして有効、基本推論（逆/推移）を満たす
- TSK-SDD-ONTO-004: 9条項が個体として参照可能
- TSK-SDD-ONTO-007: 構文エラー・循環参照・未定義参照を確実に検出

---

## 6. 統合・品質ゲート（推奨）

※ Phase 3を「実装可能な状態」にするための横断タスク。設計書のトレーサビリティ外。

| タスクID | タスク名 | 目的 | 見積 | 依存 |
|---------|---------|------|------|------|
| TSK-PHASE3-INT-001 | npm workspacesへの新規パッケージ追加 | packages/* の追加・ビルド統合 | 4h | - |
| TSK-PHASE3-INT-002 | CLIコマンド/エントリ追加 | Article II（CLI公開）を満たす | 6h | TSK-PHASE3-INT-001 |
| TSK-PHASE3-INT-003 | MCP E2E テスト（stdio） | tool→実装の疎通確認 | 6h | TSK-PHASE3-INT-001 |
| TSK-PHASE3-INT-004 | Traceability検証（REQ↔DES↔TSK） | Article V（追跡） | 4h | - |

---

## 7. 成果物

- Pattern Library Learning MCP: 抽出/抽象化/類似度/クラスター/永続化/圧縮/プライバシー
- Ontology Reasoning MCP: 定義/推論/整合/クエリ/マッピング/インポート/エラー/プライバシー
- Wake-Sleep: Wake/Sleep/サイクル/MDL/品質/進捗/リソース制限
- SDD Ontology: TTLモジュール群 + i18nラベル + バリデーション

---

**文書履歴**:
| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-05 | 初版作成 | GitHub Copilot |
