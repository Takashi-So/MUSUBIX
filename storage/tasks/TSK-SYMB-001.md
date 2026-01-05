# タスク一覧: MUSUBIX SYMB拡張（記号的推論・形式検証・Constitution強制）

> **文書ID**: TSK-SYMB-001  
> **バージョン**: 0.1  
> **作成日**: 2026-01-05  
> **対象設計**: DES-SYMB-001 v0.8  
> **対象要件**: REQ-SYMB-001 v1.1  
> **総タスク数**: 19

## フェーズ概要（REQ-SYMB-001に準拠）

| Phase | 目的 | タスク | 期間（目安） |
|------|------|------|-------------|
| Phase 1 | 基盤強化 | TSK-SYMB-001〜008 | 1-2週間 |
| Phase 2 | 形式検証統合 | TSK-SYMB-009〜013 | 2-3週間 |
| Phase 3 | 高度機能 | TSK-SYMB-014〜019 | 3-4週間 |

---

## Phase 1: 基盤強化（1-2週間）

### TSK-SYMB-001: SemanticCodeFilterPipeline 基盤実装
- **説明**: セマンティックフィルターのパイプライン（入力→評価→採否→説明）を`core`に実装する。
- **要件トレース**: REQ-SF-001, REQ-NFR-003
- **設計トレース**: DES-SYMB-001 §4.1, §5.1, §6.3
- **優先度**: P0
- **見積もり**: 6h
- **受入条件**:
  - [ ] `FilterInput`/`FilterOutput` の型契約が成立する
  - [ ] 最低1つの規則でaccept/rejectが動作する
  - [ ] すべての判定に `Explanation.summary` が付与される
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-002: HallucinationDetector + ProjectSymbolIndex 実装
- **説明**: 存在しないAPI参照を検出するためのプロジェクトシンボル索引と検出器を実装する。
- **要件トレース**: REQ-SF-002
- **設計トレース**: DES-SYMB-001 §4.2
- **優先度**: P0
- **見積もり**: 8h
- **受入条件**:
  - [ ] workspace内のimport/シンボル解決で不整合が検出できる
  - [ ] 検出結果に根拠（どの参照が解決不能か）が含まれる
  - [ ] 修正提案（候補）が返せる（最小で1件）
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-003: ConstitutionRuleRegistry + ViolationReporter（基盤）
- **説明**: Constitutionを「実行可能ルール」として登録/実行し、違反レポートを構築する基盤を実装する。
- **要件トレース**: REQ-CONST-001, REQ-CONST-005, REQ-NFR-003
- **設計トレース**: DES-SYMB-001 §4.9, §4.13, §5.1, §6.3
- **優先度**: P0
- **見積もり**: 8h
- **受入条件**:
  - [ ] `ConstitutionReport` の最小契約（pass/fail、violations、explanation）が成立する
  - [ ] enforcement（block/warn/log）が少なくとも2種類で動作する
  - [ ] ルールID/条項番号がレポートで追跡できる
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-004: Article Validator 群（I〜IX）実装
- **説明**: Article I〜IXの各検証器（最小版）と、段階（stage）に応じた実行を実装する。
- **要件トレース**: REQ-CONST-002〜010
- **設計トレース**: DES-SYMB-001 §4.10〜§4.18
- **優先度**: P0
- **見積もり**: 12h
- **受入条件**:
  - [ ] I/II/III/V/VI/VII/VIII/IXを個別に実行できる
  - [ ] Article IX（統合テスト優先）の違反が検出できる（最小ルール）
  - [ ] ブロック条件が成立した場合に処理が中断される
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-005: ConfidenceEstimator 実装
- **説明**: 信頼度推定（0.0-1.0）と4観点分解、リスク要因識別を実装する。
- **要件トレース**: REQ-ROUTE-001
- **設計トレース**: DES-SYMB-001 §4.19
- **優先度**: P0
- **見積もり**: 6h
- **受入条件**:
  - [ ] `score` が0.0-1.0で出力される
  - [ ] 4観点（syntactic/semantic/factual/consistency）が出力される
  - [ ] `riskFactors` が最小1件出力できる
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-006: ConfidenceBasedRouter 実装
- **説明**: 閾値ベースのルーティング決定と説明、実行計画（verify/regenerate）を実装する。
- **要件トレース**: REQ-ROUTE-002
- **設計トレース**: DES-SYMB-001 §4.20, §5.5, §6.3
- **優先度**: P0
- **見積もり**: 6h
- **受入条件**:
  - [ ] 閾値ルール（`x ≥ 0.8` / `0.5 ≤ x < 0.8` / `x < 0.5`）が動作する
  - [ ] `routingReason` に `Explanation.summary` が付与される
  - [ ] `executionPlan` が生成される
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-007: ErrorHandlingStrategy + graceful degradation 統合
- **説明**: 外部依存（Z3/YATA）失敗時の再試行/縮退/中断を `Result<T, E>` とメタデータで統一する。
- **要件トレース**: REQ-NFR-004
- **設計トレース**: DES-SYMB-001 §6.4
- **優先度**: P0
- **見積もり**: 6h
- **受入条件**:
  - [ ] 失敗分類（Z3_TIMEOUT等）とアクションがマップできる
  - [ ] 部分結果メタデータ（unavailableChecks）が返せる
  - [ ] `StructuredLogger.timedAsync` で外部呼び出し計測ができる

### TSK-SYMB-008: MCPツール（Phase 1）追加
- **説明**: `sdd_semantic_filter` / `sdd_route_candidate` を `mcp-server` に追加し、core実装を呼び出す。
- **要件トレース**: REQ-CONST-006, REQ-SF-001, REQ-ROUTE-002
- **設計トレース**: DES-SYMB-001 §5.6
- **優先度**: P0
- **見積もり**: 6h
- **受入条件**:
  - [ ] JSON Schema入力を受理し、`success({...})` 形式で返せる
  - [ ] `explanation` を返却JSONに含められる
  - [ ] 統合テスト（最低1件）が追加される

---

## Phase 2: 形式検証統合（2-3週間）

### TSK-SYMB-009: EarsToFormalSpecConverter（EARS→AST→SMT-LIB）
- **説明**: EARS要件文を構造化し、VC生成の前段としてSMT-LIBの雛形を出力する。
- **要件トレース**: REQ-FV-001
- **設計トレース**: DES-SYMB-001 §4.4
- **優先度**: P0
- **見積もり**: 10h
- **受入条件**:
  - [ ] 5つのEARSパターンを受理し、ASTへ正規化できる
  - [ ] `requirementId` と生成物がリンクされる
  - [ ] SMT-LIB文字列が出力できる（最小例で良い）
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-010: VerificationConditionGenerator 実装
- **説明**: AST/ドメインモデルからVC集合を生成し、検証器に渡せる形にする。
- **要件トレース**: REQ-FV-005
- **設計トレース**: DES-SYMB-001 §4.8
- **優先度**: P0
- **見積もり**: 8h
- **受入条件**:
  - [ ] VCが複数生成できる
  - [ ] VCに要件ID・対象コード要素の参照が含まれる
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-011: Z3Adapter + Pre/Post/Invariant Verifier 実装
- **説明**: Z3実行（送信/パース/タイムアウト）と、事前/事後/不変条件の検証器を実装する。
- **要件トレース**: REQ-FV-002, REQ-FV-003, REQ-FV-004, REQ-NFR-001
- **設計トレース**: DES-SYMB-001 §4.5〜§4.7, §6.1
- **優先度**: P0
- **見積もり**: 14h
- **受入条件**:
  - [ ] `valid/invalid/unknown` の判定が返る
  - [ ] タイムアウト時に部分結果とタイムアウト情報が返る
  - [ ] SMT-LIBを証跡として返せる
  - [ ] Vitestでユニットテストが追加される

### TSK-SYMB-012: MCPツール（Phase 2）追加（sdd_formal_verify）
- **説明**: `sdd_formal_verify` を追加し、coreの形式検証を呼び出す。
- **要件トレース**: REQ-CONST-006, REQ-FV-001〜005
- **設計トレース**: DES-SYMB-001 §5.6
- **優先度**: P0
- **見積もり**: 6h
- **受入条件**:
  - [ ] `verdict/evidence/fixSuggestions` を返却できる
  - [ ] `explanation` を返却JSONに含められる
  - [ ] 統合テスト（最低1件）が追加される

### TSK-SYMB-013: SecuritySandbox + SecretScanner 統合
- **説明**: 実行境界（分析優先）と機密/OWASP検出、redact方針を統合する。
- **要件トレース**: REQ-NFR-005
- **設計トレース**: DES-SYMB-001 §6.5
- **優先度**: P0
- **見積もり**: 8h
- **受入条件**:
  - [ ] `SecurityScanner`によりsecret/OWASPが検出できる
  - [ ] 機密がログ/学習データに混入しない（redact/拒否が動作）
  - [ ] 監査ログへセキュリティイベントが記録できる（TSK-SYMB-017と連携）

---

## Phase 3: 高度機能（3-4週間）

### TSK-SYMB-014: CandidateRanker 実装
- **説明**: 複数候補をスコアリングし、推奨候補と内訳を返す。
- **要件トレース**: REQ-SF-003
- **設計トレース**: DES-SYMB-001 §4.3
- **優先度**: P1
- **見積もり**: 6h
- **受入条件**:
  - [ ] 候補がスコア順に並ぶ
  - [ ] 内訳（metric→score）が返る
  - [ ] 推奨理由が説明できる

### TSK-SYMB-015: ResultBlender 実装
- **説明**: neural/symbolicの結果を3戦略でブレンドし、帰属割合を返す。
- **要件トレース**: REQ-ROUTE-003
- **設計トレース**: DES-SYMB-001 §4.21
- **優先度**: P1
- **見積もり**: 6h
- **受入条件**:
  - [ ] 3戦略（neural_priority/symbolic_priority/confidence_weighted）が選べる
  - [ ] `attribution`（neuralPct/symbolicPct）が返る
  - [ ] symbolicがinvalidのときニューラル単独採用にならない

### TSK-SYMB-016: ExtensibleRuleConfig（設定ロード/スキーマ検証）
- **説明**: セマンティックルール/Constitutionのルール設定を`storage/`から読み、スキーマ検証して適用する。
- **要件トレース**: REQ-NFR-002, REQ-CONST-001
- **設計トレース**: DES-SYMB-001 §6.2
- **優先度**: P1
- **見積もり**: 6h
- **受入条件**:
  - [ ] 設定変更のみでルール追加/変更が反映できる
  - [ ] 不正スキーマはエラーとして扱い、説明が返る
  - [ ] 参照した設定ファイルをArtifactRefとして追跡できる

### TSK-SYMB-017: AuditLogger（ハッシュチェーン/保持/アーカイブ）
- **説明**: 監査ログを分離して保存し、改ざん検出・保持・アーカイブを提供する。
- **要件トレース**: REQ-NFR-006
- **設計トレース**: DES-SYMB-001 §6.6
- **優先度**: P1
- **見積もり**: 8h
- **受入条件**:
  - [ ] `prevHash`→`hash` のチェーンが成立する
  - [ ] 保持期限に応じて `storage/archive/` へ移動できる
  - [ ] 整合性検証（改ざん検出）ができる

### TSK-SYMB-018: PerformanceBudget（段階別予算/計測/部分結果）実装
- **説明**: 形式検証の段階別予算とSLO評価の計測を実装する。
- **要件トレース**: REQ-NFR-001
- **設計トレース**: DES-SYMB-001 §6.1
- **優先度**: P1
- **見積もり**: 6h
- **受入条件**:
  - [ ] 段階別の所要時間が計測される
  - [ ] 予算超過時に `PartialResultMetadata` が付与される

### TSK-SYMB-019: 品質ゲート（承認条件）検証タスク
- **説明**: DES 7.2の承認条件に沿って、トレーサビリティ・統合テスト・モック例外承認等を検証する。
- **要件トレース**: REQ-CONST-004, REQ-CONST-010, REQ-NFR-003
- **設計トレース**: DES-SYMB-001 §7.2
- **優先度**: P0
- **見積もり**: 6h
- **受入条件**:
  - [ ] 要件↔設計↔コード↔テストのリンクが100%成立する
  - [ ] 統合テスト優先（モック例外時は理由と承認記録）が成立する
  - [ ] 主要成果物に説明（Explanation）が付与される
