# MUSUBIX Security v2.1.0 要件定義書

**Version**: 2.1.0
**Date**: 2026-01-08
**Status**: ✅ APPROVED
**Author**: AI Agent (GitHub Copilot)

---

## 1. 概要

### 1.1 目的

musubix-security パッケージを v2.1.0 に拡張し、以下の3つの主要機能を追加する：

1. **EPIC-2**: CVEデータベース連携（NVD API統合）
2. **EPIC-3**: OWASP Top 10 / CWE Top 25 ルール実装
3. **EPIC-4**: 自動修正提案（LLM生成 → Z3検証）

### 1.2 背景

EPIC-1（テイント分析の高度化）は完了済み。本要件定義書では残りの3つのEPICを定義する。

### 1.3 スコープ

| 項目 | 含む | 含まない |
|------|------|----------|
| CVE連携 | NVD API, 依存関係スキャン, 脆弱性マッチング | 商用DB (Snyk, WhiteSource等) ※将来追加予定 |
| ルール実装 | OWASP Top 10 (10項目), CWE Top 25 (25項目), カスタムルール | SAST/DAST全機能 |
| 自動修正 | VS Code LM API経由のLLM提案, Z3形式検証, パッチ適用 | 完全自動修正（人間承認必須） |

---

## 2. EPIC-2: CVEデータベース連携

### 2.1 要件一覧

#### REQ-CVE-001: NVD API クライアント
> **EARS (Event-driven)**: WHEN the system needs CVE information, THE system SHALL query the NVD API with rate limiting and caching.

**Priority**: P0 (必須)
**Acceptance Criteria**:
- NVD API 2.0 に対応
- API Key サポート（環境変数 `NVD_API_KEY`）
- Rate limiting: API Key有り 50 req/30s, 無し 5 req/30s
- レスポンスキャッシュ（TTL: 24時間）
- タイムアウト: 30秒
- リトライ: 3回（指数バックオフ）

#### REQ-CVE-002: CVE 検索機能
> **EARS (Event-driven)**: WHEN a user searches for CVEs, THE system SHALL return matching vulnerabilities with CVSS scores and affected products.

**Priority**: P0 (必須)
**Acceptance Criteria**:
- キーワード検索
- CPE (Common Platform Enumeration) による製品検索
- CVSS スコア範囲フィルタ
- 日付範囲フィルタ（公開日、更新日）
- CWE ID フィルタ
- ページネーション対応

#### REQ-CVE-003: 依存関係脆弱性マッチング
> **EARS (Event-driven)**: WHEN analyzing package.json or package-lock.json, THE system SHALL identify CVEs affecting the project's dependencies.

**Priority**: P0 (必須)
**Acceptance Criteria**:
- package.json / package-lock.json パース
- npm パッケージ名 → CPE 変換
- バージョン範囲マッチング（semver対応）
- 推移的依存関係の解析
- 修正バージョン情報の提供

#### REQ-CVE-004: CVE レポート生成
> **EARS (Event-driven)**: WHEN vulnerability scan completes, THE system SHALL generate a comprehensive CVE report in multiple formats.

**Priority**: P1 (重要)
**Acceptance Criteria**:
- JSON / Markdown / HTML フォーマット
- CVSS スコア別サマリ
- 影響を受けるパッケージ一覧
- 推奨対策の提示
- SBOM (Software Bill of Materials) 連携準備

#### REQ-CVE-005: ローカルキャッシュ DB
> **EARS (State-driven)**: WHILE offline or API unavailable, THE system SHALL use local SQLite cache for CVE lookups.

**Priority**: P1 (重要)
**Acceptance Criteria**:
- SQLite ベースのローカルキャッシュ
- 差分更新（前回同期以降の変更のみ）
- 自動同期スケジュール（設定可能）
- キャッシュサイズ上限管理

---

## 3. EPIC-3: OWASP Top 10 / CWE Top 25 ルール

### 3.1 要件一覧

#### REQ-RULE-001: OWASP Top 10 2021 ルールセット
> **EARS (Ubiquitous)**: THE system SHALL detect all OWASP Top 10 2021 vulnerability categories.

**Priority**: P0 (必須)
**Acceptance Criteria**:

| カテゴリ | CWE | 検出方法 |
|---------|-----|----------|
| A01: Broken Access Control | CWE-22, 284, 285, 352, 639 | テイント + パターン |
| A02: Cryptographic Failures | CWE-259, 327, 328, 330 | パターンマッチ |
| A03: Injection | CWE-79, 89, 94, 77 | テイント分析 (EPIC-1) |
| A04: Insecure Design | CWE-209, 256, 501 | 設計パターン分析 |
| A05: Security Misconfiguration | CWE-16, 611, 1004 | 設定ファイル検査 |
| A06: Vulnerable Components | CWE-1035, 1104 | CVE連携 (EPIC-2) |
| A07: Auth Failures | CWE-287, 306, 307, 798 | パターン + テイント |
| A08: Data Integrity Failures | CWE-494, 502, 829 | デシリアライズ検出 |
| A09: Logging Failures | CWE-117, 223, 532, 778 | ログパターン分析 |
| A10: SSRF | CWE-918 | テイント分析 |

#### REQ-RULE-002: CWE Top 25 2023 ルールセット
> **EARS (Ubiquitous)**: THE system SHALL detect all CWE Top 25 2023 Most Dangerous Software Weaknesses.

**Priority**: P0 (必須)
**Acceptance Criteria**:

| Rank | CWE ID | Name | 検出方法 |
|------|--------|------|----------|
| 1 | CWE-787 | Out-of-bounds Write | バッファ解析 |
| 2 | CWE-79 | Cross-site Scripting | テイント |
| 3 | CWE-89 | SQL Injection | テイント |
| 4 | CWE-416 | Use After Free | メモリ解析 |
| 5 | CWE-78 | OS Command Injection | テイント |
| 6 | CWE-20 | Improper Input Validation | パターン |
| 7 | CWE-125 | Out-of-bounds Read | バッファ解析 |
| 8 | CWE-22 | Path Traversal | テイント |
| 9 | CWE-352 | CSRF | パターン |
| 10 | CWE-434 | Unrestricted Upload | パターン |
| 11 | CWE-862 | Missing Authorization | パターン |
| 12 | CWE-476 | NULL Pointer Dereference | 型解析 |
| 13 | CWE-287 | Improper Authentication | パターン |
| 14 | CWE-190 | Integer Overflow | 数値解析 |
| 15 | CWE-502 | Deserialization | テイント |
| 16 | CWE-77 | Command Injection | テイント |
| 17 | CWE-119 | Buffer Overflow | バッファ解析 |
| 18 | CWE-798 | Hard-coded Credentials | パターン |
| 19 | CWE-918 | SSRF | テイント |
| 20 | CWE-306 | Missing Authentication | パターン |
| 21 | CWE-362 | Race Condition | 並行性解析 |
| 22 | CWE-269 | Improper Privilege Mgmt | パターン |
| 23 | CWE-94 | Code Injection | テイント |
| 24 | CWE-863 | Incorrect Authorization | パターン |
| 25 | CWE-276 | Incorrect Default Perms | パターン |

#### REQ-RULE-003: ルールエンジン
> **EARS (Event-driven)**: WHEN analyzing code, THE system SHALL execute rules with configurable severity thresholds and exclusions.

**Priority**: P0 (必須)
**Acceptance Criteria**:
- ルール有効/無効の切り替え
- 重大度閾値の設定
- ファイル/パス除外パターン
- インラインサプレッション（`// security-ignore: CWE-79`）
- カスタムルール追加API

#### REQ-RULE-004: ルール設定ファイル
> **EARS (State-driven)**: WHILE a configuration file exists, THE system SHALL load and apply rule settings from it.

**Priority**: P1 (重要)
**Acceptance Criteria**:
- `.musubix-security.yml` / `.musubix-security.json` サポート
- プロファイル（strict, standard, permissive）
- 継承・オーバーライド機能
- IDE 統合用スキーマ提供

#### REQ-RULE-005: Finding 出力フォーマット
> **EARS (Event-driven)**: WHEN rules detect issues, THE system SHALL output findings in SARIF and custom formats.

**Priority**: P1 (重要)
**Acceptance Criteria**:
- SARIF 2.1.0 準拠出力
- JSON / Markdown / HTML レポート
- GitHub Code Scanning 互換
- CI/CD 統合用終了コード

---

## 4. EPIC-4: 自動修正提案

### 4.1 要件一覧

#### REQ-FIX-001: VS Code LM API 経由の修正提案生成
> **EARS (Event-driven)**: WHEN a vulnerability is detected, THE system SHALL generate fix suggestions using VS Code Language Model API.

**Priority**: P0 (必須)
**Acceptance Criteria**:
- VS Code LM API (`@vscode/lm-api`) 経由でCopilot/LLMにアクセス
- 脆弱性コンテキスト（コード、CWE、説明）をプロンプトに含む
- 複数の修正案を生成（最大3案）
- 修正案にはdiff形式を含む
- プロンプトテンプレートのカスタマイズ
- VS Code外実行時のフォールバック（CLI用モック/スタブ）

#### REQ-FIX-002: Z3 形式検証
> **EARS (Event-driven)**: WHEN a fix suggestion is generated, THE system SHALL verify it using Z3 SMT solver.

**Priority**: P0 (必須)
**Acceptance Criteria**:
- 修正前後のセマンティクス保持検証
- テイントフロー除去の検証
- 入力バリデーション追加の検証
- 検証結果のスコアリング（0.0-1.0）
- 検証失敗時の理由説明

#### REQ-FIX-003: 修正安全性評価
> **EARS (Event-driven)**: WHEN fix verification completes, THE system SHALL score the fix based on multiple criteria.

**Priority**: P0 (必須)
**Acceptance Criteria**:
- 評価基準:
  - セマンティクス保持 (30%)
  - 脆弱性除去 (30%)
  - コード品質 (20%)
  - パフォーマンス影響 (10%)
  - 後方互換性 (10%)
- 総合スコア閾値設定（デフォルト: 0.7）
- 人間レビュー推奨フラグ

#### REQ-FIX-004: パッチ適用エンジン
> **EARS (Event-driven)**: WHEN a fix is approved, THE system SHALL apply the patch to the source code.

**Priority**: P1 (重要)
**Acceptance Criteria**:
- unified diff 適用
- 適用前バックアップ
- 適用結果の検証（ビルド・テスト実行）
- ロールバック機能
- Git 統合（コミットメッセージ生成）

#### REQ-FIX-005: 修正学習システム
> **EARS (Event-driven)**: WHEN a fix is accepted or rejected, THE system SHALL learn from the feedback.

**Priority**: P2 (任意)
**Acceptance Criteria**:
- Accept/Reject フィードバック記録
- 類似脆弱性への修正パターン適用
- プロンプト改善への活用
- プライバシー保護（ローカル学習のみ）

---

## 5. 非機能要件

### 5.1 パフォーマンス

| 項目 | 要件 |
|------|------|
| CVE検索応答時間 | キャッシュヒット: < 100ms, API呼び出し: < 5s |
| ルール実行時間 | 1000行あたり < 500ms |
| LLM修正生成時間 | < 30s（タイムアウト設定可能） |
| Z3検証時間 | < 10s/修正案 |

### 5.2 スケーラビリティ

| 項目 | 要件 |
|------|------|
| 同時スキャン数 | 最大10並列 |
| ローカルキャッシュ容量 | 最大1GB（設定可能） |
| 修正提案キュー | 最大100件/プロジェクト |

### 5.3 セキュリティ

| 項目 | 要件 |
|------|------|
| API Key管理 | 環境変数/設定ファイル（暗号化推奨） |
| LLMへのコード送信 | オプトイン、機密フィルタリング |
| ローカルデータ | 暗号化オプション |

---

## 6. タスク分解案

### EPIC-2: CVEデータベース連携 (8タスク)

| ID | タスク | 依存 | 工数 |
|----|--------|------|------|
| TSK-CVE-001 | NVD API クライアント基盤 | - | 4h |
| TSK-CVE-002 | Rate limiting & キャッシュ | 001 | 3h |
| TSK-CVE-003 | CVE 検索機能 | 001 | 4h |
| TSK-CVE-004 | CPE マッチングエンジン | 003 | 4h |
| TSK-CVE-005 | package.json パーサー | - | 2h |
| TSK-CVE-006 | 依存関係脆弱性スキャナー | 004, 005 | 5h |
| TSK-CVE-007 | SQLite ローカルキャッシュ | 002 | 4h |
| TSK-CVE-008 | CVE レポート生成 | 006 | 3h |

### EPIC-3: OWASP / CWE ルール (10タスク)

| ID | タスク | 依存 | 工数 |
|----|--------|------|------|
| TSK-RULE-001 | ルールエンジン基盤 | - | 4h |
| TSK-RULE-002 | ルール設定パーサー | 001 | 3h |
| TSK-RULE-003 | OWASP A01-A05 ルール | 001 | 6h |
| TSK-RULE-004 | OWASP A06-A10 ルール | 001 | 6h |
| TSK-RULE-005 | CWE Top 25 ルール (1-13) | 001 | 6h |
| TSK-RULE-006 | CWE Top 25 ルール (14-25) | 001 | 6h |
| TSK-RULE-007 | インラインサプレッション | 001 | 2h |
| TSK-RULE-008 | SARIF 出力 | 001 | 3h |
| TSK-RULE-009 | カスタムルール API | 001 | 3h |
| TSK-RULE-010 | ルールテストスイート | 003-006 | 4h |

### EPIC-4: 自動修正提案 (8タスク)

| ID | タスク | 依存 | 工数 |
|----|--------|------|------|
| TSK-FIX-001 | VS Code LM API アダプター | - | 4h |
| TSK-FIX-002 | 修正提案プロンプト設計 | 001 | 3h |
| TSK-FIX-003 | LLM 修正生成エンジン | 001, 002 | 5h |
| TSK-FIX-004 | Z3 統合アダプター | - | 4h |
| TSK-FIX-005 | 形式検証エンジン | 004 | 6h |
| TSK-FIX-006 | 修正安全性スコアリング | 003, 005 | 4h |
| TSK-FIX-007 | パッチ適用エンジン | 003 | 4h |
| TSK-FIX-008 | 修正フィードバック学習 | 007 | 3h |

---

## 7. トレーサビリティ

### 要件 → 設計（予定）

| 要件ID | 設計ID |
|--------|--------|
| REQ-CVE-001 | DES-CVE-001 |
| REQ-CVE-002 | DES-CVE-002 |
| REQ-CVE-003 | DES-CVE-003 |
| REQ-RULE-001 | DES-RULE-001 |
| REQ-RULE-002 | DES-RULE-002 |
| REQ-FIX-001 | DES-FIX-001 |
| REQ-FIX-002 | DES-FIX-002 |

---

## 8. 承認

- [x] 要件の完全性確認
- [x] EARS形式の検証
- [x] 優先度の妥当性確認
- [x] 工数見積もりの確認
- [x] ユーザー承認 (2026-01-08)

---

**レビュー依頼**: 上記要件定義についてフィードバックをお願いします。

- 要件の追加・削除・変更
- 優先度の調整
- 工数見積もりへの意見
- 技術的な懸念事項
