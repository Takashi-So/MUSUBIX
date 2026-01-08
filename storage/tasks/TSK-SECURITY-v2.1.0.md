# MUSUBIX Security v2.1.0 タスク分解書

**Version**: 1.0.0
**Date**: 2026-01-08
**Status**: ✅ APPROVED
**Trace**: DES-SECURITY-EPIC2-CVE, DES-SECURITY-EPIC3-RULES, DES-SECURITY-EPIC4-AUTOFIX

---

## 概要

| EPIC | タスク数 | 推定工数 | 優先度 |
|------|----------|----------|--------|
| EPIC-2: CVEデータベース連携 | 8 | 29h | P0 |
| EPIC-3: OWASP/CWE ルール | 10 | 43h | P0 |
| EPIC-4: 自動修正提案 | 8 | 33h | P0 |
| **合計** | **26** | **105h** | - |

---

## EPIC-2: CVEデータベース連携

### TSK-CVE-001: NVD API クライアント基盤
**工数**: 4h | **依存**: なし | **設計**: DES-CVE-001

**実装内容**:
- `packages/security/src/cve/nvd-client.ts` 作成
- NVD API 2.0 エンドポイント接続
- 基本的な GET リクエスト実装
- API Key 環境変数サポート (`NVD_API_KEY`)
- タイムアウト・リトライ設定

**受け入れ基準**:
- [ ] CVE ID で単一CVE取得可能
- [ ] API Key 有無で動作確認
- [ ] タイムアウト30秒、リトライ3回

---

### TSK-CVE-002: Rate Limiting & キャッシュ
**工数**: 3h | **依存**: TSK-CVE-001 | **設計**: DES-CVE-002, DES-CVE-003

**実装内容**:
- `packages/security/src/cve/rate-limiter.ts` 作成
- Token bucket アルゴリズム実装
- API Key有り: 50 req/30s, 無し: 5 req/30s
- メモリキャッシュ統合（TTL: 24h）

**受け入れ基準**:
- [ ] Rate limit 超過時に自動待機
- [ ] キャッシュヒット時はAPI呼び出しスキップ
- [ ] `getStatus()` で残りリクエスト数取得可能

---

### TSK-CVE-003: CVE 検索機能
**工数**: 4h | **依存**: TSK-CVE-001 | **設計**: DES-CVE-001

**実装内容**:
- `searchByKeyword()` - キーワード検索
- `searchByCPE()` - CPE検索
- `searchByCWE()` - CWE検索
- `searchByDateRange()` - 日付範囲検索
- ページネーション対応

**受け入れ基準**:
- [ ] 各検索メソッドが正常動作
- [ ] CVSS スコアフィルタリング可能
- [ ] 2000件超の結果もページネーションで取得可能

---

### TSK-CVE-004: CPE マッチングエンジン
**工数**: 4h | **依存**: TSK-CVE-003 | **設計**: DES-CVE-004

**実装内容**:
- `packages/security/src/cve/cpe-matcher.ts` 作成
- npm パッケージ名 → CPE URI 変換
- semver バージョン範囲マッチング
- 既知マッピング辞書（主要パッケージ）

**受け入れ基準**:
- [ ] `lodash@4.17.20` → 正しいCPE生成
- [ ] バージョン範囲 `>=4.0.0 <4.17.21` マッチング正常
- [ ] 主要npm パッケージ（lodash, express, axios等）マッピング済み

---

### TSK-CVE-005: package.json パーサー
**工数**: 2h | **依存**: なし | **設計**: DES-CVE-005

**実装内容**:
- `packages/security/src/cve/dependency-parser.ts` 作成
- package.json 解析（直接依存）
- package-lock.json 解析（推移的依存）
- 依存パス記録

**受け入れ基準**:
- [ ] package.json から dependencies/devDependencies 抽出
- [ ] package-lock.json から全依存抽出
- [ ] 推移的依存のパス情報付与

---

### TSK-CVE-006: 依存関係脆弱性スキャナー
**工数**: 5h | **依存**: TSK-CVE-004, TSK-CVE-005 | **設計**: DES-CVE-006

**実装内容**:
- `packages/security/src/cve/cve-scanner.ts` 作成
- DependencyParser + CPEMatcher + NVDClient 統合
- 並列スキャン（concurrency設定可能）
- 進捗コールバック

**受け入れ基準**:
- [ ] プロジェクトディレクトリ指定でスキャン実行
- [ ] CVEFinding[] 形式で結果返却
- [ ] オフラインモード対応（キャッシュのみ）

---

### TSK-CVE-007: SQLite ローカルキャッシュ
**工数**: 4h | **依存**: TSK-CVE-002 | **設計**: DES-CVE-003

**実装内容**:
- `packages/security/src/cve/cve-cache.ts` 作成
- better-sqlite3 依存追加
- CVE テーブル設計・マイグレーション
- 差分同期（incremental sync）
- サイズ上限管理・クリーンアップ

**受け入れ基準**:
- [ ] SQLite DB 作成・CVE保存/取得
- [ ] 差分同期で更新分のみ取得
- [ ] 500MB 超過時に古いエントリ削除

---

### TSK-CVE-008: CVE レポート生成
**工数**: 3h | **依存**: TSK-CVE-006 | **設計**: DES-CVE-007

**実装内容**:
- `packages/security/src/cve/report-generator.ts` 作成
- JSON / Markdown / HTML / SARIF 形式
- CVSS 重大度別サマリ
- 推奨対策の自動生成

**受け入れ基準**:
- [ ] 4形式すべて出力可能
- [ ] 重大度別件数サマリ含む
- [ ] SARIF は GitHub Code Scanning 互換

---

## EPIC-3: OWASP Top 10 / CWE Top 25 ルール

### TSK-RULE-001: ルールエンジン基盤
**工数**: 4h | **依存**: なし | **設計**: DES-RULE-001, DES-RULE-002

**実装内容**:
- `packages/security/src/rules/engine/rule-engine.ts`
- `packages/security/src/rules/engine/rule-registry.ts`
- `packages/security/src/rules/engine/rule-context.ts`
- SecurityRule インターフェース定義
- RuleContextBuilder（テイント分析/DFG統合）

**受け入れ基準**:
- [ ] ルール登録・実行フロー動作
- [ ] RuleContext にテイント分析結果含める
- [ ] 複数ルール並列実行可能

---

### TSK-RULE-002: ルール設定パーサー
**工数**: 3h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-004

**実装内容**:
- `packages/security/src/rules/config/config-parser.ts`
- `packages/security/src/rules/config/config-schema.ts`
- `packages/security/src/rules/config/profiles.ts`
- `.musubix-security.yml` / `.json` サポート
- プロファイル（strict/standard/permissive）

**受け入れ基準**:
- [ ] YAML/JSON 両形式読み込み
- [ ] プロファイルによるルール有効/無効切替
- [ ] 継承・オーバーライド動作

---

### TSK-RULE-003: OWASP A01-A05 ルール
**工数**: 6h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-005

**実装内容**:
- `a01-broken-access.ts` - Broken Access Control
- `a02-crypto-failures.ts` - Cryptographic Failures
- `a03-injection.ts` - Injection（テイント連携）
- `a04-insecure-design.ts` - Insecure Design
- `a05-misconfig.ts` - Security Misconfiguration

**受け入れ基準**:
- [ ] 各ルールでテストケース検出
- [ ] CWE マッピング正確
- [ ] 適切な severity 設定

---

### TSK-RULE-004: OWASP A06-A10 ルール
**工数**: 6h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-005

**実装内容**:
- `a06-vuln-components.ts` - Vulnerable Components（EPIC-2連携）
- `a07-auth-failures.ts` - Auth Failures
- `a08-data-integrity.ts` - Data Integrity Failures
- `a09-logging-failures.ts` - Logging Failures
- `a10-ssrf.ts` - SSRF（テイント連携）

**受け入れ基準**:
- [ ] A06 は EPIC-2 CVEスキャナー呼び出し
- [ ] 各ルールでテストケース検出
- [ ] テイント分析との連携動作

---

### TSK-RULE-005: CWE Top 25 ルール (1-13)
**工数**: 6h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-006

**実装内容**:
- CWE-787 (Out-of-bounds Write)
- CWE-079 (XSS)
- CWE-089 (SQL Injection)
- CWE-416 (Use After Free)
- CWE-078 (OS Command Injection)
- CWE-020 (Improper Input Validation)
- CWE-125 (Out-of-bounds Read)
- CWE-022 (Path Traversal)
- CWE-352 (CSRF)
- CWE-434 (Unrestricted Upload)
- CWE-862 (Missing Authorization)
- CWE-476 (NULL Pointer Dereference)
- CWE-287 (Improper Authentication)

**受け入れ基準**:
- [ ] 13ルールすべて実装
- [ ] 各ルールにテストケース
- [ ] OWASPルールとの重複排除

---

### TSK-RULE-006: CWE Top 25 ルール (14-25)
**工数**: 6h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-006

**実装内容**:
- CWE-190 (Integer Overflow)
- CWE-502 (Deserialization)
- CWE-077 (Command Injection)
- CWE-119 (Buffer Overflow)
- CWE-798 (Hard-coded Credentials)
- CWE-918 (SSRF)
- CWE-306 (Missing Authentication)
- CWE-362 (Race Condition)
- CWE-269 (Improper Privilege Mgmt)
- CWE-094 (Code Injection)
- CWE-863 (Incorrect Authorization)
- CWE-276 (Incorrect Default Perms)

**受け入れ基準**:
- [ ] 12ルールすべて実装
- [ ] 各ルールにテストケース
- [ ] TypeScript特有のパターン検出

---

### TSK-RULE-007: インラインサプレッション
**工数**: 2h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-008

**実装内容**:
- `packages/security/src/rules/suppression/inline-parser.ts`
- `packages/security/src/rules/suppression/suppression-manager.ts`
- `// security-ignore:` コメント解析
- ファイル/行/次行サプレッション

**受け入れ基準**:
- [ ] `// security-ignore: CWE-079` で行サプレッション
- [ ] `// security-ignore-next-line:` 対応
- [ ] `/* security-ignore-file: */` 対応

---

### TSK-RULE-008: SARIF 出力
**工数**: 3h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-007

**実装内容**:
- `packages/security/src/rules/output/sarif-generator.ts`
- `packages/security/src/rules/output/markdown-generator.ts`
- `packages/security/src/rules/output/html-generator.ts`
- SARIF 2.1.0 準拠

**受け入れ基準**:
- [ ] SARIF スキーマ検証パス
- [ ] GitHub Code Scanning で読み込み可能
- [ ] Markdown/HTML も読みやすく整形

---

### TSK-RULE-009: カスタムルール API
**工数**: 3h | **依存**: TSK-RULE-001 | **設計**: DES-RULE-002

**実装内容**:
- カスタムルール登録 API
- ルールプラグイン読み込み
- ドキュメント・サンプル

**受け入れ基準**:
- [ ] `engine.registerRule(customRule)` で追加可能
- [ ] 外部ファイルからルール読み込み
- [ ] サンプルカスタムルール提供

---

### TSK-RULE-010: ルールテストスイート
**工数**: 4h | **依存**: TSK-RULE-003〜006 | **設計**: -

**実装内容**:
- 全ルール用のテストケース作成
- 脆弱なコードサンプル
- 安全なコードサンプル（False Positive チェック）

**受け入れ基準**:
- [ ] 全35ルール（OWASP 10 + CWE 25）にテスト
- [ ] True Positive / False Positive 両方確認
- [ ] カバレッジ 90% 以上

---

## EPIC-4: 自動修正提案

### TSK-FIX-001: VS Code LM API アダプター
**工数**: 4h | **依存**: なし | **設計**: DES-FIX-001

**実装内容**:
- `packages/security/src/autofix/llm/lm-api-adapter.ts`
- VSCodeLMAdapter クラス（VS Code 内用）
- MockLMAdapter クラス（CLI/テスト用）
- LM API 存在チェック

**受け入れ基準**:
- [ ] VS Code 内で Copilot 呼び出し成功
- [ ] VS Code 外では MockAdapter にフォールバック
- [ ] `isAvailable()` で利用可否判定

---

### TSK-FIX-002: 修正提案プロンプト設計
**工数**: 3h | **依存**: TSK-FIX-001 | **設計**: DES-FIX-002

**実装内容**:
- `packages/security/src/autofix/llm/prompt-builder.ts`
- `packages/security/src/autofix/llm/prompt-templates.ts`
- `packages/security/src/autofix/llm/response-parser.ts`
- CWE別プロンプトテンプレート
- JSON 形式レスポンスパース

**受け入れ基準**:
- [ ] 脆弱性コンテキストを含むプロンプト生成
- [ ] 複数修正案（最大3案）のパース
- [ ] unified diff 形式の抽出

---

### TSK-FIX-003: LLM 修正生成エンジン
**工数**: 5h | **依存**: TSK-FIX-001, TSK-FIX-002 | **設計**: DES-FIX-001, DES-FIX-002

**実装内容**:
- LMAdapter + PromptBuilder 統合
- FixSuggestion 生成フロー
- エラーハンドリング・リトライ
- ストリーミング対応

**受け入れ基準**:
- [ ] RuleFinding → FixSuggestion[] 変換
- [ ] タイムアウト30秒
- [ ] LM API エラー時のグレースフルフォールバック

---

### TSK-FIX-004: Z3 統合アダプター
**工数**: 4h | **依存**: なし | **設計**: DES-FIX-003

**実装内容**:
- `packages/security/src/autofix/verification/z3-adapter.ts`
- musubix-formal-verify パッケージとの連携
- コード → Z3 式変換
- 検証結果型定義

**受け入れ基準**:
- [ ] Z3Solver インスタンス取得
- [ ] 簡単な条件式の検証成功
- [ ] タイムアウト10秒/検証

---

### TSK-FIX-005: 形式検証エンジン
**工数**: 6h | **依存**: TSK-FIX-004 | **設計**: DES-FIX-004

**実装内容**:
- `packages/security/src/autofix/verification/semantic-verifier.ts`
- `packages/security/src/autofix/verification/taint-verifier.ts`
- セマンティクス保持検証
- テイントフロー除去検証
- 新規脆弱性導入チェック

**受け入れ基準**:
- [ ] 修正前後のセマンティクス比較
- [ ] テイント分析結果の比較
- [ ] VerificationReport 生成

---

### TSK-FIX-006: 修正安全性スコアリング
**工数**: 4h | **依存**: TSK-FIX-003, TSK-FIX-005 | **設計**: DES-FIX-005

**実装内容**:
- `packages/security/src/autofix/scoring/safety-scorer.ts`
- `packages/security/src/autofix/scoring/criteria.ts`
- 5基準スコアリング
- 閾値設定・推奨判定

**受け入れ基準**:
- [ ] 5基準の重み付きスコア計算
- [ ] 閾値0.7未満は `humanReviewRequired: true`
- [ ] recommendation: 'apply' | 'review' | 'reject'

---

### TSK-FIX-007: パッチ適用エンジン
**工数**: 4h | **依存**: TSK-FIX-003 | **設計**: DES-FIX-006

**実装内容**:
- `packages/security/src/autofix/patch/patch-applier.ts`
- `packages/security/src/autofix/patch/diff-generator.ts`
- `packages/security/src/autofix/patch/backup-manager.ts`
- `packages/security/src/autofix/patch/rollback.ts`
- unified diff 適用
- バックアップ・ロールバック

**受け入れ基準**:
- [ ] diff 形式パッチ適用成功
- [ ] バックアップファイル作成
- [ ] ロールバック動作確認

---

### TSK-FIX-008: 修正フィードバック学習
**工数**: 3h | **依存**: TSK-FIX-007 | **設計**: DES-FIX-007

**実装内容**:
- `packages/security/src/autofix/learning/feedback-collector.ts`
- `packages/security/src/autofix/learning/pattern-learner.ts`
- Accept/Reject/Modify フィードバック記録
- 類似脆弱性への適用

**受け入れ基準**:
- [ ] フィードバック記録・永続化
- [ ] 類似脆弱性検索
- [ ] 学習済みパターン提案

---

## 実装順序

```
Week 1: EPIC-2 (CVE連携)
  TSK-CVE-001 → TSK-CVE-002 → TSK-CVE-003 → TSK-CVE-004
  TSK-CVE-005 (並行)
  TSK-CVE-006 → TSK-CVE-007 → TSK-CVE-008

Week 2-3: EPIC-3 (ルール)
  TSK-RULE-001 → TSK-RULE-002
  TSK-RULE-003, TSK-RULE-004 (並行)
  TSK-RULE-005, TSK-RULE-006 (並行)
  TSK-RULE-007 → TSK-RULE-008 → TSK-RULE-009 → TSK-RULE-010

Week 4: EPIC-4 (自動修正)
  TSK-FIX-001 → TSK-FIX-002 → TSK-FIX-003
  TSK-FIX-004 (並行) → TSK-FIX-005
  TSK-FIX-006 → TSK-FIX-007 → TSK-FIX-008
```

---

## 承認

- [x] タスク分解の粒度適切性
- [x] 依存関係の正確性
- [x] 工数見積もりの妥当性
- [x] 受け入れ基準の明確性
- [x] ユーザー承認 (2026-01-08)
