# 要件定義書: MUSUBIX Security Package

**文書ID**: REQ-SEC-001  
**バージョン**: 0.2.0 (Revised)  
**作成日**: 2026-01-06  
**更新日**: 2026-01-06  
**ステータス**: ✅ レビュー完了

---

## 1. 概要

### 1.1 目的

MUSUBIXシステムにセキュリティ特化機能を追加し、コードの脆弱性検出・自動修正・コンプライアンス検証を提供する。

### 1.2 スコープ

| 対象 | 説明 |
|------|------|
| **パッケージ名** | `@nahisaho/musubix-security` |
| **対象バージョン** | v1.8.0 |
| **対象言語** | TypeScript/JavaScript |
| **拡張予定** | Python, Java, Go |

### 1.3 用語定義

| 用語 | 定義 |
|------|------|
| **テイント分析** | 汚染データ（ユーザー入力等）の伝播を追跡する静的解析手法 |
| **脆弱性** | セキュリティ上の弱点。CWE/CVEで分類 |
| **OWASP** | Open Web Application Security Project。Webセキュリティ標準 |
| **CWE** | Common Weakness Enumeration。脆弱性の分類体系 |
| **CVSS** | Common Vulnerability Scoring System。脆弱性の重大度スコア |
| **LM API** | VS Code Language Model API。LLMアクセス用API |

---

## 2. 機能要件

### 2.1 脆弱性スキャン機能 (REQ-SEC-SCAN)

#### REQ-SEC-SCAN-001: 基本スキャン
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-SCAN-001

```
THE SecurityScanner SHALL detect security vulnerabilities in TypeScript and JavaScript source code.
```

#### REQ-SEC-SCAN-002: OWASP Top 10対応
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-SCAN-002

```
THE SecurityScanner SHALL detect all vulnerability types defined in OWASP Top 10 (2021).
```

#### REQ-SEC-SCAN-003: CWE Top 25対応
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-SCAN-003

```
THE SecurityScanner SHALL detect vulnerability types defined in CWE Top 25 (2024) with at least 80% coverage.
```

#### REQ-SEC-SCAN-004: 重大度フィルタリング
**パターン**: Optional  
**優先度**: P1  
**トレース**: DES-SEC-SCAN-004

```
IF the user specifies severity levels, THEN THE SecurityScanner SHALL report only vulnerabilities matching the specified severity levels (critical, high, medium, low).
```

#### REQ-SEC-SCAN-005: 増分スキャン
**パターン**: Event-driven  
**優先度**: P1  
**トレース**: DES-SEC-SCAN-005

```
WHEN a file is modified, THE SecurityScanner SHALL perform incremental scanning on only the changed files within 5 seconds.
```

#### REQ-SEC-SCAN-006: 偽陽性率
**パターン**: Unwanted  
**優先度**: P0  
**トレース**: DES-SEC-SCAN-006

```
THE SecurityScanner SHALL NOT produce false positive results exceeding 5% of total reported vulnerabilities.
```

---

### 2.2 テイント分析機能 (REQ-SEC-TAINT)

#### REQ-SEC-TAINT-001: ソース検出
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-TAINT-001

```
THE TaintAnalyzer SHALL identify taint sources including user input (req.body, req.query, req.params), environment variables, and file reads.
```

#### REQ-SEC-TAINT-002: シンク検出
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-TAINT-002

```
THE TaintAnalyzer SHALL identify taint sinks including SQL queries, eval(), innerHTML, file writes, and system commands.
```

#### REQ-SEC-TAINT-003: パス追跡
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-TAINT-003

```
THE TaintAnalyzer SHALL trace data flow paths from sources to sinks across function boundaries.
```

#### REQ-SEC-TAINT-004: サニタイザー認識
**パターン**: State-driven  
**優先度**: P1  
**トレース**: DES-SEC-TAINT-004

```
WHILE tainted data passes through a recognized sanitizer function, THE TaintAnalyzer SHALL mark the data as clean for the corresponding vulnerability type.
```

---

### 2.3 自動修正機能 (REQ-SEC-FIX)

#### REQ-SEC-FIX-001: 修正生成
**パターン**: Event-driven  
**優先度**: P0  
**トレース**: DES-SEC-FIX-001

```
WHEN a vulnerability is detected, THE FixGenerator SHALL generate at least one fix candidate using VS Code Language Model API.
```

#### REQ-SEC-FIX-002: 形式検証
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-FIX-002

```
THE FixVerifier SHALL verify that generated fixes eliminate the original vulnerability using Z3 formal verification.
```

#### REQ-SEC-FIX-003: 新規脆弱性チェック
**パターン**: Unwanted  
**優先度**: P0  
**トレース**: DES-SEC-FIX-003

```
THE FixVerifier SHALL NOT approve fixes that introduce new security vulnerabilities.
```

#### REQ-SEC-FIX-004: 機能保持
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-FIX-004

```
THE FixVerifier SHALL verify that generated fixes preserve the original code functionality through semantic analysis.
```

#### REQ-SEC-FIX-005: 複数候補
**パターン**: Optional  
**優先度**: P1  
**トレース**: DES-SEC-FIX-005

```
IF multiple fix approaches exist, THEN THE FixGenerator SHALL provide up to 3 fix candidates ranked by confidence score.
```

#### REQ-SEC-FIX-006: LLM非依存フォールバック
**パターン**: State-driven  
**優先度**: P1  
**トレース**: DES-SEC-FIX-006

```
WHILE VS Code Language Model API is unavailable, THE FixGenerator SHALL provide template-based fixes from the pattern library.
```

---

### 2.4 シークレット検出機能 (REQ-SEC-SECRET)

#### REQ-SEC-SECRET-001: 基本検出
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-SECRET-001

```
THE SecretsDetector SHALL detect hardcoded secrets including API keys, tokens, passwords, and private keys in source code.
```

#### REQ-SEC-SECRET-002: エントロピー分析
**パターン**: Ubiquitous  
**優先度**: P1  
**トレース**: DES-SEC-SECRET-002

```
THE SecretsDetector SHALL use entropy analysis with threshold 4.5 to identify potential secrets without known patterns.
```

#### REQ-SEC-SECRET-003: 既知パターン
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-SECRET-003

```
THE SecretsDetector SHALL detect secrets matching known patterns for GitHub tokens, Azure keys, Google API keys, JWT secrets, and database connection strings.
```

---

### 2.5 依存関係監査機能 (REQ-SEC-DEPS)

#### REQ-SEC-DEPS-001: 脆弱性チェック
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-DEPS-001

```
THE DependencyAuditor SHALL check all npm dependencies against known vulnerability databases (NVD, GitHub Advisory).
```

#### REQ-SEC-DEPS-002: 推移的依存関係
**パターン**: Ubiquitous  
**優先度**: P1  
**トレース**: DES-SEC-DEPS-002

```
THE DependencyAuditor SHALL analyze transitive dependencies up to depth 10.
```

#### REQ-SEC-DEPS-003: アップグレード提案
**パターン**: Event-driven  
**優先度**: P1  
**トレース**: DES-SEC-DEPS-003

```
WHEN a vulnerable dependency is detected, THE DependencyAuditor SHALL suggest the minimum safe version for upgrade.
```

---

### 2.6 コンプライアンス機能 (REQ-SEC-COMP)

#### REQ-SEC-COMP-001: レポート生成
**パターン**: Event-driven  
**優先度**: P1  
**トレース**: DES-SEC-COMP-001

```
WHEN a compliance check is requested, THE ComplianceChecker SHALL generate a report in HTML, JSON, or SARIF format.
```

#### REQ-SEC-COMP-002: OWASP準拠
**パターン**: Ubiquitous  
**優先度**: P1  
**トレース**: DES-SEC-COMP-002

```
THE ComplianceChecker SHALL assess code against OWASP Application Security Verification Standard (ASVS).
```

---

### 2.7 YATA統合 (REQ-SEC-YATA)

#### REQ-SEC-YATA-001: 脆弱性知識グラフ
**パターン**: Ubiquitous  
**優先度**: P1  
**トレース**: DES-SEC-YATA-001

```
THE SecurityPackage SHALL store detected vulnerabilities and fixes in YATA knowledge graph for traceability.
```

#### REQ-SEC-YATA-002: パターン学習
**パターン**: Event-driven  
**優先度**: P2  
**トレース**: DES-SEC-YATA-002

```
WHEN a fix is successfully verified and applied, THE SecurityPackage SHALL store the fix pattern in the pattern library for future reference.
```

---

### 2.8 MCP統合 (REQ-SEC-MCP)

#### REQ-SEC-MCP-001: スキャンツール
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-MCP-001

```
THE SecurityPackage SHALL expose security_scan tool through MCP protocol for AI agent integration.
```

#### REQ-SEC-MCP-002: 修正ツール
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-MCP-002

```
THE SecurityPackage SHALL expose security_fix tool through MCP protocol for automated vulnerability remediation.
```

---

## 3. 非機能要件

### 3.1 パフォーマンス (REQ-SEC-PERF)

#### REQ-SEC-PERF-001: スキャン速度
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-PERF-001

```
THE SecurityScanner SHALL scan code at a rate of at least 1000 lines per second on reference hardware (4-core CPU @ 2.5GHz, 8GB RAM).
```

#### REQ-SEC-PERF-002: メモリ使用量
**パターン**: Unwanted  
**優先度**: P1  
**トレース**: DES-SEC-PERF-002

```
THE SecurityPackage SHALL NOT consume more than 512MB of memory during normal operation.
```

### 3.2 信頼性 (REQ-SEC-REL)

#### REQ-SEC-REL-001: 検出率
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-REL-001

```
THE SecurityScanner SHALL achieve a true positive rate of at least 90% for OWASP Top 10 vulnerabilities.
```

#### REQ-SEC-REL-002: 修正成功率
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-REL-002

```
THE FixPipeline SHALL achieve a verified fix success rate of at least 80%.
```

### 3.3 可用性 (REQ-SEC-AVAIL)

#### REQ-SEC-AVAIL-001: オフライン動作
**パターン**: State-driven  
**優先度**: P1  
**トレース**: DES-SEC-AVAIL-001

```
WHILE network connectivity is unavailable, THE SecurityScanner SHALL operate using local rule database and template-based fixes.
```

---

### 3.4 CLI要件 (REQ-SEC-CLI) - 憲法II条準拠

#### REQ-SEC-CLI-001: 基本CLIコマンド
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-CLI-001

```
THE SecurityPackage SHALL provide CLI commands for scanning, fixing, and auditing operations via 'npx musubix security' command.
```

#### REQ-SEC-CLI-002: ヘルプ・ドキュメント
**パターン**: Ubiquitous  
**優先度**: P0  
**トレース**: DES-SEC-CLI-002

```
THE SecurityPackage CLI SHALL provide --help flag with usage examples for all commands.
```

#### REQ-SEC-CLI-003: 終了コード
**パターン**: Ubiquitous  
**優先度**: P1  
**トレース**: DES-SEC-CLI-003

```
THE SecurityPackage CLI SHALL return exit code 0 for success, 1 for vulnerabilities found, and 2 for errors.
```

---

### 3.5 エラーハンドリング (REQ-SEC-ERR)

#### REQ-SEC-ERR-001: グレースフルデグラデーション
**パターン**: State-driven  
**優先度**: P0  
**トレース**: DES-SEC-ERR-001

```
WHILE an external service (LLM API, NVD) is unavailable, THE SecurityPackage SHALL continue operation with degraded functionality and notify the user.
```

#### REQ-SEC-ERR-002: エラーメッセージ
**パターン**: Ubiquitous  
**優先度**: P1  
**トレース**: DES-SEC-ERR-002

```
THE SecurityPackage SHALL provide actionable error messages including error code, description, and suggested resolution.
```

---

## 4. 制約条件

### 4.1 技術的制約

| 制約 | 詳細 |
|------|------|
| **言語** | TypeScript 5.x |
| **ランタイム** | Node.js >= 20.0.0 |
| **LLM API** | VS Code Language Model API (vscode.lm) |
| **形式検証** | Z3 SMTソルバ（Wasm優先） |
| **知識グラフ** | YATA (SQLite/分散) |

### 4.2 9条憲法準拠

| 条項 | 適用 |
|------|------|
| I. Library-First | ✅ 独立パッケージとして実装 |
| II. CLI Interface | ✅ CLIコマンド提供 |
| III. Test-First | ✅ TDDで開発 |
| IV. EARS Format | ✅ 本文書で定義 |
| V. Traceability | ✅ 要件→設計→コード追跡 |
| VI. Project Memory | ✅ steering/参照 |
| VII. Design Patterns | ✅ 設計書で文書化 |
| VIII. Decision Records | ✅ ADR作成 |
| IX. Quality Gates | ✅ レビュープロセス |

---

## 5. 受け入れ基準

### 5.1 機能テスト

| テスト | 基準 |
|--------|------|
| OWASP Top 10検出 | 全10カテゴリで1件以上の検出 |
| CWE Top 25検出 | 20件以上（80%）の検出 |
| テイント分析 | ソース→シンク追跡成功率 >95% |
| 自動修正 | 検証済み修正成功率 >80% |
| シークレット検出 | 既知パターン検出率 >99% |

### 5.2 品質メトリクス

| メトリクス | 目標値 |
|-----------|--------|
| テストカバレッジ | >90% |
| 偽陽性率 | <5% |
| 偽陰性率 | <10% |
| ドキュメント完成度 | 100% |

---

## 6. トレーサビリティマトリクス

### 6.1 機能要件

| 要件ID | 設計ID | テストID | 実装ファイル |
|--------|--------|----------|--------------|
| REQ-SEC-SCAN-001 | DES-SEC-SCAN-001 | TST-SEC-SCAN-001 | VulnerabilityScanner.ts |
| REQ-SEC-SCAN-002 | DES-SEC-SCAN-002 | TST-SEC-SCAN-002 | rules/owasp-top-10.yaml |
| REQ-SEC-SCAN-003 | DES-SEC-SCAN-003 | TST-SEC-SCAN-003 | rules/cwe-top-25.yaml |
| REQ-SEC-SCAN-004 | DES-SEC-SCAN-004 | TST-SEC-SCAN-004 | VulnerabilityScanner.ts |
| REQ-SEC-SCAN-005 | DES-SEC-SCAN-005 | TST-SEC-SCAN-005 | IncrementalScanner.ts |
| REQ-SEC-SCAN-006 | DES-SEC-SCAN-006 | TST-SEC-SCAN-006 | VulnerabilityScanner.ts |
| REQ-SEC-TAINT-001 | DES-SEC-TAINT-001 | TST-SEC-TAINT-001 | TaintAnalyzer.ts |
| REQ-SEC-TAINT-002 | DES-SEC-TAINT-002 | TST-SEC-TAINT-002 | TaintAnalyzer.ts |
| REQ-SEC-TAINT-003 | DES-SEC-TAINT-003 | TST-SEC-TAINT-003 | TaintAnalyzer.ts |
| REQ-SEC-TAINT-004 | DES-SEC-TAINT-004 | TST-SEC-TAINT-004 | SanitizerRegistry.ts |
| REQ-SEC-FIX-001 | DES-SEC-FIX-001 | TST-SEC-FIX-001 | FixGenerator.ts |
| REQ-SEC-FIX-002 | DES-SEC-FIX-002 | TST-SEC-FIX-002 | FixVerifier.ts |
| REQ-SEC-FIX-003 | DES-SEC-FIX-003 | TST-SEC-FIX-003 | FixVerifier.ts |
| REQ-SEC-FIX-004 | DES-SEC-FIX-004 | TST-SEC-FIX-004 | SemanticAnalyzer.ts |
| REQ-SEC-FIX-005 | DES-SEC-FIX-005 | TST-SEC-FIX-005 | FixGenerator.ts |
| REQ-SEC-FIX-006 | DES-SEC-FIX-006 | TST-SEC-FIX-006 | TemplateFixProvider.ts |
| REQ-SEC-SECRET-001 | DES-SEC-SECRET-001 | TST-SEC-SECRET-001 | SecretsDetector.ts |
| REQ-SEC-SECRET-002 | DES-SEC-SECRET-002 | TST-SEC-SECRET-002 | EntropyAnalyzer.ts |
| REQ-SEC-SECRET-003 | DES-SEC-SECRET-003 | TST-SEC-SECRET-003 | PatternMatcher.ts |
| REQ-SEC-DEPS-001 | DES-SEC-DEPS-001 | TST-SEC-DEPS-001 | DependencyAuditor.ts |
| REQ-SEC-DEPS-002 | DES-SEC-DEPS-002 | TST-SEC-DEPS-002 | TransitiveDependencyResolver.ts |
| REQ-SEC-DEPS-003 | DES-SEC-DEPS-003 | TST-SEC-DEPS-003 | UpgradeAdvisor.ts |
| REQ-SEC-COMP-001 | DES-SEC-COMP-001 | TST-SEC-COMP-001 | ReportGenerator.ts |
| REQ-SEC-COMP-002 | DES-SEC-COMP-002 | TST-SEC-COMP-002 | ASVSChecker.ts |
| REQ-SEC-YATA-001 | DES-SEC-YATA-001 | TST-SEC-YATA-001 | YataSecurityAdapter.ts |
| REQ-SEC-YATA-002 | DES-SEC-YATA-002 | TST-SEC-YATA-002 | FixPatternLearner.ts |
| REQ-SEC-MCP-001 | DES-SEC-MCP-001 | TST-SEC-MCP-001 | McpSecurityTools.ts |
| REQ-SEC-MCP-002 | DES-SEC-MCP-002 | TST-SEC-MCP-002 | McpSecurityTools.ts |

### 6.2 非機能要件・CLI・エラーハンドリング

| 要件ID | 設計ID | テストID | 実装ファイル |
|--------|--------|----------|--------------|
| REQ-SEC-PERF-001 | DES-SEC-PERF-001 | TST-SEC-PERF-001 | VulnerabilityScanner.ts |
| REQ-SEC-PERF-002 | DES-SEC-PERF-002 | TST-SEC-PERF-002 | MemoryManager.ts |
| REQ-SEC-REL-001 | DES-SEC-REL-001 | TST-SEC-REL-001 | VulnerabilityScanner.ts |
| REQ-SEC-REL-002 | DES-SEC-REL-002 | TST-SEC-REL-002 | FixPipeline.ts |
| REQ-SEC-AVAIL-001 | DES-SEC-AVAIL-001 | TST-SEC-AVAIL-001 | OfflineMode.ts |
| REQ-SEC-CLI-001 | DES-SEC-CLI-001 | TST-SEC-CLI-001 | cli/security.ts |
| REQ-SEC-CLI-002 | DES-SEC-CLI-002 | TST-SEC-CLI-002 | cli/security.ts |
| REQ-SEC-CLI-003 | DES-SEC-CLI-003 | TST-SEC-CLI-003 | cli/security.ts |
| REQ-SEC-ERR-001 | DES-SEC-ERR-001 | TST-SEC-ERR-001 | ErrorHandler.ts |
| REQ-SEC-ERR-002 | DES-SEC-ERR-002 | TST-SEC-ERR-002 | ErrorHandler.ts |

---

## 7. レビュー履歴

| バージョン | 日付 | レビュアー | ステータス | コメント |
|-----------|------|-----------|----------|---------|
| 0.1.0 | 2026-01-06 | - | 📝 レビュー待ち | 初版作成 |
| 0.2.0 | 2026-01-06 | AI Agent (Constitution Enforcer) | ✅ 合格 | TAINT-004パターン修正、CLI要件追加、エラーハンドリング要件追加、非機能要件トレースID追加 |

---

## 8. 承認

| 役割 | 名前 | 署名 | 日付 |
|------|------|------|------|
| 作成者 | AI Agent | ✅ | 2026-01-06 |
| レビュアー | AI Agent (Constitution Enforcer) | ✅ | 2026-01-06 |
| 承認者 | - | ⏳ | - |

---

**© 2026 MUSUBIX Project**
