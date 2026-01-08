# MUSUBIX Security v2.1.0 要件定義書

**ドキュメントID**: REQ-SECURITY-2.1.0  
**バージョン**: 1.0.0  
**作成日**: 2026-01-08  
**ステータス**: Draft  
**優先度**: P0（必須）

---

## 1. 概要

### 1.1 目的

`@nahisaho/musubix-security` パッケージを Enterprise Ready レベルに強化し、以下の機能を実装する：

1. **テイント分析の高度化**: インタープロシージャル解析、データフロー追跡
2. **CVEデータベース連携**: NVD API統合によるリアルタイム脆弱性情報
3. **OWASP Top 10 / CWE Top 25 完全準拠**: 業界標準ルールセットの実装
4. **自動修正提案（Neuro-Symbolic）**: LLM生成 → Z3形式検証 → 安全な修正適用

### 1.2 スコープ

| 対象 | 説明 |
|------|------|
| **パッケージ** | `@nahisaho/musubix-security` |
| **対象言語** | TypeScript, JavaScript |
| **統合先** | VS Code Extension, MCP Server, CLI |
| **目標バージョン** | v2.1.0 |

### 1.3 前提条件

- MUSUBIX v2.0.x が正常にインストールされていること
- Node.js >= 20.0.0
- `@nahisaho/musubix-formal-verify` (Z3統合) が利用可能であること

### 1.4 参考事例

| ツール | アプローチ | MUSUBIXでの対応 |
|--------|----------|-----------------|
| Snyk DeepCode AI | LLM修正 + ルール再検証 | Z3形式検証で強化 |
| Semgrep | パターンベース検出 | YATA知識グラフ統合 |
| GitHub CodeQL | データフロー解析 | DFGパッケージ連携 |
| NVD/CVE | 脆弱性データベース | NVD API統合 |

---

## 2. 機能要件

### 2.1 テイント分析の高度化（REQ-SEC-TAINT）

#### REQ-SEC-TAINT-001: インタープロシージャルテイント解析

**パターン**: Event-driven  
**優先度**: P0

> WHEN a source file is analyzed,  
> THE TaintAnalyzer SHALL trace tainted data across function calls, module boundaries, and async operations.

**受け入れ基準**:
- [ ] 関数呼び出しを跨いだテイントフローを追跡できる
- [ ] モジュール境界（import/export）を跨いだ追跡ができる
- [ ] async/await、Promise チェーンを追跡できる
- [ ] コールグラフを構築し、テイント伝播を可視化できる

#### REQ-SEC-TAINT-002: テイントソース・シンク定義

**パターン**: Ubiquitous  
**優先度**: P0

> THE TaintAnalyzer SHALL support configurable taint sources and sinks based on OWASP and CWE categories.

**テイントソース（Sources）**:
| カテゴリ | 例 |
|---------|-----|
| HTTP入力 | `req.body`, `req.query`, `req.params`, `req.headers` |
| ユーザー入力 | `document.getElementById().value`, `prompt()` |
| 環境変数 | `process.env.*` (設定可能) |
| ファイル入力 | `fs.readFile()`, `fs.readFileSync()` |
| データベース結果 | `db.query()` 結果 |
| 外部API | `fetch()`, `axios.get()` レスポンス |

**テイントシンク（Sinks）**:
| カテゴリ | CWE | 例 |
|---------|-----|-----|
| SQLクエリ | CWE-89 | `db.query(sql)`, `sequelize.query()` |
| コマンド実行 | CWE-78 | `exec()`, `spawn()`, `execSync()` |
| HTML出力 | CWE-79 | `innerHTML`, `document.write()` |
| ファイルパス | CWE-22 | `fs.readFile(path)`, `path.join()` |
| コード実行 | CWE-94 | `eval()`, `new Function()` |
| リダイレクト | CWE-601 | `res.redirect(url)` |

#### REQ-SEC-TAINT-003: サニタイザー認識

**パターン**: State-driven  
**優先度**: P1

> WHILE tracing taint flow, THE TaintAnalyzer SHALL recognize sanitizers and mark data as clean.

**認識するサニタイザー**:
| カテゴリ | サニタイザー |
|---------|-------------|
| SQL | パラメータ化クエリ、`escape()`, `sqlstring.escape()` |
| HTML | `DOMPurify.sanitize()`, `escapeHtml()`, `he.encode()` |
| URL | `encodeURIComponent()`, `encodeURI()` |
| パス | `path.normalize()` + 検証 |

#### REQ-SEC-TAINT-004: DFGパッケージ統合

**パターン**: Event-driven  
**優先度**: P0

> WHEN performing taint analysis,  
> THE TaintAnalyzer SHALL utilize `@nahisaho/musubix-dfg` for data flow graph construction.

**受け入れ基準**:
- [ ] DFGパッケージからデータフローグラフを取得
- [ ] CFGと統合してパス感度解析を実行
- [ ] YATA知識グラフにテイントパスを保存

---

### 2.2 CVEデータベース連携（REQ-SEC-CVE）

#### REQ-SEC-CVE-001: NVD API統合

**パターン**: Ubiquitous  
**優先度**: P0

> THE CVEDatabase SHALL integrate with NIST NVD API 2.0 to fetch vulnerability information.

**API仕様**:
- エンドポイント: `https://services.nvd.nist.gov/rest/json/cves/2.0`
- 認証: API Key（オプション、レートリミット緩和）
- レートリミット: 5 requests/30 seconds (API Key なし)

**受け入れ基準**:
- [ ] CVE IDによる脆弱性情報取得
- [ ] CPE（Common Platform Enumeration）による検索
- [ ] キーワード検索
- [ ] CVSS v3.x スコア取得

#### REQ-SEC-CVE-002: ローカルキャッシュ

**パターン**: Ubiquitous  
**優先度**: P0

> THE CVEDatabase SHALL maintain a local SQLite cache to reduce API calls and enable offline operation.

**キャッシュ仕様**:
| 項目 | 値 |
|------|-----|
| **ストレージ** | SQLite (`~/.musubix/cve-cache.db`) |
| **TTL** | 24時間（設定可能） |
| **サイズ上限** | 500MB（設定可能） |
| **更新戦略** | LRU + 差分更新 |

#### REQ-SEC-CVE-003: 依存関係脆弱性マッチング

**パターン**: Event-driven  
**優先度**: P0

> WHEN scanning dependencies,  
> THE DependencyAuditor SHALL match package versions against NVD CVE data and report affected packages.

**受け入れ基準**:
- [ ] package.json / package-lock.json から依存関係を抽出
- [ ] npm パッケージ名 → CPE マッピング
- [ ] バージョン範囲マッチング（semver）
- [ ] 影響を受けるバージョンの特定
- [ ] CVSS スコアに基づく重要度分類

#### REQ-SEC-CVE-004: CVEアラート通知

**パターン**: Event-driven  
**優先度**: P1

> WHEN a new CVE affecting project dependencies is published,  
> THE CVEDatabase SHALL notify users via configured channels.

**通知チャネル**:
- VS Code 通知
- CLI 警告出力
- レポートへの追記

---

### 2.3 OWASP Top 10 / CWE Top 25 ルール（REQ-SEC-RULES）

#### REQ-SEC-RULES-001: OWASP Top 10 (2021) 完全対応

**パターン**: Ubiquitous  
**優先度**: P0

> THE RuleEngine SHALL implement detection rules for all OWASP Top 10 (2021) vulnerability categories.

| Rank | Category | CWE | 実装状態 |
|------|----------|-----|---------|
| A01 | Broken Access Control | CWE-200, CWE-284 | 🆕 新規 |
| A02 | Cryptographic Failures | CWE-259, CWE-327, CWE-331 | 🆕 新規 |
| A03 | Injection | CWE-79, CWE-89, CWE-78 | ✅ 既存強化 |
| A04 | Insecure Design | CWE-209, CWE-256 | 🆕 新規 |
| A05 | Security Misconfiguration | CWE-16 | 🆕 新規 |
| A06 | Vulnerable Components | CWE-1104 | ✅ 既存強化 |
| A07 | Identification Failures | CWE-287, CWE-384 | 🆕 新規 |
| A08 | Data Integrity Failures | CWE-502 | 🆕 新規 |
| A09 | Logging Failures | CWE-778 | 🆕 新規 |
| A10 | SSRF | CWE-918 | 🆕 新規 |

#### REQ-SEC-RULES-002: CWE Top 25 (2023) 完全対応

**パターン**: Ubiquitous  
**優先度**: P0

> THE RuleEngine SHALL implement detection rules for all CWE Top 25 (2023) weaknesses.

| Rank | CWE ID | Name | カテゴリ |
|------|--------|------|---------|
| 1 | CWE-787 | Out-of-bounds Write | Memory |
| 2 | CWE-79 | XSS | Injection |
| 3 | CWE-89 | SQL Injection | Injection |
| 4 | CWE-416 | Use After Free | Memory |
| 5 | CWE-78 | OS Command Injection | Injection |
| 6 | CWE-20 | Improper Input Validation | Input |
| 7 | CWE-125 | Out-of-bounds Read | Memory |
| 8 | CWE-22 | Path Traversal | File |
| 9 | CWE-352 | CSRF | Web |
| 10 | CWE-434 | Unrestricted Upload | File |
| 11 | CWE-862 | Missing Authorization | AuthZ |
| 12 | CWE-476 | NULL Pointer Dereference | Memory |
| 13 | CWE-287 | Improper Authentication | AuthN |
| 14 | CWE-190 | Integer Overflow | Numeric |
| 15 | CWE-502 | Deserialization | Data |
| 16 | CWE-77 | Command Injection | Injection |
| 17 | CWE-119 | Buffer Overflow | Memory |
| 18 | CWE-798 | Hardcoded Credentials | Secrets |
| 19 | CWE-918 | SSRF | Network |
| 20 | CWE-306 | Missing Authentication | AuthN |
| 21 | CWE-362 | Race Condition | Concurrency |
| 22 | CWE-269 | Improper Privilege | AuthZ |
| 23 | CWE-94 | Code Injection | Injection |
| 24 | CWE-863 | Incorrect Authorization | AuthZ |
| 25 | CWE-276 | Incorrect Permissions | File |

#### REQ-SEC-RULES-003: ルール定義形式

**パターン**: Ubiquitous  
**優先度**: P0

> THE RuleEngine SHALL support YAML-based rule definitions with AST pattern matching.

**ルール定義スキーマ**:
```yaml
# rules/owasp/A03-injection.yaml
rules:
  - id: sql-injection-template-literal
    name: SQL Injection via Template Literal
    severity: critical
    cwe: CWE-89
    owasp: A03
    message: |
      Possible SQL injection. User input is directly concatenated into SQL query.
    pattern:
      type: CallExpression
      callee:
        object: db
        property: query
      arguments:
        - type: TemplateLiteral
          hasTaintedExpression: true
    fix:
      type: parameterize
      template: |
        db.query($SQL, [$PARAMS])
    references:
      - https://owasp.org/Top10/A03_2021-Injection/
      - https://cwe.mitre.org/data/definitions/89.html
```

#### REQ-SEC-RULES-004: カスタムルールサポート

**パターン**: Optional  
**優先度**: P1

> IF a user defines custom rules in `.musubix/security-rules.yaml`,  
> THEN THE RuleEngine SHALL load and apply those rules alongside built-in rules.

---

### 2.4 自動修正提案（REQ-SEC-FIX）

#### REQ-SEC-FIX-001: LLM修正生成

**パターン**: Event-driven  
**優先度**: P0

> WHEN a vulnerability is detected,  
> THE FixGenerator SHALL generate fix candidates using available LLM (VS Code LM API / Ollama / API).

**LLMプロバイダー優先順位**:
1. VS Code Language Model API (GitHub Copilot)
2. Ollama (ローカルLLM)
3. OpenAI API (設定時)
4. パターンベースフォールバック

**プロンプト構造**:
```
You are a security expert. Generate a secure fix for:

## Vulnerability
- Type: {type}
- CWE: {cweId}
- Location: {file}:{line}
- Description: {description}

## Vulnerable Code
```{language}
{vulnerableCode}
```

## Requirements
- Fix MUST eliminate the vulnerability
- Fix MUST preserve original functionality
- Fix SHOULD follow security best practices
- Fix MUST be minimal and targeted

## Expected Output
Provide the fixed code with explanation.
```

#### REQ-SEC-FIX-002: Z3形式検証

**パターン**: Event-driven  
**優先度**: P0

> WHEN a fix candidate is generated,  
> THE FixVerifier SHALL verify the fix using Z3 SMT solver to ensure:
> 1. The vulnerability is eliminated
> 2. No new vulnerabilities are introduced
> 3. Semantic equivalence is preserved (where applicable)

**検証プロセス**:
```
Fix Candidate → AST解析 → SMT式生成 → Z3検証 → 結果
                    ↓
              テイント再解析
                    ↓
              脆弱性再スキャン
```

**受け入れ基準**:
- [ ] 修正後コードでテイントパスが遮断されることを検証
- [ ] 入力制約が適切に実装されていることを検証
- [ ] 出力エンコーディングが適用されていることを検証
- [ ] 検証失敗時は修正を棄却し、理由を報告

#### REQ-SEC-FIX-003: 修正信頼度スコア

**パターン**: Ubiquitous  
**優先度**: P0

> THE FixGenerator SHALL assign a confidence score to each fix candidate based on:
> - LLM confidence
> - Z3 verification result
> - Pattern library match
> - Historical success rate

**スコア計算**:
```
confidence = (
  llm_confidence * 0.3 +
  z3_verified * 0.4 +
  pattern_match * 0.2 +
  historical_success * 0.1
)
```

| スコア | ラベル | アクション |
|--------|--------|----------|
| >= 0.9 | High | 自動適用可能 |
| 0.7-0.9 | Medium | ユーザー確認推奨 |
| 0.5-0.7 | Low | 手動レビュー必須 |
| < 0.5 | Unreliable | 棄却 |

#### REQ-SEC-FIX-004: 修正適用とロールバック

**パターン**: Event-driven  
**優先度**: P1

> WHEN a fix is applied,  
> THE FixApplier SHALL create a backup and support rollback if tests fail.

**受け入れ基準**:
- [ ] 修正前のコードをバックアップ
- [ ] git stashまたはファイルバックアップ
- [ ] 適用後にテスト実行（設定時）
- [ ] テスト失敗時は自動ロールバック

---

## 3. 非機能要件

### 3.1 パフォーマンス（REQ-SEC-PERF）

#### REQ-SEC-PERF-001: スキャン速度

**パターン**: Ubiquitous  
**優先度**: P0

> THE SecurityScanner SHALL scan 10,000 lines of code in under 10 seconds on standard hardware.

| 規模 | 目標時間 |
|------|----------|
| 1,000 LOC | < 1秒 |
| 10,000 LOC | < 10秒 |
| 100,000 LOC | < 2分 |

#### REQ-SEC-PERF-002: メモリ使用量

**パターン**: Ubiquitous  
**優先度**: P1

> THE SecurityScanner SHALL use no more than 1GB of memory for projects up to 100,000 LOC.

### 3.2 信頼性（REQ-SEC-REL）

#### REQ-SEC-REL-001: 偽陽性率

**パターン**: Ubiquitous  
**優先度**: P0

> THE SecurityScanner SHALL maintain a false positive rate below 5% for critical/high severity findings.

#### REQ-SEC-REL-002: 検出率

**パターン**: Ubiquitous  
**優先度**: P0

> THE SecurityScanner SHALL detect at least 90% of known vulnerabilities in benchmark test suites.

---

## 4. インターフェース

### 4.1 CLI

```bash
# 基本スキャン
npx musubix security scan ./src

# OWASP/CWE準拠レポート
npx musubix security scan ./src --compliance owasp-top-10
npx musubix security scan ./src --compliance cwe-top-25

# CVEチェック
npx musubix security cve-check
npx musubix security cve-check --package lodash@4.17.20

# 自動修正
npx musubix security fix ./src --auto
npx musubix security fix ./src --interactive

# レポート生成
npx musubix security report --format sarif --output report.sarif
```

### 4.2 MCP Tools

| ツール名 | 説明 |
|---------|------|
| `security_scan` | ディレクトリ/ファイルのセキュリティスキャン |
| `security_taint_analyze` | テイント解析の実行 |
| `security_cve_check` | CVE脆弱性チェック |
| `security_generate_fix` | 脆弱性に対する修正生成 |
| `security_verify_fix` | 修正のZ3検証 |
| `security_apply_fix` | 修正の適用 |

### 4.3 API

```typescript
import { 
  SecurityScanner,
  TaintAnalyzer,
  CVEDatabase,
  FixGenerator,
  FixVerifier
} from '@nahisaho/musubix-security';

// スキャン
const scanner = new SecurityScanner({
  rules: ['owasp-top-10', 'cwe-top-25'],
  severity: ['critical', 'high']
});
const result = await scanner.scan('./src');

// テイント解析
const taintAnalyzer = new TaintAnalyzer({ interprocedural: true });
const taintPaths = await taintAnalyzer.analyze('./src');

// CVEチェック
const cveDb = new CVEDatabase({ apiKey: process.env.NVD_API_KEY });
await cveDb.sync();
const cves = await cveDb.checkDependencies('./package.json');

// 修正生成と検証
const fixGen = new FixGenerator();
const fixes = await fixGen.generate(result.vulnerabilities[0]);

const verifier = new FixVerifier();
for (const fix of fixes) {
  const verified = await verifier.verify(fix);
  if (verified.passed) {
    await fix.apply();
  }
}
```

---

## 5. テスト要件

### 5.1 ユニットテスト

| モジュール | 目標カバレッジ |
|-----------|---------------|
| TaintAnalyzer | 90% |
| CVEDatabase | 85% |
| RuleEngine | 90% |
| FixGenerator | 80% |
| FixVerifier | 90% |

### 5.2 統合テスト

- [ ] OWASP Benchmark との互換性テスト
- [ ] NIST SARD テストスイートとの互換性テスト
- [ ] 実プロジェクトでのスキャンテスト

### 5.3 ベンチマークテスト

- [ ] スキャン速度ベンチマーク
- [ ] メモリ使用量ベンチマーク
- [ ] 検出率ベンチマーク

---

## 6. 依存関係

### 6.1 内部依存

| パッケージ | 用途 |
|-----------|------|
| `@nahisaho/musubix-core` | 基盤機能 |
| `@nahisaho/musubix-dfg` | データフローグラフ |
| `@nahisaho/musubix-formal-verify` | Z3形式検証 |
| `@nahisaho/yata-local` | 知識グラフストレージ |

### 6.2 外部依存

| パッケージ | バージョン | 用途 |
|-----------|----------|------|
| `ts-morph` | ^24.0.0 | AST解析 |
| `better-sqlite3` | ^11.0.0 | CVEキャッシュ |
| `semver` | ^7.6.0 | バージョン比較 |

---

## 7. トレーサビリティ

### 7.1 上位要件へのマッピング

| 本要件 | 上位要件 | 根拠 |
|--------|---------|------|
| REQ-SEC-TAINT-* | REQ-INT-001 (Neuro-Symbolic統合) | DFG/CFGによる記号的解析 |
| REQ-SEC-CVE-* | REQ-LEARN-001 (継続学習) | 脆弱性知識の更新 |
| REQ-SEC-FIX-* | REQ-INT-002 (信頼度評価) | LLM+Z3のNeuro-Symbolic |

### 7.2 成果物へのマッピング

| 要件 | 設計 | 実装 | テスト |
|------|------|------|--------|
| REQ-SEC-TAINT-001 | DES-SEC-TAINT-001 | TBD | TBD |
| REQ-SEC-CVE-001 | DES-SEC-CVE-001 | TBD | TBD |
| REQ-SEC-RULES-001 | DES-SEC-RULES-001 | TBD | TBD |
| REQ-SEC-FIX-001 | DES-SEC-FIX-001 | TBD | TBD |

---

## 8. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Assistant | 2026-01-08 | ✓ |
| レビュアー | | | |
| 承認者 | | | |

---

## 付録

### A. 用語集

| 用語 | 定義 |
|------|------|
| **テイント解析** | 信頼されないソースから危険なシンクへのデータフロー追跡 |
| **CVE** | Common Vulnerabilities and Exposures - 脆弱性の標準識別子 |
| **NVD** | National Vulnerability Database - NISTが管理する脆弱性DB |
| **CVSS** | Common Vulnerability Scoring System - 脆弱性の重大度スコア |
| **CPE** | Common Platform Enumeration - ソフトウェアの標準識別子 |
| **OWASP** | Open Web Application Security Project |
| **CWE** | Common Weakness Enumeration - 脆弱性の分類体系 |

### B. 参考文献

1. OWASP Top 10 (2021): https://owasp.org/Top10/
2. CWE Top 25 (2023): https://cwe.mitre.org/top25/
3. NVD API 2.0: https://nvd.nist.gov/developers/vulnerabilities
4. SARIF: https://sarifweb.azurewebsites.net/

---

**© 2026 MUSUBIX Project**
