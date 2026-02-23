# MUSUBIX セキュリティ分析パッケージ

**パッケージ名**: `@nahisaho/musubix-security`  
**バージョン**: 1.8.0  
**最終更新**: 2026-01-07

---

## 1. 概要

`@nahisaho/musubix-security` は、TypeScript/JavaScriptプロジェクトの包括的なセキュリティ分析を提供するパッケージです。OWASP Top 10およびCWE Top 25に基づく脆弱性検出、シークレット漏洩検出、テイント解析、依存関係監査を統合します。

### 1.1 主要機能

| 機能 | 説明 |
|------|------|
| **脆弱性スキャン** | SQLインジェクション、XSS、コマンドインジェクション等の検出 |
| **シークレット検出** | API キー、認証情報、秘密鍵のハードコード検出 |
| **テイント解析** | ユーザー入力から危険な関数へのデータフロー追跡 |
| **依存関係監査** | npm audit統合による脆弱な依存関係の検出 |
| **自動修正生成** | 検出された脆弱性に対する修正コードの提案 |
| **レポート生成** | JSON/Markdown/HTML/SARIF形式のレポート出力 |
| **自動修正・修復** | AutoFixer、パッチ生成、修正検証（Phase 5） |
| **セキュリティインテリジェンス** | 脅威フィード統合、MITRE ATT&CK対応（Phase 6） |
| **リスク分析** | CVSS計算、予測分析、異常検出（Phase 6） |

### 1.2 モジュール構成

```
packages/security/src/
├── analysis/            # 解析エンジン
│   ├── vulnerability-scanner.ts  # 脆弱性スキャナ
│   ├── secret-detector.ts        # シークレット検出
│   ├── taint-analyzer.ts         # テイント解析
│   └── dependency-auditor.ts     # 依存関係監査
├── services/            # サービス層
│   ├── security-service.ts       # 統合サービス
│   ├── fix-generator.ts          # 修正生成
│   ├── fix-verifier.ts           # 修正検証
│   └── report-generator.ts       # レポート生成
├── remediation/         # 自動修正（Phase 5）
│   ├── auto-fixer.ts             # 自動修正エンジン
│   ├── fix-validator.ts          # 修正検証
│   ├── patch-generator.ts        # パッチ生成
│   ├── remediation-planner.ts    # 修復計画
│   └── secure-code-transformer.ts # セキュアコード変換
├── intelligence/        # セキュリティインテリジェンス（Phase 6）
│   ├── threat-intelligence.ts    # 脅威インテリジェンス
│   ├── attack-pattern-matcher.ts # MITRE ATT&CK統合
│   ├── risk-scorer.ts            # リスクスコアリング
│   ├── security-analytics.ts     # セキュリティ分析
│   └── predictive-analyzer.ts    # 予測分析
├── infrastructure/      # インフラストラクチャ
│   ├── ast-parser.ts             # AST解析
│   ├── file-scanner.ts           # ファイルスキャン
│   ├── config-loader.ts          # 設定読み込み
│   └── cache.ts                  # キャッシュ
├── mcp/                 # MCPツール統合
│   ├── server.ts                 # MCPサーバー
│   └── tools.ts                  # MCPツール定義
├── cli/                 # CLIインターフェース
│   └── commands.ts               # CLIコマンド
├── types/               # 型定義
│   ├── vulnerability.ts          # 脆弱性型
│   ├── secret.ts                 # シークレット型
│   ├── taint.ts                  # テイント型
│   ├── fix.ts                    # 修正型
│   ├── dependency.ts             # 依存関係型
│   └── config.ts                 # 設定型
└── index.ts             # エントリポイント
```

---

## 2. 脆弱性スキャン

### 2.1 概要

ts-morphを使用したAST解析により、ソースコード内のセキュリティ脆弱性を静的に検出します。

### 2.2 VulnerabilityScanner

```typescript
import { VulnerabilityScanner } from '@nahisaho/musubix-security';

const scanner = new VulnerabilityScanner();

// 単一ファイルスキャン（Vulnerability[]を返す）
const vulnerabilities = scanner.scanFile('src/api.ts');

// ディレクトリスキャン（ScanResultを返す）
const result = await scanner.scanDirectory('./src');

console.log(result.vulnerabilities);  // 検出された脆弱性
console.log(result.scannedFiles);     // スキャンしたファイル数
console.log(result.summary);          // 重要度別サマリー
```

### 2.3 検出可能な脆弱性

| カテゴリ | CWE | 検出パターン | 重要度 |
|---------|-----|-------------|--------|
| **SQLインジェクション** | CWE-89 | 文字列連結/テンプレートリテラルによるクエリ構築 | Critical |
| **コマンドインジェクション** | CWE-78 | exec, execSync, spawn への動的入力 | Critical |
| **XSS** | CWE-79 | innerHTML, document.write への未サニタイズ出力 | High |
| **パストラバーサル** | CWE-22 | ユーザー入力を含むファイルパス操作 | High |
| **コードインジェクション** | CWE-94 | eval, new Function の使用 | Critical |
| **NoSQLインジェクション** | CWE-943 | MongoDB等への動的クエリ | High |
| **オープンリダイレクト** | CWE-601 | 未検証のリダイレクトURL | Medium |
| **XXE** | CWE-611 | XML外部エンティティ参照 | High |

### 2.4 Vulnerability型

```typescript
interface Vulnerability {
  id: string;                    // 一意のID (VULN-YYYYMMDD-NNN)
  ruleId: string;                // ルールID (sql-injection等)
  name: string;                  // 脆弱性名
  description: string;           // 説明
  severity: Severity;            // critical/high/medium/low/info
  location: SourceLocation;      // ファイル/行/列
  cweId?: string;                // CWE ID
  owaspCategory?: string;        // OWASP カテゴリ
  snippet?: string;              // コードスニペット
  remediation?: string;          // 修正ガイダンス
}

type Severity = 'critical' | 'high' | 'medium' | 'low' | 'info';
```

---

## 3. シークレット検出

### 3.1 概要

ソースコードやコンフィグファイル内にハードコードされた機密情報を検出します。

### 3.2 SecretDetector

```typescript
import { SecretDetector } from '@nahisaho/musubix-security';

const detector = new SecretDetector();

// コンテンツスキャン（Secret[]を返す）
const secrets = detector.scanContent(content, 'config.ts');

// ディレクトリスキャン（SecretScanResultを返す）
const result = await detector.scan('./src');

console.log(result.summary.total);    // 検出されたシークレット数
console.log(result.scannedFiles);     // スキャンしたファイル数
```

### 3.3 検出可能なシークレット

| タイプ | パターン | 重要度 |
|--------|---------|--------|
| **AWS Access Key** | `AKIA[0-9A-Z]{16}` | Critical |
| **AWS Secret Key** | 40文字のbase64文字列 | Critical |
| **GitHub Token** | `ghp_*`, `gho_*`, `ghu_*`, `ghs_*`, `ghr_*` | Critical |
| **Private Key** | PEM形式の秘密鍵 | Critical |
| **Database URL** | `postgres://`, `mongodb://`, `mysql://` | High |
| **JWT Secret** | JWT署名シークレット | High |
| **Stripe Key** | `sk_live_*`, `sk_test_*` | Critical/Low |
| **Slack Webhook** | `https://hooks.slack.com/services/...` | Medium |
| **Azure Connection** | Azure接続文字列 | Critical |

### 3.4 Secret型

```typescript
interface Secret {
  id: string;              // 一意のID (SEC-YYYYMMDD-NNN)
  type: SecretType;        // シークレットタイプ
  value: string;           // 検出された値
  masked: string;          // マスクされた値
  file: string;            // ファイルパス
  line: number;            // 行番号
  column: number;          // 列番号
  context: string;         // コンテキスト情報
  confidence: number;      // 信頼度 (0-1)
  isTestValue: boolean;    // テスト用の値かどうか
}
```

### 3.5 カスタムパターン

```typescript
const detector = new SecretDetector({
  customPatterns: [
    {
      id: 'custom-api-key',
      name: 'Custom API Key',
      type: 'custom-key',
      severity: 'high',
      regex: /MYAPP_KEY_[A-Z0-9]{32}/g,
      enabled: true,
    },
  ],
});
```

---

## 4. テイント解析

### 4.1 概要

ユーザー入力（ソース）から危険な関数呼び出し（シンク）へのデータフローを追跡し、未サニタイズのデータが脆弱性を引き起こす可能性を検出します。

### 4.2 TaintAnalyzer

```typescript
import { TaintAnalyzer } from '@nahisaho/musubix-security';

const analyzer = new TaintAnalyzer();
const result = analyzer.analyze('./src');

console.log(result.sources);  // テイントソース（ユーザー入力）
console.log(result.sinks);    // テイントシンク（危険な関数）
console.log(result.paths);    // ソースからシンクへのパス
```

### 4.3 テイントソースカテゴリ

| カテゴリ | 説明 | 例 |
|---------|------|-----|
| `user-input` | ユーザー入力 | `req.body`, `req.query`, `req.params` |
| `database` | データベース出力 | `db.query()` の結果 |
| `file-system` | ファイル読み取り | `fs.readFileSync()` |
| `network` | ネットワーク応答 | `fetch()`, `axios` の結果 |
| `environment` | 環境変数 | `process.env.*` |
| `cli-args` | コマンドライン引数 | `process.argv` |

### 4.4 テイントシンクカテゴリ

| カテゴリ | 危険性 | 例 |
|---------|--------|-----|
| `sql-query` | SQLインジェクション | `db.query()`, `knex.raw()` |
| `command-exec` | コマンドインジェクション | `exec()`, `spawn()` |
| `html-output` | XSS | `innerHTML`, `document.write()` |
| `file-read` | パストラバーサル | `fs.readFile()` |
| `file-write` | 任意ファイル書き込み | `fs.writeFile()` |
| `eval` | コードインジェクション | `eval()`, `new Function()` |
| `redirect` | オープンリダイレクト | `res.redirect()` |

### 4.5 TaintResult型

```typescript
interface TaintResult {
  sources: TaintSource[];      // 検出されたソース
  sinks: TaintSink[];          // 検出されたシンク
  paths: TaintPath[];          // ソース→シンクのパス
  sanitizers: string[];        // 検出されたサニタイザ
  summary: {
    totalSources: number;
    totalSinks: number;
    totalPaths: number;
    bySeverity: Record<Severity, number>;
  };
}
```

---

## 5. 依存関係監査

### 5.1 概要

npm auditを統合し、プロジェクトの依存関係に含まれる既知の脆弱性を検出します。

### 5.2 DependencyAuditor

```typescript
import { DependencyAuditor } from '@nahisaho/musubix-security';

const auditor = new DependencyAuditor();
const result = await auditor.audit('./project');

console.log(result.vulnerabilities);     // 脆弱な依存関係
console.log(result.upgradeSuggestions);  // アップグレード提案
```

### 5.3 AuditResult型

```typescript
interface AuditResult {
  vulnerabilities: VulnerableDependency[];
  upgradeSuggestions: UpgradeSuggestion[];
  summary: {
    total: number;
    critical: number;
    high: number;
    medium: number;
    low: number;
  };
  timestamp: Date;
}

interface VulnerableDependency {
  name: string;           // パッケージ名
  version: string;        // 現在のバージョン
  severity: Severity;     // 重要度
  vulnerability: {
    id: string;           // 脆弱性ID (GHSA-*, CVE-*)
    title: string;        // タイトル
    description: string;  // 説明
    patchedVersions: string;  // 修正バージョン
  };
}
```

---

## 6. 統合セキュリティサービス

### 6.1 SecurityService

すべてのセキュリティ機能を統合したサービスクラス。

```typescript
import { createSecurityService } from '@nahisaho/musubix-security';

const service = createSecurityService();

// フルスキャン
const result = await service.scan({
  target: './src',
  vulnerabilities: true,
  taint: true,
  secrets: true,
  dependencies: true,
  generateFixes: true,
});

// クイックスキャン（脆弱性のみ）
const quickResult = await service.quickScan('./src');

// 単一ファイルスキャン
const fileResult = await service.scanFile('src/api.ts');

// テイント解析のみ
const taintResult = await service.analyzeTaint('./src');

// シークレット検出のみ
const secretResult = await service.detectSecrets('./src');

// 依存関係監査のみ
const auditResult = await service.auditDependencies('./project');
```

### 6.2 FullScanResult型

```typescript
interface FullScanResult {
  metadata: {
    target: string;
    timestamp: Date;
    duration: number;
    filesScanned: number;
  };
  vulnerabilities: ScanResult;
  taint?: TaintResult;
  secrets?: SecretScanResult;
  dependencies?: AuditResult;
  fixes?: Fix[];
  summary: {
    totalVulnerabilities: number;
    totalSecrets: number;
    totalTaintPaths: number;
    fixesGenerated: number;
    bySeverity: Record<Severity, number>;
  };
}
```

---

## 7. レポート生成

### 7.1 ReportGenerator

複数のフォーマットでセキュリティレポートを生成します。

```typescript
const report = await service.generateReport(scanResult, 'sarif');

// 対応フォーマット
type ReportFormat = 'json' | 'markdown' | 'html' | 'sarif';
```

### 7.2 SARIF形式

GitHub Code Scanningと互換性のあるSARIF 2.1.0形式を出力。

```json
{
  "$schema": "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json",
  "version": "2.1.0",
  "runs": [{
    "tool": {
      "driver": {
        "name": "MUSUBIX Security Scanner",
        "version": "1.8.0"
      }
    },
    "results": [...]
  }]
}
```

### 7.3 Markdown形式

```markdown
# Security Scan Report

## Summary

| Severity | Count |
|----------|-------|
| Critical | 2 |
| High | 5 |
| Medium | 10 |

## Vulnerabilities

### SQL Injection (CWE-89)
- **File**: src/db.ts:42
- **Severity**: Critical
- **Description**: ...
```

### 7.4 HTML形式

視覚的なダッシュボード形式のHTMLレポートを生成。

---

## 8. 修正生成

### 8.1 FixGenerator

検出された脆弱性に対する修正コードを自動生成します。

```typescript
import { createSecurityService } from '@nahisaho/musubix-security';

const service = createSecurityService();
const scanResult = await service.scan({
  target: './src',
  generateFixes: true,
});

for (const fix of scanResult.fixes) {
  console.log(`Fix for ${fix.vulnerabilityId}:`);
  console.log(`Strategy: ${fix.strategy}`);
  console.log(`Confidence: ${fix.confidence}`);
  for (const edit of fix.edits) {
    console.log(`${edit.file}:${edit.startLine}`);
    console.log(`- ${edit.originalCode}`);
    console.log(`+ ${edit.newCode}`);
  }
}
```

### 8.2 修正戦略

| 戦略 | 対象脆弱性 | 説明 |
|------|-----------|------|
| `parameterized-query` | SQLインジェクション | プリペアドステートメントに変換 |
| `escape-html` | XSS | HTMLエスケープを追加 |
| `shell-escape` | コマンドインジェクション | シェルエスケープを追加 |
| `path-sanitize` | パストラバーサル | パス正規化を追加 |
| `remove-eval` | コードインジェクション | eval を安全な代替に置換 |

### 8.3 Fix型

```typescript
interface Fix {
  id: string;                // 修正ID
  vulnerabilityId: string;   // 対象脆弱性ID
  description: string;       // 修正説明
  strategy: FixStrategy;     // 修正戦略
  confidence: number;        // 信頼度 (0-1)
  edits: CodeEdit[];         // コード編集
}

interface CodeEdit {
  file: string;
  startLine: number;
  endLine: number;
  originalCode: string;
  newCode: string;
}
```

---

## 9. 自動修正・修復システム（Phase 5）

### 9.1 AutoFixer

検出された脆弱性に対する自動修正を生成します。

```typescript
import { AutoFixer, createAutoFixer } from '@nahisaho/musubix-security';

const fixer = createAutoFixer();

// 脆弱性に対する修正を生成
const fixes = fixer.generateFixes(vulnerability, {
  maxFixes: 3,
  minConfidence: 0.7,
  includeBreakingChanges: false,
  preferredStrategies: ['sanitization', 'parameterization'],
});

// 修正を適用
const result = fixer.applyFix(fixes[0], fileContent);
```

### 9.2 FixValidator

修正の適用前に検証を行います。

```typescript
import { FixValidator, createFixValidator } from '@nahisaho/musubix-security';

const validator = createFixValidator();

// 修正の検証
const result = await validator.validate(fix, originalCode, fixedCode);

console.log(result.valid);           // 検証結果
console.log(result.checks);          // 検証チェック一覧
console.log(result.score);           // スコア (0-100)
console.log(result.recommendations); // 推奨事項
```

### 9.3 PatchGenerator

修正をパッチ形式で出力します。

```typescript
import { PatchGenerator, createPatchGenerator } from '@nahisaho/musubix-security';

const generator = createPatchGenerator();

// パッチ生成
const patch = generator.generatePatch(fix, originalContent, {
  format: 'unified', // unified | git | json | context
  contextLines: 3,
});

// パッチの適用
const applied = generator.applyPatch(patch, targetContent);

// リバースパッチ
const reversePatch = generator.generateReversePatch(patch);
```

### 9.4 RemediationPlanner

複数の脆弱性に対する修復計画を策定します。

```typescript
import { RemediationPlanner, createRemediationPlanner } from '@nahisaho/musubix-security';

const planner = createRemediationPlanner();

// 修復計画の作成
const plan = planner.createPlan(vulnerabilities, {
  strategy: 'risk-based', // severity-first | effort-first | risk-based | dependency-aware | balanced
  maxParallelFixes: 3,
});

console.log(plan.phases);           // フェーズ分けされた修復順序
console.log(plan.estimatedEffort);  // 推定作業量
console.log(plan.riskReduction);    // リスク削減効果
```

### 9.5 SecureCodeTransformer

セキュアなコードパターンへの変換を行います。

```typescript
import { SecureCodeTransformer, createSecureCodeTransformer } from '@nahisaho/musubix-security';

const transformer = createSecureCodeTransformer();

// 変換の適用
const result = transformer.transform(code, {
  categories: ['output-encoding', 'cryptography', 'error-handling'],
});

console.log(result.transformed);    // 変換後のコード
console.log(result.changes);        // 変更一覧
console.log(result.riskLevel);      // リスクレベル
```

---

## 10. セキュリティインテリジェンス（Phase 6）

### 10.1 ThreatIntelligence

外部脅威フィードとの統合とIOCマッチングを提供します。

```typescript
import { ThreatIntelligence, createThreatIntelligence } from '@nahisaho/musubix-security';

const intel = createThreatIntelligence();

// フィードの追加
await intel.addFeed({
  id: 'custom-feed',
  name: 'Custom Threat Feed',
  url: 'https://threat-feed.example.com/iocs',
  type: 'stix',
  refreshInterval: 3600000, // 1時間
});

// コードに対するIOCマッチング
const matches = intel.matchCode(sourceCode);

// IOC検索
const iocs = intel.searchIOCs({ type: 'ip', severity: 'high' });
```

### 10.2 AttackPatternMatcher

MITRE ATT&CKフレームワークとの統合を提供します。

```typescript
import { AttackPatternMatcher, createAttackPatternMatcher } from '@nahisaho/musubix-security';

const matcher = createAttackPatternMatcher();

// コードに対するパターンマッチング
const matches = matcher.matchCode(sourceCode);

// 特定のテクニックの取得
const technique = matcher.getTechnique('T1059');

// タクティクス別のテクニック一覧
const techniques = matcher.getTechniquesByTactic('execution');

// カスタムパターンの追加
matcher.addPattern({
  id: 'CUSTOM-001',
  name: 'Custom Attack Pattern',
  technique: 'T1059',
  patterns: [/eval\s*\(/g],
  severity: 'high',
});
```

### 10.3 RiskScorer

CVSS計算とビジネスインパクト評価を行います。

```typescript
import { RiskScorer, createRiskScorer } from '@nahisaho/musubix-security';

const scorer = createRiskScorer();

// CVSS計算
const cvss = scorer.calculateCVSS(vulnerability);
console.log(cvss.baseScore);        // 基本スコア
console.log(cvss.temporalScore);    // 時間的スコア
console.log(cvss.environmentalScore); // 環境的スコア
console.log(cvss.severity);         // 重要度ラベル

// ビジネスインパクト評価
const impact = scorer.assessBusinessImpact(vulnerability, {
  assetCriticality: 'high',
  dataClassification: 'confidential',
  serviceAvailability: 'critical',
});

console.log(impact.score);          // インパクトスコア
console.log(impact.factors);        // 評価要素
console.log(impact.recommendations); // 推奨事項
```

### 10.4 SecurityAnalytics

セキュリティメトリクスの収集とダッシュボード生成を行います。

```typescript
import { SecurityAnalytics, createSecurityAnalytics } from '@nahisaho/musubix-security';

const analytics = createSecurityAnalytics();

// イベントの記録
analytics.recordVulnerability(vulnerability);
analytics.recordFix(fix);
analytics.recordScan(scanResult);

// メトリクス計算
const mttr = analytics.calculateMetric('mean-time-to-remediation');
const vulnTrend = analytics.calculateMetric('vulnerability-trend');

// ダッシュボード生成
const dashboard = analytics.generateDashboard();
console.log(dashboard.summary);     // サマリー
console.log(dashboard.kpis);        // KPI一覧
console.log(dashboard.trends);      // トレンドデータ
```

### 10.5 PredictiveAnalyzer

セキュリティトレンドの予測と異常検出を行います。

```typescript
import { PredictiveAnalyzer, createPredictiveAnalyzer } from '@nahisaho/musubix-security';

const analyzer = createPredictiveAnalyzer();

// データポイントの追加
analyzer.addDataPoints([
  { timestamp: new Date('2026-01-01'), value: 10, metric: 'vulnerabilities' },
  { timestamp: new Date('2026-01-02'), value: 12, metric: 'vulnerabilities' },
  // ...
]);

// リスク予測（30日先）
const projection = analyzer.projectRisk(30);
console.log(projection.projectedRisk);  // 予測リスク値
console.log(projection.confidence);     // 信頼度
console.log(projection.trend);          // トレンド方向

// 異常検出
const anomalies = analyzer.detectAnomalies();
console.log(anomalies);  // 検出された異常一覧

// アラート取得
const alerts = analyzer.getAlerts();
```

---

## 11. CLI使用方法

### 11.1 基本コマンド

```bash
# フルスキャン
npx musubix-security scan ./src

# 脆弱性スキャンのみ
npx musubix-security scan ./src --vulnerabilities-only

# シークレット検出のみ
npx musubix-security secrets ./src

# テイント解析のみ
npx musubix-security taint ./src

# 依存関係監査
npx musubix-security audit ./project
```

### 11.2 オプション

```bash
# 重要度フィルタ
npx musubix-security scan ./src --severity critical,high

# 出力フォーマット
npx musubix-security scan ./src --format sarif --output report.sarif

# 修正生成
npx musubix-security scan ./src --generate-fixes

# 詳細出力
npx musubix-security scan ./src --verbose
```

---

## 12. MCP統合

### 12.1 MCPツール

MCP（Model Context Protocol）サーバーとして以下のツールを提供。

| ツール名 | 説明 |
|---------|------|
| `security_scan` | 包括的セキュリティスキャン |
| `security_scan_file` | 単一ファイルスキャン |
| `security_detect_secrets` | シークレット検出 |
| `security_analyze_taint` | テイント解析 |
| `security_audit_deps` | 依存関係監査 |
| `security_generate_fix` | 修正コード生成 |
| `security_generate_report` | レポート生成 |

### 12.2 MCPサーバー起動

```bash
npx musubix-security-mcp
```

---

## 13. 設定

### 13.1 設定ファイル

プロジェクトルートに `.musubix-securityrc.json` を配置：

```json
{
  "version": "1.0",
  "scan": {
    "severityFilter": ["critical", "high", "medium"],
    "rulesets": ["owasp-top-10", "cwe-top-25"]
  },
  "taint": {
    "interprocedural": true,
    "trackAsync": true,
    "maxPathDepth": 10
  },
  "secret": {
    "ignoreTestValues": true
  },
  "report": {
    "format": "sarif",
    "includeCodeSnippets": true,
    "includeFixes": true
  }
}
```

### 13.2 DEFAULT_CONFIG

```typescript
import { DEFAULT_CONFIG } from '@nahisaho/musubix-security';

// デフォルト設定を確認
console.log(DEFAULT_CONFIG.scan.severityFilter);
// ['critical', 'high', 'medium']
```

---

## 14. テスト統計

| フェーズ | テストファイル数 | テスト数 | 状態 |
|---------|-----------------|---------|------|
| Core | 7 | 125 | ✅ 合格 |
| Phase 2 (Advanced Detection) | 5 | 91 | ✅ 合格 |
| Phase 3 (Enterprise) | 5 | 120 | ✅ 合格 |
| Phase 4 (Integration) | 5 | 141 | ✅ 合格 |
| Phase 5 (Auto-Fix) | 5 | 176 | ✅ 合格 |
| Phase 6 (Intelligence) | 5 | 70 | ✅ 合格 |
| **合計** | **32** | **723** | **✅ 全合格** |

※ 2件のスキップテストあり（Container/Image Scanner の外部依存）

---

## 15. 依存関係

| パッケージ | バージョン | 用途 |
|-----------|-----------|------|
| `ts-morph` | ^24.0.0 | TypeScript AST解析 |
| `minimatch` | ^10.0.1 | ファイルパターンマッチング |
| `cosmiconfig` | ^9.0.0 | 設定ファイル読み込み |
| `yaml` | ^2.7.1 | YAML設定サポート |
| `zod` | ^3.24.1 | スキーマバリデーション |
| `commander` | ^13.1.0 | CLI構築 |
| `@modelcontextprotocol/sdk` | ^1.11.0 | MCP統合 |

---

## 16. 関連ドキュメント

- [MUSUBIX Overview](./MUSUBIX-Overview.md) - システム全体概要
- [MUSUBIX Core](./MUSUBIX-Core.md) - コアライブラリ
- [MUSUBIX Formal Verify](./MUSUBIX-FormalVerify.md) - 形式検証
- [API Reference](../API-REFERENCE.md) - 詳細APIリファレンス

---

## 17. ライセンス

MIT License

Copyright (c) 2026 nahisaho
