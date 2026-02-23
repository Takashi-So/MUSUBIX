# MUSUBIX Security v2.1.0 - セキュリティ強化リリース

**パッケージ名**: `@nahisaho/musubix-security`  
**バージョン**: 2.1.0  
**最終更新**: 2026-01-08

---

## 1. 概要

MUSUBIX v2.1.0は、**4つのEPIC**で**30タスク**を実装したセキュリティ強化リリースです。**3400+テスト**が全て合格しており、エンタープライズグレードのセキュリティ分析を提供します。

### 1.1 v2.1.0 新機能サマリー

| EPIC | 機能 | タスク数 | テスト数 |
|------|------|---------|---------|
| **EPIC-1** | テイント分析強化 | 8 | 200+ |
| **EPIC-2** | CVEデータベース連携 | 7 | 150+ |
| **EPIC-3** | OWASP/CWE Top 25 ルール | 6 | 700+ |
| **EPIC-4** | 自動修正パイプライン | 9 | 200+ |

### 1.2 アーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                    Security Analysis Engine                  │
├─────────────────────────────────────────────────────────────┤
│  EPIC-1: Enhanced Taint Analysis                            │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │ 50+ Sources │──│ Propagation │──│ 40+ Sinks           │ │
│  │ (HTTP,ENV)  │  │ (DFG/CFG)   │  │ (SQL,CMD,XSS)       │ │
│  └─────────────┘  └─────────────┘  └─────────────────────┘ │
├─────────────────────────────────────────────────────────────┤
│  EPIC-2: CVE Database Integration                           │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │ NVD API 2.0 │──│ CVE Cache   │──│ Vuln Matching       │ │
│  │ (Real-time) │  │ (SQLite)    │  │ (Semver/Regex)      │ │
│  └─────────────┘  └─────────────┘  └─────────────────────┘ │
├─────────────────────────────────────────────────────────────┤
│  EPIC-3: OWASP/CWE Rules                                    │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │ OWASP Top10 │──│ CWE Top 25  │──│ Rule Engine         │ │
│  │ (10 Rules)  │  │ (25 Rules)  │  │ (Registry/Config)   │ │
│  └─────────────┘  └─────────────┘  └─────────────────────┘ │
├─────────────────────────────────────────────────────────────┤
│  EPIC-4: Auto-Fix Pipeline                                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐ │
│  │ Fix Gen     │──│ Validation  │──│ CI/CD Integration   │ │
│  │ (Template)  │  │ (Sandbox)   │  │ (GitHub/GitLab)     │ │
│  └─────────────┘  └─────────────┘  └─────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
```

---

## 2. EPIC-1: テイント分析強化

### 2.1 概要

高度なテイント追跡システムにより、ユーザー入力から危険なシンクへのデータフローを正確に追跡します。

### 2.2 ソース定義（50+）

```typescript
import {
  ALL_BUILTIN_SOURCES,
  SourceCategory,
} from '@nahisaho/musubix-security';

// カテゴリ別ソース
const categories: SourceCategory[] = [
  'user-input',    // req.body, req.query, req.params, document.getElementById
  'network',       // fetch, axios.get, http.request
  'environment',   // process.env, Deno.env
  'file',          // fs.readFile, fs.readFileSync
  'database',      // query result, findOne, findMany
  'external-api',  // response.json(), response.text()
];

// 例: user-input ソース
// req.body, req.query, req.params, req.headers
// document.getElementById, document.querySelector
// window.location, URLSearchParams
```

### 2.3 シンク定義（40+）

```typescript
import {
  ALL_BUILTIN_SINKS,
  SinkCategory,
} from '@nahisaho/musubix-security';

// カテゴリ別シンク
const sinkCategories: SinkCategory[] = [
  'sql-query',     // query(), execute(), raw()
  'command-exec',  // exec(), spawn(), execSync()
  'html-output',   // innerHTML, document.write()
  'file-path',     // fs.readFile(), fs.writeFile()
  'code-exec',     // eval(), Function(), vm.runInContext()
  'redirect',      // res.redirect(), window.location
];
```

### 2.4 サニタイザ定義（30+）

```typescript
import {
  ALL_BUILTIN_SANITIZERS,
  SanitizerMapping,
} from '@nahisaho/musubix-security';

// シンクタイプ別サニタイザ
const sanitizers: SanitizerMapping = {
  'sql-query': ['parameterizedQuery', 'escapeSQL', 'preparedStatement'],
  'html-output': ['escapeHTML', 'sanitizeHTML', 'DOMPurify.sanitize'],
  'command-exec': ['escapeShell', 'shellEscape'],
  'file-path': ['path.normalize', 'path.resolve', 'validatePath'],
  'redirect': ['validateURL', 'isAllowedDomain'],
};
```

### 2.5 手続き間テイント伝播

```typescript
import {
  CallGraphBuilder,
  TaintPropagator,
  InterproceduralAnalyzer,
} from '@nahisaho/musubix-security';

// コールグラフ構築
const callGraph = new CallGraphBuilder();
callGraph.buildFromProject('./src');

// 手続き間テイント伝播
const propagator = new TaintPropagator(callGraph);
const taintFlows = propagator.analyze(code);

// DFG統合解析
const analyzer = new InterproceduralAnalyzer({
  maxDepth: 10,
  trackImplicitFlows: true,
});
const result = await analyzer.analyze(project);
```

### 2.6 使用例

```typescript
import { createEnhancedTaintAnalyzer } from '@nahisaho/musubix-security';

const analyzer = createEnhancedTaintAnalyzer({
  maxDepth: 10,
  sources: ALL_BUILTIN_SOURCES,
  sinks: ALL_BUILTIN_SINKS,
  sanitizers: ALL_BUILTIN_SANITIZERS,
});

const result = await analyzer.analyze(`
  const userInput = req.body.name;
  const query = "SELECT * FROM users WHERE name = '" + userInput + "'";
  db.query(query);  // 🚨 SQL Injection detected!
`, 'app.ts');

console.log(result.taintFlows);
// [{
//   source: { type: 'user-input', location: 'req.body.name' },
//   sink: { type: 'sql-query', location: 'db.query()' },
//   path: ['userInput', 'query', 'db.query'],
//   sanitized: false
// }]
```

---

## 3. EPIC-2: CVEデータベース連携

### 3.1 概要

NVD（National Vulnerability Database）API 2.0と連携し、リアルタイムでCVE情報を取得・照合します。

### 3.2 NVDClient

```typescript
import { NVDClient, NVDConfig } from '@nahisaho/musubix-security';

const client = new NVDClient({
  apiKey: process.env.NVD_API_KEY,  // オプション（レートリミット緩和）
  cacheEnabled: true,
  cacheTTL: 86400,  // 24時間
});

// CVE検索
const cves = await client.searchCVEs({
  keywordSearch: 'lodash',
  resultsPerPage: 20,
});

// 特定CVE取得
const cve = await client.getCVE('CVE-2021-23337');
console.log(cve.cvssV3Score);  // 7.2
console.log(cve.description);
```

### 3.3 CVEマッチング

```typescript
import { CVEMatcher, DependencyScanner } from '@nahisaho/musubix-security';

const matcher = new CVEMatcher(nvdClient);
const scanner = new DependencyScanner();

// package.json解析
const deps = await scanner.scanPackageJson('./package.json');

// CVEマッチング
const matches = await matcher.matchDependencies(deps);

for (const match of matches) {
  console.log(`${match.package}@${match.version}`);
  console.log(`  CVE: ${match.cve.id}`);
  console.log(`  CVSS: ${match.cve.cvssV3Score}`);
  console.log(`  Fix: ${match.fixedVersion || 'No fix available'}`);
}
```

### 3.4 ローカルキャッシュ

```typescript
import { CVECache, CVEDatabase } from '@nahisaho/musubix-security';

// SQLiteベースのローカルキャッシュ
const cache = new CVECache({
  dbPath: './.musubix/cve-cache.db',
  ttl: 86400 * 7,  // 7日間
});

// バッチ更新
await cache.updateFromNVD({
  startDate: '2024-01-01',
  modifiedSince: lastUpdateDate,
});

// ローカル検索（高速）
const results = cache.search({
  package: 'express',
  versionRange: '>=4.0.0 <4.18.2',
});
```

---

## 4. EPIC-3: OWASP/CWE Top 25 ルール

### 4.1 概要

OWASP Top 10（2021）とCWE Top 25（2023）に完全対応したルールエンジンを実装しました。

### 4.2 OWASP Top 10 ルール

```typescript
import { OWASPRules } from '@nahisaho/musubix-security';

// A01: Broken Access Control
// A02: Cryptographic Failures  
// A03: Injection
// A04: Insecure Design
// A05: Security Misconfiguration
// A06: Vulnerable Components
// A07: Authentication Failures
// A08: Integrity Failures
// A09: Logging Failures
// A10: SSRF

const rules = OWASPRules.getAll();
console.log(rules.length);  // 10
```

### 4.3 CWE Top 25 ルール

```typescript
import { CWERules } from '@nahisaho/musubix-security';

// CWE-79: XSS
// CWE-89: SQL Injection
// CWE-78: OS Command Injection
// CWE-20: Improper Input Validation
// CWE-22: Path Traversal
// CWE-352: CSRF
// CWE-434: Unrestricted File Upload
// CWE-502: Deserialization
// CWE-798: Hardcoded Credentials
// CWE-862: Missing Authorization
// ... (25 rules total)

const rules = CWERules.getAll();
console.log(rules.length);  // 25
```

### 4.4 ルールエンジン

```typescript
import {
  RuleEngine,
  RuleRegistry,
  RuleContext,
} from '@nahisaho/musubix-security';

// ルール登録
const registry = new RuleRegistry();
registry.registerAll(OWASPRules.getAll());
registry.registerAll(CWERules.getAll());

// エンジン初期化
const engine = new RuleEngine(registry, {
  severity: ['critical', 'high', 'medium'],
  categories: ['injection', 'authentication'],
});

// 解析実行
const context = new RuleContext(sourceFile, project);
const violations = await engine.analyze(context);

for (const v of violations) {
  console.log(`[${v.rule.id}] ${v.message}`);
  console.log(`  File: ${v.location.file}:${v.location.line}`);
  console.log(`  Severity: ${v.severity}`);
  console.log(`  Fix: ${v.suggestedFix}`);
}
```

### 4.5 設定プロファイル

```typescript
import { SecurityProfiles } from '@nahisaho/musubix-security';

// 組み込みプロファイル
const profiles = {
  'default': SecurityProfiles.DEFAULT,      // バランス
  'strict': SecurityProfiles.STRICT,        // 厳格
  'minimal': SecurityProfiles.MINIMAL,      // 最小
  'owasp-top10': SecurityProfiles.OWASP,    // OWASPのみ
  'cwe-top25': SecurityProfiles.CWE,        // CWEのみ
};

// カスタムプロファイル
const custom = SecurityProfiles.create({
  extends: 'strict',
  rules: {
    'CWE-79': 'error',
    'CWE-89': 'error',
    'CWE-352': 'warn',
  },
  exclude: ['**/test/**', '**/node_modules/**'],
});
```

---

## 5. EPIC-4: 自動修正パイプライン

### 5.1 概要

検出された脆弱性に対して、安全な修正コードを自動生成し、CI/CDパイプラインに統合します。

### 5.2 AutoFixer

```typescript
import { AutoFixer, FixTemplate } from '@nahisaho/musubix-security';

const fixer = new AutoFixer({
  templates: FixTemplate.loadBuiltins(),
  validateFix: true,
  preserveSemantics: true,
});

// 脆弱性に対する修正生成
const fix = await fixer.generateFix(vulnerability);

console.log(fix.original);
// const query = "SELECT * FROM users WHERE id = " + userId;

console.log(fix.fixed);
// const query = "SELECT * FROM users WHERE id = ?";
// db.query(query, [userId]);

console.log(fix.explanation);
// "パラメータ化クエリを使用してSQLインジェクションを防止"
```

### 5.3 修正検証

```typescript
import { FixValidator, SandboxRunner } from '@nahisaho/musubix-security';

const validator = new FixValidator({
  sandbox: new SandboxRunner(),
  timeout: 5000,
});

// 修正の検証
const result = await validator.validate(fix, {
  syntaxCheck: true,        // 構文チェック
  typeCheck: true,          // 型チェック
  semanticCheck: true,      // セマンティクス保持
  securityCheck: true,      // 脆弱性再発防止
  testExecution: true,      // テスト実行
});

if (result.valid) {
  await fix.apply();
} else {
  console.error(result.errors);
}
```

### 5.4 パッチ生成

```typescript
import { PatchGenerator, UnifiedDiff } from '@nahisaho/musubix-security';

const generator = new PatchGenerator();

// 単一ファイルパッチ
const patch = generator.generatePatch(fix);
console.log(patch.diff);
// --- a/src/api.ts
// +++ b/src/api.ts
// @@ -10,3 +10,4 @@
// -const query = "SELECT * FROM users WHERE id = " + userId;
// +const query = "SELECT * FROM users WHERE id = ?";
// +db.query(query, [userId]);

// 複数修正のバッチパッチ
const batchPatch = generator.generateBatchPatch(fixes);
await batchPatch.writeToFile('./security-fixes.patch');
```

### 5.5 CI/CD統合

```typescript
import { CIIntegration, GitHubActions, GitLabCI } from '@nahisaho/musubix-security';

// GitHub Actions統合
const github = new GitHubActions({
  token: process.env.GITHUB_TOKEN,
  repo: 'owner/repo',
});

// セキュリティスキャン結果をPRコメント
await github.commentOnPR(prNumber, {
  violations: scanResult.violations,
  fixes: generatedFixes,
  summary: true,
});

// 自動修正PR作成
await github.createFixPR({
  fixes: generatedFixes,
  branch: 'security/auto-fix',
  title: 'Security: Auto-fix vulnerabilities',
  labels: ['security', 'auto-generated'],
});
```

### 5.6 パイプラインオーケストレーション

```typescript
import {
  SecurityPipeline,
  PipelineStage,
  PipelineConfig,
} from '@nahisaho/musubix-security';

const pipeline = new SecurityPipeline({
  stages: [
    PipelineStage.SCAN,           // 脆弱性スキャン
    PipelineStage.TAINT_ANALYSIS, // テイント解析
    PipelineStage.CVE_CHECK,      // CVEチェック
    PipelineStage.RULE_CHECK,     // ルールチェック
    PipelineStage.FIX_GENERATION, // 修正生成
    PipelineStage.VALIDATION,     // 検証
    PipelineStage.REPORT,         // レポート生成
  ],
  parallel: true,
  failFast: false,
});

const result = await pipeline.run('./src');

console.log(result.summary);
// {
//   totalVulnerabilities: 15,
//   fixable: 12,
//   fixed: 10,
//   manualReviewRequired: 5,
//   duration: '45s'
// }
```

---

## 6. 使用例

### 6.1 基本的なセキュリティスキャン

```typescript
import { SecurityService } from '@nahisaho/musubix-security';

const service = new SecurityService({
  profile: 'strict',
  enableTaintAnalysis: true,
  enableCVECheck: true,
});

const result = await service.scan('./src');

console.log(`Found ${result.vulnerabilities.length} vulnerabilities`);
console.log(`Critical: ${result.summary.critical}`);
console.log(`High: ${result.summary.high}`);
```

### 6.2 自動修正ワークフロー

```typescript
import {
  SecurityService,
  AutoFixer,
  ReportGenerator,
} from '@nahisaho/musubix-security';

// スキャン
const service = new SecurityService({ profile: 'strict' });
const scanResult = await service.scan('./src');

// 修正生成
const fixer = new AutoFixer();
const fixes = await fixer.generateFixes(scanResult.vulnerabilities);

// 修正適用（ドライラン）
const dryRun = await fixer.applyFixes(fixes, { dryRun: true });
console.log(`${dryRun.applied} fixes would be applied`);

// レポート生成
const reporter = new ReportGenerator();
await reporter.generate(scanResult, {
  format: 'html',
  output: './security-report.html',
  includeFixes: true,
});
```

### 6.3 CI/CDパイプライン統合

```yaml
# .github/workflows/security.yml
name: Security Scan

on: [push, pull_request]

jobs:
  security:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Run MUSUBIX Security
        run: |
          npx musubix security scan ./src \
            --profile strict \
            --format sarif \
            --output security-results.sarif
      
      - name: Upload SARIF
        uses: github/codeql-action/upload-sarif@v3
        with:
          sarif_file: security-results.sarif
```

---

## 7. 設定

### 7.1 設定ファイル

```json
// musubix.security.json
{
  "profile": "strict",
  "rules": {
    "CWE-79": "error",
    "CWE-89": "error",
    "CWE-78": "error"
  },
  "taintAnalysis": {
    "enabled": true,
    "maxDepth": 10,
    "trackImplicitFlows": true
  },
  "cveCheck": {
    "enabled": true,
    "apiKey": "${NVD_API_KEY}",
    "cacheTTL": 86400
  },
  "autoFix": {
    "enabled": true,
    "validateFix": true,
    "preserveSemantics": true
  },
  "exclude": [
    "**/node_modules/**",
    "**/dist/**",
    "**/*.test.ts"
  ]
}
```

### 7.2 環境変数

| 変数名 | 説明 | デフォルト |
|--------|------|-----------|
| `NVD_API_KEY` | NVD APIキー（オプション） | - |
| `MUSUBIX_SECURITY_PROFILE` | デフォルトプロファイル | `default` |
| `MUSUBIX_SECURITY_CACHE_DIR` | キャッシュディレクトリ | `.musubix/cache` |

---

## 8. テスト

### 8.1 テスト統計

| カテゴリ | テスト数 | 合格率 |
|---------|---------|--------|
| テイント分析 | 200+ | 100% |
| CVE連携 | 150+ | 100% |
| OWASP/CWE | 700+ | 100% |
| 自動修正 | 200+ | 100% |
| 統合テスト | 150+ | 100% |
| **合計** | **1400+** | **100%** |

### 8.2 テスト実行

```bash
# 全テスト
npm run test

# セキュリティパッケージのみ
npm run test -- --filter @nahisaho/musubix-security

# カバレッジ
npm run test:coverage
```

---

## 9. 関連ドキュメント

- [MUSUBIX-Security.md](./MUSUBIX-Security.md) - 基本機能ドキュメント
- [MUSUBIX-Security-Plan.md](./MUSUBIX-Security-Plan.md) - セキュリティ実装計画
- [API-REFERENCE.md](../API-REFERENCE.md) - APIリファレンス
- [CHANGELOG.md](../../CHANGELOG.md) - 変更履歴

---

**作成日**: 2026-01-08  
**バージョン**: 2.1.0  
**作成者**: MUSUBIX Development Team
