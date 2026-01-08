# EPIC-2: CVEデータベース連携 設計書

**Version**: 1.0.0
**Date**: 2026-01-08
**Status**: ✅ APPROVED
**Trace**: REQ-CVE-001 〜 REQ-CVE-005

---

## 1. 概要

### 1.1 目的

NVD (National Vulnerability Database) API と連携し、プロジェクトの依存関係に存在する既知の脆弱性（CVE）を検出するシステムを設計する。

### 1.2 設計方針

- **Infrastructure Layer**: NVD API クライアント、SQLiteキャッシュ
- **Domain Layer**: CVE検索ロジック、CPEマッチング、レポート生成
- **既存資産活用**: `types/cve.ts` の型定義、`infrastructure/cache.ts` のキャッシュ基盤

---

## 2. C4モデル

### 2.1 Context Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                       Developer                              │
└─────────────────────┬───────────────────────────────────────┘
                      │ scans project
                      ▼
┌─────────────────────────────────────────────────────────────┐
│                  MUSUBIX Security                            │
│              (CVE Database Integration)                      │
└─────────────────────┬───────────────────────────────────────┘
                      │ queries
                      ▼
┌─────────────────────────────────────────────────────────────┐
│              NVD (National Vulnerability Database)           │
│                  https://services.nvd.nist.gov               │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 Container Diagram

```
┌──────────────────────────────────────────────────────────────────────┐
│                         MUSUBIX Security Package                      │
│                                                                       │
│  ┌────────────────────┐     ┌────────────────────┐                   │
│  │   CLI / MCP        │────▶│  CVE Scanner       │                   │
│  │   Interface        │     │  Service           │                   │
│  └────────────────────┘     └─────────┬──────────┘                   │
│                                       │                               │
│                    ┌──────────────────┼──────────────────┐           │
│                    │                  │                  │           │
│                    ▼                  ▼                  ▼           │
│  ┌────────────────────┐  ┌────────────────┐  ┌────────────────────┐ │
│  │  Dependency        │  │  CVE Matcher   │  │  Report Generator  │ │
│  │  Parser            │  │  (CPE-based)   │  │  (JSON/MD/HTML)    │ │
│  └────────────────────┘  └───────┬────────┘  └────────────────────┘ │
│                                  │                                   │
│                    ┌─────────────┴─────────────┐                    │
│                    │                           │                    │
│                    ▼                           ▼                    │
│  ┌────────────────────────────┐  ┌────────────────────────────┐    │
│  │     NVD API Client         │  │   SQLite Cache             │    │
│  │  (Rate Limiting, Retry)    │  │   (Offline Support)        │    │
│  └────────────────────────────┘  └────────────────────────────┘    │
│                    │                                                 │
└────────────────────┼─────────────────────────────────────────────────┘
                     │
                     ▼
            ┌────────────────┐
            │    NVD API     │
            │   (External)   │
            └────────────────┘
```

### 2.3 Component Diagram

```
packages/security/src/
├── cve/                           # NEW: CVE連携モジュール
│   ├── index.ts                   # Public exports
│   ├── nvd-client.ts              # NVD API クライアント
│   ├── rate-limiter.ts            # Rate limiting
│   ├── cve-cache.ts               # CVE専用キャッシュ (SQLite)
│   ├── cpe-matcher.ts             # CPE マッチングエンジン
│   ├── dependency-parser.ts       # package.json パーサー
│   ├── cve-scanner.ts             # 統合スキャナー
│   └── report-generator.ts        # レポート生成
├── types/
│   └── cve.ts                     # 既存 (拡張なし)
└── infrastructure/
    └── cache.ts                   # 既存 (拡張なし)
```

---

## 3. コンポーネント設計

### 3.1 DES-CVE-001: NVD API クライアント

**Trace**: REQ-CVE-001

```typescript
// packages/security/src/cve/nvd-client.ts

/**
 * NVD API 2.0 クライアント
 */
export interface NVDClientOptions {
  /** API Key (環境変数 NVD_API_KEY) */
  apiKey?: string;
  /** ベースURL */
  baseUrl?: string;
  /** タイムアウト (ms) */
  timeout?: number;
  /** リトライ回数 */
  maxRetries?: number;
}

export class NVDClient {
  private readonly baseUrl = 'https://services.nvd.nist.gov/rest/json/cves/2.0';
  private rateLimiter: RateLimiter;
  
  constructor(options?: NVDClientOptions);
  
  /**
   * CVE ID で検索
   */
  async getCVE(cveId: string): Promise<CVE | null>;
  
  /**
   * キーワード検索
   */
  async searchByKeyword(keyword: string, options?: CVESearchQuery): Promise<CVESearchResult>;
  
  /**
   * CPE で検索
   */
  async searchByCPE(cpe: string, options?: CVESearchQuery): Promise<CVESearchResult>;
  
  /**
   * CWE ID で検索
   */
  async searchByCWE(cweId: string, options?: CVESearchQuery): Promise<CVESearchResult>;
  
  /**
   * 日付範囲で検索
   */
  async searchByDateRange(
    startDate: Date,
    endDate: Date,
    options?: CVESearchQuery
  ): Promise<CVESearchResult>;
}
```

### 3.2 DES-CVE-002: Rate Limiter

**Trace**: REQ-CVE-001

```typescript
// packages/security/src/cve/rate-limiter.ts

/**
 * NVD API Rate Limiter
 * - API Key あり: 50 req/30s
 * - API Key なし: 5 req/30s
 */
export interface RateLimiterOptions {
  hasApiKey: boolean;
  windowMs?: number;  // Default: 30000 (30s)
}

export class RateLimiter {
  private queue: Array<() => Promise<void>> = [];
  private requestCount = 0;
  private windowStart = Date.now();
  
  constructor(options: RateLimiterOptions);
  
  /**
   * Rate limit を適用してリクエストを実行
   */
  async execute<T>(fn: () => Promise<T>): Promise<T>;
  
  /**
   * 現在のステータス
   */
  getStatus(): { remaining: number; resetIn: number };
}
```

### 3.3 DES-CVE-003: CVE Cache (SQLite)

**Trace**: REQ-CVE-005

```typescript
// packages/security/src/cve/cve-cache.ts

import Database from 'better-sqlite3';

/**
 * SQLite ベースの CVE キャッシュ
 */
export interface CVECacheOptions {
  dbPath: string;
  ttlHours?: number;       // Default: 24
  maxSizeMB?: number;      // Default: 500
}

export class CVECache {
  private db: Database.Database;
  
  constructor(options: CVECacheOptions);
  
  /**
   * CVE を取得（キャッシュ優先）
   */
  async get(cveId: string): Promise<CVE | null>;
  
  /**
   * CVE をキャッシュに保存
   */
  async set(cve: CVE): Promise<void>;
  
  /**
   * 複数 CVE を一括保存
   */
  async setBulk(cves: CVE[]): Promise<void>;
  
  /**
   * CPE で検索（ローカル）
   */
  async searchByCPE(cpe: string): Promise<CVE[]>;
  
  /**
   * 差分同期（前回同期以降の更新のみ）
   */
  async syncIncremental(client: NVDClient): Promise<CVESyncResult>;
  
  /**
   * 古いエントリの削除
   */
  async cleanup(): Promise<number>;
  
  /**
   * データベース統計
   */
  getStats(): CVECacheStats;
}

interface CVECacheStats {
  totalEntries: number;
  sizeBytes: number;
  oldestEntry: Date;
  newestEntry: Date;
  lastSync: Date | null;
}
```

### 3.4 DES-CVE-004: CPE Matcher

**Trace**: REQ-CVE-003

```typescript
// packages/security/src/cve/cpe-matcher.ts

/**
 * npm パッケージ → CPE 変換 & マッチング
 */
export class CPEMatcher {
  private mappings: Map<string, NpmCPEMapping> = new Map();
  
  constructor();
  
  /**
   * npm パッケージ名から CPE を生成
   * 例: "lodash" → "cpe:2.3:a:lodash:lodash:*:*:*:*:*:node.js:*:*"
   */
  npmToCPE(packageName: string, version?: string): string;
  
  /**
   * CPE がバージョン範囲にマッチするか
   */
  matchesCPE(cpe: string, cpeMatch: CPEMatch): boolean;
  
  /**
   * semver バージョン範囲チェック
   */
  versionInRange(
    version: string,
    startIncluding?: string,
    startExcluding?: string,
    endIncluding?: string,
    endExcluding?: string
  ): boolean;
  
  /**
   * カスタムマッピングを追加
   */
  addMapping(mapping: NpmCPEMapping): void;
  
  /**
   * 既知のマッピングをロード
   */
  loadKnownMappings(): Promise<void>;
}
```

### 3.5 DES-CVE-005: Dependency Parser

**Trace**: REQ-CVE-003

```typescript
// packages/security/src/cve/dependency-parser.ts

/**
 * 解析済み依存関係
 */
export interface ParsedDependency {
  name: string;
  version: string;
  type: 'direct' | 'transitive';
  path: string[];  // 依存パス (transitive の場合)
  dev: boolean;
}

/**
 * package.json / package-lock.json パーサー
 */
export class DependencyParser {
  /**
   * package.json から直接依存を解析
   */
  async parsePackageJson(path: string): Promise<ParsedDependency[]>;
  
  /**
   * package-lock.json から全依存（推移的含む）を解析
   */
  async parsePackageLock(path: string): Promise<ParsedDependency[]>;
  
  /**
   * プロジェクトディレクトリから依存を解析
   */
  async parseProject(projectDir: string): Promise<ParsedDependency[]>;
  
  /**
   * 依存ツリーを構築
   */
  buildDependencyTree(dependencies: ParsedDependency[]): DependencyTree;
}

interface DependencyTree {
  root: string;
  nodes: Map<string, DependencyNode>;
}

interface DependencyNode {
  name: string;
  version: string;
  children: string[];
  parents: string[];
}
```

### 3.6 DES-CVE-006: CVE Scanner

**Trace**: REQ-CVE-003

```typescript
// packages/security/src/cve/cve-scanner.ts

/**
 * スキャンオプション
 */
export interface CVEScanOptions {
  /** 最小 CVSS スコア閾値 */
  minSeverity?: CVSSSeverity;
  /** dev dependencies を含む */
  includeDev?: boolean;
  /** オフラインモード（キャッシュのみ） */
  offline?: boolean;
  /** 並列リクエスト数 */
  concurrency?: number;
}

/**
 * スキャン結果
 */
export interface CVEScanResult {
  projectPath: string;
  scannedAt: Date;
  totalDependencies: number;
  vulnerableDependencies: number;
  findings: CVEFinding[];
  summary: {
    critical: number;
    high: number;
    medium: number;
    low: number;
    none: number;
  };
}

/**
 * CVE 統合スキャナー
 */
export class CVEScanner {
  private client: NVDClient;
  private cache: CVECache;
  private matcher: CPEMatcher;
  private parser: DependencyParser;
  
  constructor(options?: CVEScannerOptions);
  
  /**
   * プロジェクトをスキャン
   */
  async scan(projectDir: string, options?: CVEScanOptions): Promise<CVEScanResult>;
  
  /**
   * 特定パッケージをスキャン
   */
  async scanPackage(
    packageName: string,
    version: string
  ): Promise<CVEFinding[]>;
  
  /**
   * 進捗コールバック付きスキャン
   */
  async scanWithProgress(
    projectDir: string,
    onProgress: (progress: ScanProgress) => void,
    options?: CVEScanOptions
  ): Promise<CVEScanResult>;
}

interface ScanProgress {
  phase: 'parsing' | 'scanning' | 'reporting';
  current: number;
  total: number;
  currentPackage?: string;
}
```

### 3.7 DES-CVE-007: Report Generator

**Trace**: REQ-CVE-004

```typescript
// packages/security/src/cve/report-generator.ts

/**
 * レポート形式
 */
export type ReportFormat = 'json' | 'markdown' | 'html' | 'sarif';

/**
 * レポートオプション
 */
export interface ReportOptions {
  format: ReportFormat;
  outputPath?: string;
  includeRemediation?: boolean;
  groupBy?: 'severity' | 'package' | 'cwe';
}

/**
 * CVE レポート生成
 */
export class CVEReportGenerator {
  /**
   * レポートを生成
   */
  async generate(
    result: CVEScanResult,
    options: ReportOptions
  ): Promise<string>;
  
  /**
   * JSON 形式
   */
  private generateJSON(result: CVEScanResult): string;
  
  /**
   * Markdown 形式
   */
  private generateMarkdown(result: CVEScanResult): string;
  
  /**
   * HTML 形式
   */
  private generateHTML(result: CVEScanResult): string;
  
  /**
   * SARIF 形式 (GitHub Code Scanning 互換)
   */
  private generateSARIF(result: CVEScanResult): string;
}
```

---

## 4. データフロー

```
┌─────────────────┐
│  package.json   │
│  package-lock   │
└────────┬────────┘
         │ parse
         ▼
┌─────────────────┐     ┌─────────────────┐
│  Dependency     │────▶│  CPE Matcher    │
│  Parser         │     │  (npm → CPE)    │
└─────────────────┘     └────────┬────────┘
                                 │ CPE queries
         ┌───────────────────────┼───────────────────────┐
         │                       │                       │
         ▼                       ▼                       ▼
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  SQLite Cache   │◀───▶│  NVD Client     │────▶│  NVD API        │
│  (Local)        │     │  (Rate Limited) │     │  (External)     │
└────────┬────────┘     └─────────────────┘     └─────────────────┘
         │
         │ CVE findings
         ▼
┌─────────────────┐     ┌─────────────────┐
│  CVE Scanner    │────▶│  Report         │────▶ JSON/MD/HTML/SARIF
│  (Matcher)      │     │  Generator      │
└─────────────────┘     └─────────────────┘
```

---

## 5. エラーハンドリング

| エラー | 対応 |
|--------|------|
| NVD API タイムアウト | 3回リトライ（指数バックオフ） |
| NVD API 429 (Rate Limit) | Rate limiter で自動待機 |
| NVD API 5xx | リトライ後、キャッシュにフォールバック |
| ネットワークエラー | オフラインモードでキャッシュ使用 |
| package.json パースエラー | SecurityError を throw |
| CPE マッチング失敗 | ログ出力、スキップして続行 |

---

## 6. 依存パッケージ

| パッケージ | バージョン | 用途 |
|-----------|-----------|------|
| `better-sqlite3` | ^11.0.0 | SQLite キャッシュ |
| `semver` | ^7.6.0 | バージョン範囲マッチング |
| `node-fetch` | (native) | NVD API 呼び出し |

---

## 7. タスク → 設計 トレーサビリティ

| タスク | 設計 |
|--------|------|
| TSK-CVE-001 | DES-CVE-001 (NVD Client) |
| TSK-CVE-002 | DES-CVE-002 (Rate Limiter), DES-CVE-003 (Cache) |
| TSK-CVE-003 | DES-CVE-001 (Search methods) |
| TSK-CVE-004 | DES-CVE-004 (CPE Matcher) |
| TSK-CVE-005 | DES-CVE-005 (Dependency Parser) |
| TSK-CVE-006 | DES-CVE-006 (CVE Scanner) |
| TSK-CVE-007 | DES-CVE-003 (SQLite Cache) |
| TSK-CVE-008 | DES-CVE-007 (Report Generator) |

---

## 8. 承認

- [x] アーキテクチャの妥当性
- [x] 既存コードとの整合性
- [x] 依存パッケージの適切性
- [x] タスク分解の妥当性
- [x] ユーザー承認 (2026-01-08)

---

**Status**: ✅ APPROVED
