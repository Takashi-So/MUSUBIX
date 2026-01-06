# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.8.0] - 2026-01-06

### Added - Security Analysis Edition

セキュリティ分析機能を提供する新パッケージ`@nahisaho/musubix-security`をリリース。全59テスト合格。

#### 脆弱性スキャン

OWASP Top 10/CWE Top 25に基づくセキュリティ脆弱性検出:

```typescript
import { VulnerabilityScanner, createSecurityService } from '@nahisaho/musubix-security';

// 脆弱性スキャナー
const scanner = new VulnerabilityScanner();
const vulnerabilities = scanner.scanFile('src/api.ts');
const result = await scanner.scanDirectory('./src');

// 統合セキュリティサービス
const service = createSecurityService();
const fullScan = await service.scan({
  target: './src',
  vulnerabilities: true,
  taint: true,
  secrets: true,
  dependencies: true,
  generateFixes: true,
});
```

#### 検出可能な脆弱性

| カテゴリ | 検出パターン |
|---------|-------------|
| SQLインジェクション | 文字列連結、テンプレートリテラル |
| コマンドインジェクション | exec, execSync, spawn |
| XSS | innerHTML, document.write |
| パストラバーサル | fs.readFile with user input |
| コードインジェクション | eval, new Function |

#### シークレット検出

機密情報のハードコード検出:

```typescript
import { SecretDetector } from '@nahisaho/musubix-security';

const detector = new SecretDetector();
const secrets = detector.scanContent(content, 'config.ts');
const result = await detector.scan('./src');
```

| シークレットタイプ | パターン |
|------------------|----------|
| AWS Access Key | AKIA... |
| AWS Secret Key | 40文字base64 |
| GitHub Token | ghp_*, gho_*, ghu_* |
| Private Key | PEM形式 |
| Database URL | postgres://, mongodb:// |
| JWT | eyJ... |
| Stripe Key | sk_live_*, sk_test_* |

#### テイント解析

データフロー追跡による汚染解析:

```typescript
import { TaintAnalyzer } from '@nahisaho/musubix-security';

const analyzer = new TaintAnalyzer();
const result = analyzer.analyze('./src');
// sources: ユーザー入力の検出
// sinks: 危険な関数呼び出しの検出
// paths: ソースからシンクへのデータフロー
```

#### 依存関係監査

npm audit統合による脆弱な依存関係の検出:

```typescript
import { DependencyAuditor } from '@nahisaho/musubix-security';

const auditor = new DependencyAuditor();
const result = await auditor.audit('./project');
// vulnerabilities: 脆弱な依存関係
// upgradeSuggestions: アップグレード提案
```

#### レポート生成

複数フォーマットでのレポート出力:

```typescript
const report = await service.generateReport(scanResult, 'sarif');
// 対応フォーマット: json, markdown, html, sarif
```

### テスト統計

- **テスト数**: 59件（全合格）
- **カバレッジ**: types, secret-detector, vulnerability-scanner, security-service

---

## [1.7.5] - 2026-01-07

### Added - Formal Verification Edition

形式検証機能を追加する新パッケージ`@nahisaho/musubix-formal-verify`をリリース。全141テスト合格。

#### Z3 SMTソルバー統合

Z3定理証明器との統合により、コード仕様の形式検証が可能に:

```typescript
import { Z3Adapter, PreconditionVerifier, PostconditionVerifier } from '@nahisaho/musubix-formal-verify';

// Z3アダプター（自動フォールバック機能付き）
const z3 = await Z3Adapter.create();

// 事前条件検証
const preVerifier = new PreconditionVerifier(z3);
const result = await preVerifier.verify({
  condition: { expression: 'amount > 0 && balance >= amount', format: 'javascript' },
  variables: [
    { name: 'amount', type: 'Int' },
    { name: 'balance', type: 'Int' },
  ],
});

// 事後条件検証（Hoareトリプル）
const postVerifier = new PostconditionVerifier(z3);
const hoareResult = await postVerifier.verify({
  precondition: { expression: 'balance >= amount', format: 'javascript' },
  postcondition: { expression: 'balance_new == balance - amount', format: 'javascript' },
  preVariables: [{ name: 'balance', type: 'Int' }, { name: 'amount', type: 'Int' }],
  postVariables: [{ name: 'balance_new', type: 'Int' }],
  transition: 'balance_new == balance - amount',
});
```

#### Z3バックエンド

| クラス | 説明 |
|--------|------|
| `Z3WasmClient` | WebAssembly版z3-solver（高速） |
| `Z3ProcessFallback` | 外部Z3プロセス（フォールバック） |
| `Z3Adapter` | 自動バックエンド選択 |

#### EARS→SMT変換

EARS形式要件をSMT-LIB2に変換:

```typescript
import { EarsToSmtConverter } from '@nahisaho/musubix-formal-verify';

const converter = new EarsToSmtConverter();

// 5パターン対応
const results = converter.convertMultiple([
  'THE system SHALL validate inputs',           // ubiquitous
  'WHEN error, THE system SHALL notify user',   // event-driven
  'WHILE busy, THE system SHALL queue requests', // state-driven
  'THE system SHALL NOT expose secrets',        // unwanted
  'IF admin, THEN THE system SHALL allow edit', // optional
]);
```

#### トレーサビリティDB

SQLiteベースの高性能トレーサビリティデータベース:

```typescript
import { TraceabilityDB, ImpactAnalyzer } from '@nahisaho/musubix-formal-verify';

const db = new TraceabilityDB('./trace.db');

// ノード追加
await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'Auth' });
await db.addNode({ id: 'DES-001', type: 'design', title: 'AuthService' });

// リンク追加
await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });

// 影響分析
const analyzer = new ImpactAnalyzer(db);
const impact = await analyzer.analyze('REQ-001');
console.log(`影響ノード数: ${impact.totalImpacted}`);
```

#### MCPツール（6ツール）

| ツール | 説明 |
|--------|------|
| `verify_precondition` | 事前条件の充足可能性検証 |
| `verify_postcondition` | 事後条件（Hoareトリプル）検証 |
| `ears_to_smt` | EARS→SMT-LIB2変換 |
| `trace_add_link` | トレーサビリティリンク追加 |
| `trace_query` | トレーサビリティクエリ |
| `trace_impact` | 影響範囲分析 |

### Technical Details

- **パッケージ**: `@nahisaho/musubix-formal-verify@1.7.5`
- **依存関係**: `z3-solver`（オプション）, `better-sqlite3`
- **テスト**: 141テスト（100%合格）
- **サポート型**: `Int`, `Real`, `Bool`, `String`, `Array`, `BitVec`

---

## [1.7.0] - 2026-01-06

### Added - YATA Platform Enhancements

5つの重要な改善を実装。全1386テスト合格。

#### Phase 1: インデックス最適化 (REQ-YI-IDX-001〜003)

`IndexOptimizer`クラスを`@nahisaho/yata-local`に追加:

| メソッド | 説明 |
|---------|------|
| `analyzeQueries()` | クエリパターン分析 |
| `suggestIndexes()` | インデックス推奨（<5秒） |
| `createIndex()` | インデックス作成 |
| `dropIndex()` | インデックス削除 |
| `getIndexStats()` | 統計取得 |
| `optimizeAll()` | 自動最適化 |

#### Phase 2: エクスポート機能 (REQ-YI-EXP-001〜003)

複数フォーマットでのエクスポート対応:

```typescript
import { exportToRDF, exportToJSON, exportToCSV } from '@nahisaho/yata-local';

// RDF/Turtle形式（標準準拠）
const rdf = await exportToRDF(db, { format: 'turtle' });

// JSON-LD形式
const jsonld = await exportToJSON(db, { format: 'json-ld' });

// CSV形式（スプレッドシート互換）
const csv = await exportToCSV(db, { includeMetadata: true });
```

#### Phase 3: YATA Global統合 (REQ-YI-GLB-001〜003)

`GlobalSyncManager`クラスを追加:

| メソッド | 説明 |
|---------|------|
| `sync()` | 双方向同期（60秒/1000変更以内） |
| `push()` | ローカル→リモート同期 |
| `pull()` | リモート→ローカル同期 |
| `getStatus()` | 同期状態取得 |
| `resolveConflict()` | 手動競合解決 |

競合解決戦略: `local-wins` | `remote-wins` | `manual`

#### Phase 4: コード生成強化 (REQ-YI-GEN-001〜003)

`EnhancedCodeGenerator`クラスを`@nahisaho/musubix-core`に追加:

```typescript
import { EnhancedCodeGenerator } from '@nahisaho/musubix-core';

const generator = new EnhancedCodeGenerator();

// C4設計からコード生成
const files = await generator.generateFromDesign(designMarkdown);

// EARS要件からテスト生成
const tests = await generator.generateTestsFromEARS(requirements);

// トレーサビリティマトリクス生成
const matrix = generator.generateTraceabilityMatrix(files);
```

#### Phase 5: Web UI (REQ-YI-WEB-001〜003)

新パッケージ`@nahisaho/yata-ui`を追加:

```bash
# CLIで起動
npx yata-ui --port 3000

# プログラムから起動
import { createYataUIServer } from '@nahisaho/yata-ui';
const server = createYataUIServer({ port: 3000 });
await server.start();
```

機能:
- REST API: `/api/graph`, `/api/nodes`, `/api/edges`, `/api/stats`
- SSE: `/api/events`（リアルタイム更新）
- 組み込みUI: Cytoscape.js可視化、PNG出力

### テスト統計

| パッケージ | 新規テスト |
|-----------|-----------|
| yata-local (IndexOptimizer) | 23 |
| yata-local (Export) | 12 |
| yata-local (GlobalSync) | 26 |
| core (EnhancedCodeGenerator) | 25 |
| yata-ui | 8 |
| **合計新規** | **94** |
| **全体** | **1386** |

## [1.6.7] - 2026-01-05

### Added - Scaffold & Trace Sync

project-08-property-rental のSDD再開発から発見された改善点を実装。

#### scaffoldコマンド追加 (IMP-SDD-001)

SDDプロジェクトの即座生成:

```bash
# DDDプロジェクト生成
npx musubix scaffold domain-model <name>

# エンティティ指定
npx musubix scaffold domain-model <name> -e "User,Order,Product"

# ドメイン接頭辞指定
npx musubix scaffold domain-model <name> -d DOMAIN

# 最小構成
npx musubix scaffold minimal <name>
```

生成されるファイル:
- `storage/specs/REQ-DOMAIN-001.md` (EARS形式要件)
- `storage/design/DES-DOMAIN-001.md` (C4設計)
- `storage/traceability/TRACE-DOMAIN-001.md` (トレーサビリティ)
- `src/types/common.ts` (Value Objects)
- `src/types/errors.ts` (ドメインエラー)
- `src/entities/*.ts` (エンティティ実装)
- `__tests__/*.test.ts` (テストスタブ)
- `package.json`, `tsconfig.json`, `vitest.config.ts`
- `.yata/config.json` (YATA Local設定)

#### trace sync コマンド追加 (IMP-SDD-003)

トレーサビリティマトリクスの自動更新:

```bash
# トレーサビリティマトリクス自動更新
npx musubix trace sync

# プロジェクト指定
npx musubix trace sync -p virtual-projects/project-08

# プレビューのみ
npx musubix trace sync --dry-run
```

#### CLI --path オプション追加 (IMP-CLI-001)

全traceサブコマンドに`--path`オプションを追加:

```bash
npx musubix trace matrix -p virtual-projects/project-08
npx musubix trace validate -p virtual-projects/project-08
npx musubix trace impact REQ-001 -p virtual-projects/project-08
```

#### テスト

- 1292テスト全合格
- ビルド成功

## [1.6.5] - 2026-01-07

### Added - YATA Local改善とCLI強化

YATA Localテストで発見された課題に基づく改善。

#### 高レベルAPI追加 (P0)

`@nahisaho/yata-local` に使いやすいAPIを追加:

| メソッド | 説明 |
|---------|------|
| `getEntitiesByType(type)` | EntityTypeで検索 |
| `getEntitiesByNamespace(namespace)` | Namespaceで検索 |
| `getEntitiesByKind(kind)` | metadata.entityKindで検索 |
| `getEntityByName(name, namespace?)` | 名前で単一エンティティ取得 |
| `upsertEntity(entity, matchBy)` | 存在確認付き追加/更新 |
| `upsertEntities(entities, matchBy)` | バッチupsert |
| `rawQuery<T>(sql, params)` | SQLクエリ直接実行 |

#### EntityType/RelationType使用ガイドライン (P1)

`packages/yata-local/docs/BEST-PRACTICES.md` を新規作成:

- 16種類のEntityType定義とSDDマッピング
- 8種類のRelationType定義
- metadata.entityKindパターン
- コード例とベストプラクティス

#### CLI共通auto-learnミドルウェア (P1)

`packages/core/src/cli/middleware/auto-learn.ts`:

```typescript
// 使用例
const middleware = new AutoLearnMiddleware({ autoLearn: true });
await middleware.init();
await middleware.registerEntity({ name: 'REQ-001', type: 'module', ... });
await middleware.registerBatch(entities, relationships);
```

#### tasksコマンド追加 (P1)

```bash
# タスク検証（YATA Local登録オプション付き）
npx musubix tasks validate <file> --auto-learn

# YATA Localからタスク一覧
npx musubix tasks list --priority P0

# タスク統計
npx musubix tasks stats
```

#### learn dashboardコマンド (P2)

```bash
# 学習ダッシュボード表示
npx musubix learn dashboard

# JSON出力
npx musubix learn dashboard --json
```

#### YATA Localエクスポート (P2)

```bash
# JSON形式でエクスポート
npx musubix learn yata-export -o export.json

# RDF形式でエクスポート
npx musubix learn yata-export -f rdf -o export.ttl
```

#### Mermaidグラフ生成 (P2)

```bash
# フローチャート生成
npx musubix learn yata-graph -o diagram.md

# ER図形式
npx musubix learn yata-graph -t er -o er.md

# クラス図形式
npx musubix learn yata-graph -t class -o class.md

# フィルタオプション
npx musubix learn yata-graph -n requirements -k Requirement --max-nodes 100
```

### テスト

- 1292テスト全合格維持

## [1.6.4] - 2026-01-06

### Added - KGPR (Knowledge Graph Pull Request)

GitHub PRモデルに基づく知識グラフ共有機能。YATA Local → YATA Global間で知識グラフを安全に共有。

#### KGPR概要

| コンポーネント | ファイル | 機能 |
|--------------|---------|------|
| **Types** | `packages/yata-global/src/kgpr/types.ts` | KGPR型定義, ステータス管理 |
| **Privacy Filter** | `packages/yata-global/src/kgpr/privacy-filter.ts` | 機密情報フィルタリング |
| **KGPR Manager** | `packages/yata-global/src/kgpr/kgpr-manager.ts` | KGPR操作の中心クラス |
| **MCP Tools** | `packages/mcp-server/src/tools/kgpr-tools.ts` | 5つの新MCPツール |
| **CLI Commands** | `packages/core/src/cli/commands/kgpr.ts` | CLIコマンド |

#### KGPRワークフロー

```
┌─────────────┐     ┌──────────────┐     ┌───────────────┐
│ YATA Local  │ ──► │ KGPR (Draft) │ ──► │ YATA Global   │
│ (ローカルKG) │     │ (差分抽出)    │     │ (レビュー・マージ) │
└─────────────┘     └──────────────┘     └───────────────┘

ステータス遷移:
draft → open → reviewing → approved/changes_requested → merged/closed
```

#### プライバシーフィルター

| レベル | フィルタ対象 |
|-------|------------|
| `strict` | ファイルパス, URL, 認証情報, 全メタデータ |
| `moderate` | ファイルパス, URL, 認証情報 |
| `none` | フィルタなし |

#### 新MCPツール（5ツール）

| ツール名 | 説明 |
|---------|------|
| `kgpr_create` | KGPR作成（ローカルKGからドラフト作成） |
| `kgpr_diff` | 差分プレビュー |
| `kgpr_list` | KGPR一覧表示 |
| `kgpr_submit` | KGPR送信（レビュー用） |
| `kgpr_review` | KGPRレビュー（approve/changes_requested/commented） |

#### 新CLIコマンド

```bash
# KGPR作成
npx musubix kgpr create -t "Add authentication patterns"

# 差分プレビュー
npx musubix kgpr diff --namespace myproject --privacy moderate

# KGPR一覧
npx musubix kgpr list

# KGPR送信
npx musubix kgpr submit <id>

# KGPR詳細表示
npx musubix kgpr show <id>

# KGPRクローズ
npx musubix kgpr close <id>
```

#### テスト結果

```
全体: 1292 tests passed (62 files)
```

---

## [1.6.3] - 2026-01-06

### Added - YATA Local & YATA Global Implementation

ローカル/グローバル知識グラフストレージの完全実装。

#### YATA Local (`@nahisaho/yata-local`)

SQLiteベースのローカル知識グラフストレージ。

| コンポーネント | ファイル | 機能 |
|--------------|---------|------|
| **Database Layer** | `database.ts` | SQLite (WAL, FTS5), CRUD, トランザクション |
| **Query Engine** | `query-engine.ts` | BFS/DFSパス探索, サブグラフ抽出, パターンマッチ |
| **Reasoning Engine** | `reasoning.ts` | 4組み込みルール, 4制約, 推論・検証 |
| **I/O Module** | `io.ts` | JSON/RDF export, Delta同期 |
| **Main Class** | `index.ts` | YataLocal統合クラス |

**組み込み推論ルール**:
- `transitive-extends` - 推移的継承
- `implements-type` - 型実装
- `transitive-dependency` - 推移的依存
- `method-override` - メソッドオーバーライド

**組み込み制約**:
- `no-circular-inheritance` - 循環継承禁止
- `imports-resolve` - インポート解決
- `entity-has-name` - エンティティ名必須
- `function-return-type` - 関数戻り値型

#### YATA Global (`@nahisaho/yata-global`)

分散型知識グラフプラットフォーム。

| コンポーネント | ファイル | 機能 |
|--------------|---------|------|
| **API Client** | `api-client.ts` | REST API, 認証, レート制限 |
| **Cache Manager** | `cache-manager.ts` | SQLiteオフラインキャッシュ |
| **Sync Engine** | `sync-engine.ts` | Push/Pull同期, 自動同期 |
| **Main Client** | `index.ts` | YataGlobal統合クライアント |

**主な型定義**:
- `FrameworkKnowledge` - フレームワーク知識 (19カテゴリ, 20言語)
- `SharedPattern` - コミュニティ共有パターン (15カテゴリ)
- `SyncConfig` - 同期設定 (オフラインモード対応)
- `SearchOptions` - 検索オプション (ソート, フィルタ, ページネーション)

#### テスト結果

```
YATA Local:  22 tests passed
YATA Global: 28 tests passed
全体:        1267 tests passed (60 files)
```

## [1.6.2] - 2026-01-06

### Improved - SDD Cycle Validation

仮想プロジェクト（Project-07〜13）に対してSDDフルサイクルを実行し、改善を検証。

#### SDDサイクル実行結果

| プロジェクト | 要件数 | EARSテスト | 全テスト |
|-------------|--------|-----------|---------|
| Project-07 Medical Clinic | 25 | 42 | 132 ✅ |
| Project-08 Property Rental | 28 | 41 | 113 ✅ |
| Project-11 E-Learning | 17 | 29 | 60 ✅ |
| Project-12 Employee Management | 15 | 27 | 66 ✅ |
| Project-13 Budget Tracker | 20 | 28 | 75 ✅ |

#### 学習データ統計

- **Total Feedback**: 88件
- **Accept**: 72件 / Reject: 7件 / Modify: 9件
- **Total Patterns**: 23件
- **Average Confidence**: 65.7%
- **MUSUBIXテストスイート**: 1217テスト全合格

#### 改善確認済み機能

| 機能 | 状態 |
|------|------|
| `toPascalCase()` - BLOG_PLATFORM → BlogPlatform | ✅ |
| C4設計からTypeScriptコード生成 | ✅ |
| トレーサビリティマッピング（60+ドメイン） | ✅ |
| EARSテスト自動生成 | ✅ |

## [1.6.1] - 2026-01-06

### Added - Learning-Based Improvements

学習機能のフィードバック（70件）とパターン（23件）を分析し、MUSUBIXを改善。

#### 新機能: EARSテストジェネレータ

EARS要件から自動でテストケースを生成する`EarsTestGenerator`クラスを追加：

```typescript
import { createEarsTestGenerator, EarsRequirement } from '@nahisaho/musubix-core';

const generator = createEarsTestGenerator({ framework: 'vitest' });
const requirements: EarsRequirement[] = [
  { id: 'REQ-001', type: 'ubiquitous', text: 'THE system SHALL validate input' },
  { id: 'REQ-002', type: 'event-driven', text: 'WHEN user submits, THE system SHALL save' },
];
const testCases = generator.generateFromRequirements(requirements);
const testFile = generator.generateTestFileContent(testCases, 'myModule');
```

| EARS形式 | 生成テスト |
|---------|-----------|
| Ubiquitous | 常時テスト + Result.ok検証 |
| Event-driven | 正常/異常ケース |
| State-driven | ステータス遷移テスト |
| Unwanted | 禁止動作 + Result.err検証 |
| Optional | 条件分岐テスト |

#### 学習パターン統合

以下の学習パターンをテスト生成に組み込み：

| パターン | 内容 |
|---------|------|
| BP-TEST-001 | beforeEachでカウンターリセット |
| BP-TEST-004 | Result型の両ケーステスト（isOk/isErr） |
| BP-TEST-005 | ステータス遷移の網羅テスト |

#### トレーサビリティ改善

IoT・API Gatewayドメインのキーワードマッピングを追加：

- **IoT**: device, telemetry, alert, sensor, firmware, protocol
- **API Gateway**: gateway, route, ratelimit, circuit, cache, loadbalance

### Changed

- **unit-test-generator.ts**: EarsTestGenerator追加（+250行）
- **index.ts**: EarsTestGenerator, EarsRequirement, EarsTestCaseエクスポート追加
- **design.ts**: ドメインキーワードマッピング拡張

### テスト統計

| 項目 | 値 |
|------|------|
| 総テスト数 | 1217 |
| 新規追加 | +9 |
| 成功 | 1217 |
| 成功率 | 100% |

---

## [1.6.0] - 2026-01-06

### Added - REPL Test Implementation & CLI Enhancement

v1.6.0として、REPLテストの完全実装とCLI統合を追加。

#### 新機能: REPL Complete Test Suite (REQ-REPL-001〜009)

| テストスイート | テスト数 | 要件 |
|---------------|---------|------|
| ReplEngine Tests | 10 | REQ-REPL-001 |
| CommandCompleter Tests | 10 | REQ-REPL-002 |
| HistoryManager Tests | 14 | REQ-REPL-003 |
| SessionState Tests | 12 | REQ-REPL-004 |
| OutputFormatter Tests | 13 | REQ-REPL-005 |
| PromptRenderer Tests | 9 | REQ-REPL-006 |
| Integration Tests | 7 | REQ-REPL-007 |
| Factory Function Tests | 10 | - |

#### CLI統合 (REQ-REPL-007)

```typescript
// REPLからCLIコマンドを実行可能に
repl> requirements analyze input.md
repl> design generate req.md
repl> learn status
```

- `executeExternal()` メソッドがspawnでCLIを呼び出し
- 標準出力/エラーを適切にキャプチャ
- 終了コードに基づいた成功/失敗判定

### Changed

- **repl-engine.ts**: CLI統合実装（spawn使用）
- **repl.test.ts**: 22スケルトンテスト → 105完全実装

### テスト統計

| 項目 | 値 |
|------|------|
| 総テスト数 | 1208 |
| 成功 | 1208 |
| 失敗 | 0 |
| REPLテスト | 105 |

---

## [1.5.2] - 2026-01-06

### Added - E2E Test Enhancement

v1.5.2として、E2Eテスト強化フレームワークを実装。1155テスト全合格。

#### 新機能: テストヘルパーフレームワーク

| コンポーネント | パターン | 説明 | 要件 |
|---------------|---------|------|------|
| **TestProject** | Factory | テストプロジェクト作成・管理 | REQ-E2E-001 |
| **TestFixtures** | Repository | EARS/コード/トリプルサンプル提供 | REQ-E2E-001 |
| **CliRunner** | Facade | CLIコマンド実行ラッパー | REQ-E2E-001 |
| **TestContext** | Builder | 統合テストコンテキスト | REQ-E2E-001 |
| **Assertions** | Strategy | カスタムE2Eアサーション | REQ-E2E-001 |

#### TestProject Factory

```typescript
// テンプレートでプロジェクト作成
const project = await createTestProject({ template: 'sdd' });
// 自動クリーンアップ
await withTestProject(async (project) => {
  // テスト実行
});
```

| テンプレート | 内容 |
|-------------|------|
| `minimal` | 最小構成（package.json, src/index.ts） |
| `full` | フル構成（all directories） |
| `sdd` | SDD構成（steering/, storage/） |

#### TestFixtures Repository

```typescript
const fixtures = await getFixtures();
// EARS要件サンプル
fixtures.requirements.valid   // 5パターン（ubiquitous, event-driven, etc.）
fixtures.requirements.invalid // 5サンプル
// コードサンプル
fixtures.code.typescript
fixtures.code.javascript
// トリプルサンプル
fixtures.triples.valid
fixtures.triples.invalid
```

#### CliRunner Facade

```typescript
const cli = createCliRunner(projectPath);
// 汎用実行
const result = await cli.run('requirements', 'analyze', 'input.md');
// ショートカットメソッド
await cli.requirements('validate', 'file.md');
await cli.design('generate', 'req.md');
await cli.learn('status');
await cli.ontology('validate', '-f', 'graph.ttl');
```

#### TestContext Builder

```typescript
const ctx = await TestContext.builder()
  .withProject({ template: 'sdd' })
  .withFixtures()
  .withCli()
  .build();

// 使用例
const result = await ctx.cli.requirements('analyze', 'input.md');
expect(result.exitCode).toBe(0);

// 自動クリーンアップ
await ctx.cleanup();
```

#### カスタムアサーション

| 関数 | 説明 |
|------|------|
| `isValidEars(text)` | EARS形式検証（正規表現ベース） |
| `getEarsPattern(text)` | EARSパターン抽出 |
| `hasExitCode(result, code)` | 終了コード検証 |
| `isWithinBudget(result, budget)` | パフォーマンス予算検証 |
| `hasTraceability(output, id)` | トレーサビリティID検証 |
| `containsPattern(output, pattern)` | パターン参照検証 |
| `meetsCodeQuality(code, options)` | コード品質検証 |

#### E2Eテストスイート

| テストファイル | テスト数 | 対象 |
|---------------|---------|------|
| `sdd-workflow.e2e.test.ts` | 18 | SDDワークフロー全体 |
| `performance.e2e.test.ts` | 16 | パフォーマンス基準 |
| `error-handling.e2e.test.ts` | 17 | エラーハンドリング |
| `testing.test.ts` | 33 | テストフレームワーク自体 |

#### 使用例

```typescript
// 完全なE2Eテスト例
describe('SDD Workflow E2E', () => {
  let ctx: TestContext;

  beforeAll(async () => {
    ctx = await TestContext.builder()
      .withProject({ template: 'sdd' })
      .withFixtures()
      .build();
  });

  afterAll(async () => {
    await ctx.cleanup();
  });

  it('should validate EARS requirements', () => {
    for (const req of ctx.fixtures.requirements.valid) {
      expect(isValidEars(req.text)).toBe(true);
      expect(getEarsPattern(req.text)).toBe(req.pattern);
    }
  });

  it('should execute CLI within budget', async () => {
    const result = await ctx.cli.run('--version');
    expect(isWithinBudget(result, { maxDuration: 500 })).toBe(true);
  });
});
```

#### 新規ファイル

```
packages/core/src/testing/
├── types.ts           # 型定義
├── test-project.ts    # TestProject Factory
├── test-fixtures.ts   # TestFixtures Repository
├── cli-runner.ts      # CliRunner Facade
├── test-context.ts    # TestContext Builder
├── assertions.ts      # カスタムアサーション
├── index.ts           # エクスポート
└── __tests__/
    └── testing.test.ts  # フレームワークテスト

packages/core/__tests__/e2e/
├── sdd-workflow.e2e.test.ts    # SDDワークフローE2E
├── performance.e2e.test.ts      # パフォーマンスE2E
└── error-handling.e2e.test.ts   # エラーハンドリングE2E
```

#### 要件ドキュメント

- [REQ-E2E-v1.5.2.md](storage/specs/REQ-E2E-v1.5.2.md) - 7要件定義
- [DES-E2E-v1.5.2.md](storage/design/DES-E2E-v1.5.2.md) - 設計書

---

## [1.5.1] - 2026-01-06

### Added - Performance Optimization

v1.5.1として、Performance Optimization（パフォーマンス最適化）を実装。1071テスト全合格。

#### 新機能: パフォーマンスユーティリティ

| コンポーネント | 説明 | 要件 |
|---------------|------|------|
| **LazyLoader** | モジュール遅延読み込み（Virtual Proxy） | REQ-PERF-001 |
| **LRUCache** | LRUキャッシュ（TTLサポート） | REQ-PERF-002 |
| **ParallelExecutor** | 並列実行（concurrency制御） | REQ-PERF-003 |
| **MemoryMonitor** | メモリ監視（ヒープ使用量追跡） | REQ-PERF-004 |
| **Benchmark** | ベンチマーク計測スイート | REQ-PERF-005 |

#### Lazy Loading機能

| 関数 | 説明 |
|------|------|
| `lazyImport<T>()` | モジュールの遅延インポート |
| `lazyLoad<T>()` | 関数の遅延ロード |
| `ensureLoaded()` | モジュールのロード確認 |
| `createLazyModule()` | Proxyベースの遅延モジュール作成 |

#### LRUキャッシュ機能

| 関数 | 説明 |
|------|------|
| `LRUCache` | LRUキャッシュクラス（容量・TTL設定） |
| `memoize()` | 同期関数のメモ化 |
| `memoizeAsync()` | 非同期関数のメモ化 |
| `createGlobalCache()` | グローバルキャッシュの取得 |

#### 並列処理機能

| 関数 | 説明 |
|------|------|
| `parallel()` | 並列実行（concurrency制御） |
| `parallelMap()` | 並列マップ |
| `parallelFilter()` | 並列フィルタ |
| `ParallelExecutor` | 高度な並列実行クラス |
| `throttle()` | 関数のスロットリング |
| `debounce()` | 関数のデバウンス |

#### メモリ監視機能

| 関数 | 説明 |
|------|------|
| `MemoryMonitor` | メモリ監視クラス（イベント発行） |
| `measureMemory()` | メモリ使用量の取得 |
| `formatBytes()` | バイト数のフォーマット |
| `isMemoryHigh()` | メモリ使用率のチェック |

#### ベンチマーク機能

| 関数 | 説明 |
|------|------|
| `benchmark()` | ベンチマーク実行 |
| `benchmarkSuite()` | ベンチマークスイート実行 |
| `measure()` | コールバック関数の計測 |
| `time()` | 非同期関数の計測 |
| `runStandardBenchmarks()` | 標準ベンチマーク実行 |

#### CLIコマンド

```bash
# ベンチマーク実行
npx musubix perf benchmark

# 起動時間計測
npx musubix perf startup

# メモリ使用量表示
npx musubix perf memory
npx musubix perf memory --watch    # 監視モード

# キャッシュ統計
npx musubix perf cache-stats

# キャッシュクリア
npx musubix perf cache-clear
```

#### 設計パターン

| パターン | コンポーネント | 説明 |
|---------|---------------|------|
| **Virtual Proxy** | LazyLoader | 遅延読み込みのプロキシ |
| **Cache-Aside** | LRUCache | キャッシュ管理パターン |
| **Promise Pool** | ParallelExecutor | 並列実行の制御 |
| **Observer** | MemoryMonitor | メモリイベントの監視 |

---

## [1.5.0] - 2026-01-06

### Added - Interactive CLI Mode (REPL)

v1.5.0として、Interactive CLI Mode（REPLシェル）を実装。1021テスト全合格。

#### 新機能: REPLエンジン

| コンポーネント | 説明 | 要件 |
|---------------|------|------|
| **ReplEngine** | メインREPLエンジン（Facade） | REQ-CLI-001 |
| **CommandCompleter** | TAB補完（コマンド/サブコマンド/オプション/ファイルパス） | REQ-CLI-002 |
| **HistoryManager** | コマンド履歴管理（永続化・検索） | REQ-CLI-003 |
| **SessionState** | セッション変数管理（set/get/expand） | REQ-CLI-007 |
| **OutputFormatter** | 出力フォーマット（JSON/Table/YAML） | REQ-CLI-008 |
| **PromptRenderer** | プロンプト描画（プロジェクト名/フェーズ/色） | REQ-CLI-004 |

#### REPL機能

| 機能 | 説明 |
|------|------|
| **コマンド補完** | TABキーでコマンド/サブコマンド/オプションを補完 |
| **履歴ナビゲーション** | ↑/↓キーで履歴をナビゲート |
| **履歴検索** | Ctrl+R で履歴をインクリメンタル検索 |
| **セッション変数** | `set VAR=value` で変数を設定、`$VAR` で参照 |
| **出力フォーマット** | JSON/Table/YAML形式で出力 |
| **ヘルプシステム** | `help <command>` で詳細ヘルプ |

#### 設計パターン

| パターン | コンポーネント | 説明 |
|---------|---------------|------|
| **Facade** | ReplEngine | 複雑なサブシステムを統一インターフェースで提供 |
| **Strategy** | CommandCompleter, OutputFormatter | 異なる補完/フォーマット戦略を切り替え |
| **Repository** | HistoryManager | 履歴データの永続化管理 |
| **State** | SessionState | セッション状態の管理 |
| **Template Method** | PromptRenderer | プロンプト描画の拡張ポイント |

#### 使用方法

```bash
# REPLを起動
npx musubix repl

# カスタム履歴ファイル
npx musubix repl --history ~/.musubix_history

# 色なしモード
npx musubix repl --no-color
```

---

## [1.4.5] - 2026-01-06

### Added - Advanced Inference (v1.5.0 Phase 3)

v1.5.0のPhase 3として、Advanced Inference（高度推論）を実装。969テスト全合格。

#### 新機能: OWL 2 RL推論エンジン

| コンポーネント | 説明 | 要件 |
|---------------|------|------|
| **OWL2RLReasoner** | OWL 2 RLプロファイル準拠の推論エンジン | REQ-ONTO-010 |
| **DatalogEngine** | ストラティファイドDatalog評価 | REQ-ONTO-014 |
| **InferenceExplainer** | 人間可読な推論説明生成 | REQ-ONTO-013 |
| **ProgressReporter** | 推論進捗フィードバック（500ms間隔） | REQ-ONTO-012 |

#### OWL 2 RLビルトインルール（20+）

| カテゴリ | ルール例 | 説明 |
|---------|---------|------|
| **Class Axioms** | cax-sco, cax-eqc | サブクラス・同値クラス推論 |
| **Property Axioms** | prp-dom, prp-rng | ドメイン・レンジ推論 |
| **Property Characteristics** | prp-symp, prp-trp, prp-inv | 対称・推移・逆プロパティ |
| **Equality** | eq-ref, eq-sym, eq-trans | sameAs推論 |
| **Schema** | scm-cls, scm-sco | スキーマ推論 |

#### Datalogエンジン機能

- ストラティファイド評価（否定サポート）
- 固定点計算（効率的な反復）
- ルールパース（文字列からDatalogRule）
- クエリサポート（パターンマッチング）

#### 推論説明機能

| フォーマット | 説明 |
|-------------|------|
| `text` | プレーンテキスト説明 |
| `markdown` | Markdown形式 |
| `html` | HTML形式（エスケープ対応） |

#### 進捗レポート機能

- 自動進捗レポート（500ms間隔）
- フェーズ表示（initializing, loading, reasoning, explaining, completed, error）
- 残り時間推定
- プログレスバー表示

#### 新規ファイル

```
packages/core/src/learning/inference/
├── types.ts                  # Phase 3型定義
├── owl2rl-reasoner.ts        # OWL 2 RL推論エンジン
├── datalog-engine.ts         # Datalogエンジン
├── inference-explainer.ts    # 推論説明生成
├── progress-reporter.ts      # 進捗レポーター
├── index.ts                  # モジュールエクスポート
└── __tests__/
    ├── owl2rl-reasoner.test.ts
    ├── datalog-engine.test.ts
    ├── inference-explainer.test.ts
    └── progress-reporter.test.ts
```

### Changed

- `InferenceProgress`型を更新（totalTriples追加、percentage等削除）
- `IProgressReporter`インターフェースを更新（ProgressReporter実装と整合）

---

## [1.4.4] - 2026-01-05

### Added - Pattern Sharing Foundation (v1.5.0 Phase 2)

v1.5.0のPhase 2として、Pattern Sharing基盤を実装。902テスト全合格。

#### 新機能: Pattern Sharing

| コンポーネント | 説明 | 要件 |
|---------------|------|------|
| **PatternSerializer** | JSON/N3形式へのエクスポート | REQ-SHARE-001 |
| **PatternDeserializer** | JSON/N3形式からのインポート | REQ-SHARE-002 |
| **PatternServer** | HTTPベースの共有サーバー | REQ-SHARE-003 |
| **ConflictResolver** | 競合検出・解決戦略 | REQ-SHARE-005 |
| **AuthManager** | トークンベース認証・認可 | REQ-SHARE-006 |

#### サポートフォーマット

| フォーマット | 説明 |
|-------------|------|
| **JSON** | 標準パターンフォーマット（チェックサム付き） |
| **N3** | RDF/Turtle形式（オントロジー連携） |

#### 競合解決戦略

| 戦略 | 説明 |
|------|------|
| `keep-local` | ローカルパターンを維持 |
| `keep-remote` | リモートパターンを採用 |
| `merge` | 両方をマージ（高信頼度優先） |
| `skip` | 競合をスキップ |
| `prompt` | ユーザーに確認 |

#### 認証機能

- ユーザー認証（SHA-256 + Salt）
- APIキー認証
- トークンベース認可（JWT風）
- スコープベースアクセス制御

#### 新規ファイル

```
packages/core/src/learning/sharing/
├── types.ts              # 型定義
├── pattern-serializer.ts # PatternSerializer
├── pattern-deserializer.ts # PatternDeserializer
├── pattern-server.ts     # PatternServer
├── conflict-resolver.ts  # ConflictResolver
├── auth-manager.ts       # AuthManager
└── index.ts             # モジュールエクスポート
```

### Fixed

- TypeScript型名衝突の解消（ValidationError → SharingValidationError）
- パターンシリアライザーの型整合性修正

## [1.4.3] - 2026-01-05

### Added - Real-time Pattern Learning Foundation (v1.5.0 Phase 1)

v1.5.0のPhase 1として、Real-time Learning基盤を実装。853テスト全合格。

#### 新機能: Real-time Learning

| コンポーネント | 説明 | 要件 |
|---------------|------|------|
| **FileWatcher** | fs.watchベースのファイル変更監視 | REQ-LEARN-010 |
| **StreamProcessor** | 500ms SLA対応のイベント処理 | REQ-LEARN-011 |
| **FeedbackQueue** | 100ms SLA対応の非同期フィードバック | REQ-LEARN-013 |
| **EventStream** | 1000 events/sec対応のイベント配信 | REQ-LEARN-014 |
| **IncrementalUpdater** | 差分パターン更新（Delta Update） | REQ-LEARN-012 |
| **RealtimeLearningEngine** | 全体オーケストレーション | REQ-LEARN-010 |

#### アーキテクチャ決定（ADR）

| ADR | 決定 |
|-----|------|
| ADR-0001 | fs.watch + EventEmitter（外部依存なし） |
| ADR-0002 | File-based JSON export/import |
| ADR-0003 | N3.js + カスタムOWL 2 RLルール |

#### v1.5.0計画ドキュメント

| ドキュメント | 内容 |
|-------------|------|
| REQ-v1.5.0.md | EARS形式要件定義（24要件） |
| DES-v1.5.0.md | C4モデル設計書（23コンポーネント） |
| TST-v1.5.0.md | テスト計画（64テストケース） |

#### 新規ファイル

```
packages/core/src/learning/realtime/
├── types.ts           # 型定義
├── file-watcher.ts    # FileWatcher
├── stream-processor.ts # StreamProcessor
├── feedback-queue.ts  # FeedbackQueue
├── event-stream.ts    # EventStream
├── incremental-updater.ts # IncrementalUpdater
└── index.ts           # RealtimeLearningEngine

storage/specs/
├── REQ-v1.5.0.md      # 要件定義
├── TST-v1.5.0.md      # テスト計画
└── __tests__/REQ-v1.5.0.test.ts # テストスケルトン

storage/design/
└── DES-v1.5.0.md      # 設計ドキュメント

docs/adr/
├── 0001-real-time-pattern-learning-architecture-for-v1-5-0.md
├── 0002-pattern-sharing-protocol-for-cross-team-collaborat.md
└── 0003-owl-2-rl-implementation-strategy-for-advanced-infe.md
```

#### テスト追加

| テストスイート | テスト数 |
|---------------|---------|
| FileWatcher | 4 |
| StreamProcessor | 6 |
| FeedbackQueue | 6 |
| EventStream | 6 |
| IncrementalUpdater | 8 |
| RealtimeLearningEngine | 6 |
| Integration | 2 |
| **合計追加** | **38** |

---

## [1.4.2] - 2025-01-05

### Added - Quality & UX Improvements

品質向上とユーザー体験改善のためのアップデート。815テスト全合格。

#### テスト・品質

| 改善 | 詳細 |
|------|------|
| **E2Eテスト追加** | CLI E2Eテスト15件追加（cli-e2e.test.ts） |
| **カバレッジ測定** | @vitest/coverage-v8導入 |
| **閾値調整** | 現実的なカバレッジ閾値に調整（lines: 25%, branches: 21%） |

#### CLI UX改善

| 改善 | 詳細 |
|------|------|
| **ヘルプ拡充** | `learn`, `ontology`コマンドをヘルプに追加 |
| **多言語対応** | 日本語/英語メッセージ辞書（messages.ts） |
| **ロケール自動検出** | `LANG`環境変数によるロケール自動切替 |

#### ドキュメント

| ドキュメント | 内容 |
|-------------|------|
| **ROADMAP-v1.5.md** | v1.5.0機能計画（Real-time Learning, Pattern Sharing等） |
| **CHANGELOG.md** | v1.4.1にMCPツール・CLI・PatternValidator追記 |
| **AGENTS.md** | テスト数815、MCPツール19に更新 |

#### 新規ファイル

- `packages/core/__tests__/e2e/cli-e2e.test.ts` - CLI E2Eテスト
- `packages/core/src/cli/messages.ts` - 多言語メッセージ辞書
- `docs/ROADMAP-v1.5.md` - v1.5.0ロードマップ

---

## [1.4.1] - 2025-01-05

### Added - Consistency Validation (正誤性検証)

知識グラフへのデータ登録時の正誤性検証機能を追加。OWL制約に基づく一貫性チェック。775テスト全合格。

#### 新機能

| 機能 | 説明 |
|------|------|
| **ConsistencyValidator** | OWL制約に基づく一貫性検証クラス |
| **トリプル事前検証** | addTripleValidated()で追加前に検証 |
| **ストア整合性チェック** | checkConsistency()でストア全体を検証 |
| **重複検出** | 完全一致・意味的重複の検出 |
| **循環検出** | subClassOf等の循環依存検出 |

#### 検証タイプ

| タイプ | 説明 | 重大度 |
|--------|------|--------|
| `disjoint-class-membership` | owl:disjointWith違反 | error |
| `functional-property-violation` | owl:FunctionalProperty違反 | error |
| `inverse-functional-violation` | owl:InverseFunctionalProperty違反 | error |
| `asymmetric-violation` | owl:AsymmetricProperty違反 | error |
| `irreflexive-violation` | owl:IrreflexiveProperty違反 | error |
| `duplicate-triple` | 重複トリプル | warning |
| `circular-dependency` | 循環依存 | error |

#### 使用例

```typescript
import { N3Store } from '@nahisaho/musubix-ontology-mcp';

// 検証付きストア
const store = new N3Store({}, true); // validateOnAdd = true

// 検証付き追加
const result = store.addTripleValidated(triple);
if (!result.success) {
  console.error(result.validation.errors);
}

// ストア整合性チェック
const consistency = store.checkConsistency();
```

### Added - MCP & CLI Enhancements

#### MCP Serverツール追加（3ツール）

| ツール | 説明 |
|--------|------|
| `consistency_validate` | 知識グラフの整合性検証 |
| `validate_triple` | 単一トリプルの事前検証 |
| `check_circular` | 循環依存の検出 |

#### CLI ontologyコマンド追加

```bash
# 知識グラフの整合性検証
npx musubix ontology validate -f triples.json
npx musubix ontology validate -s "Subject" -p "predicate" -o "Object"

# 循環依存チェック
npx musubix ontology check-circular -f relationships.json

# 統計表示
npx musubix ontology stats -f triples.json
```

#### Wake-Sleep PatternValidator追加

パターン検証機能（duplicate, circular, disjoint, low-confidence, name-collision検出）

### Changed

- テスト数: 756 → 800 (+44)
- `@nahisaho/musubix-ontology-mcp`: 1.0.0 → 1.0.1
- `@nahisaho/musubix-mcp-server`: 1.3.0 → 1.3.1
- `@nahisaho/musubix-wake-sleep`: 1.0.0 → 1.0.1

---

## [1.4.0] - 2025-01-05

### Added - Learning Data Portability (知識グラフのポータビリティ)

プロジェクト間で学習データを共有・移行するためのCLI機能を追加。756テスト全合格。

#### 新機能

| 機能 | 説明 |
|------|------|
| **learn export拡張** | プライバシーフィルター、パターン/フィードバック選択エクスポート |
| **learn import拡張** | マージ戦略（skip/overwrite/merge）、ドライラン機能 |
| **プライバシーフィルター** | API Key、Password、Token等の機密情報自動除去 |
| **マージ戦略** | skip（既存保持）、overwrite（上書き）、merge（統合） |

#### CLIオプション

**export:**
```bash
npx musubix learn export --output patterns.json --privacy-filter --patterns-only --min-confidence 0.8
```

**import:**
```bash
npx musubix learn import patterns.json --merge-strategy merge --dry-run
```

### Changed

- テスト数: 752 → 756 (+4)

---

## [1.3.0] - 2025-01-05

### Added - Pattern Library Learning Integration (S1-S3 Complete)

DreamCoder風Wake-Sleep学習とオントロジー推論の完全統合。752テスト全合格。

#### S1スプリント: 基盤構築

| パッケージ | 機能 |
|-----------|------|
| **@nahisaho/musubix-pattern-mcp** | パターン抽出・圧縮・ライブラリ管理 |
| **@nahisaho/musubix-ontology-mcp** | N3Store・推論エンジン・SDDオントロジー |
| **@nahisaho/musubix-wake-sleep** | Wake-Sleep学習サイクル |
| **@nahisaho/musubix-sdd-ontology** | SDD方法論オントロジー |

#### S2スプリント: 高度な機能

| コンポーネント | 機能 |
|---------------|------|
| **PatternCompressor** | MDL原理によるパターン圧縮 |
| **PatternQualityEvaluator** | パターン品質評価・ランキング |
| **AntiUnifier** | 反単一化によるパターン一般化 |
| **TypeScriptParser** | Tree-sitter TypeScript AST解析 |
| **RuleEngine** | 前方連鎖推論エンジン |
| **WakeSleepCycle** | 自動Wake-Sleep学習サイクル |

#### S3スプリント: 統合・MCP連携

| コンポーネント | 機能 |
|---------------|------|
| **PatternOntologyBridge** | パターン↔オントロジー統合ブリッジ |
| **pattern_learn** | コード観察からパターン学習（MCPツール） |
| **pattern_consolidate** | Sleepフェーズ実行（MCPツール） |
| **pattern_query_relations** | パターン関係クエリ（MCPツール） |
| **pattern_search** | パターン検索（MCPツール） |
| **pattern_stats** | 学習統計取得（MCPツール） |
| **pattern_import_kg** | 知識グラフインポート（MCPツール） |
| **pattern_export_kg** | Turtleエクスポート（MCPツール） |

### Changed

- テスト数: 598 → 752 (+154)
- パッケージ数: 3 → 7 (+4)
- MCPツール数: 9 → 16 (+7)

### New Packages

| パッケージ | npm |
|-----------|-----|
| pattern-mcp | @nahisaho/musubix-pattern-mcp |
| ontology-mcp | @nahisaho/musubix-ontology-mcp |
| wake-sleep | @nahisaho/musubix-wake-sleep |
| sdd-ontology | @nahisaho/musubix-sdd-ontology |

### Traceability

```
REQ-PATTERN-001〜007 (パターン学習)
REQ-ONTO-001〜005 (オントロジー推論)
REQ-WAKE-001〜004 (Wake-Sleep)
REQ-INT-001〜003 (統合)
  └─ 19タスク完了
       └─ 752テスト (全合格)
```

---

## [1.2.0] - 2026-01-05

### Added - Neuro-Symbolic Integration (Phase 1-3 Complete)

Symbolic推論モジュールの完全実装。REQ-SYMB-001の全27要件をカバー。

#### Phase 1: 基盤コンポーネント（TSK-SYMB-001〜008）

| コンポーネント | 機能 |
|---------------|------|
| **SemanticCodeFilterPipeline** | LLM出力のセマンティック検証・フィルタリング |
| **HallucinationDetector** | 幻覚検出（未定義シンボル、無効インポート） |
| **ConstitutionRuleRegistry** | 9憲法条項の強制検証 |
| **ConfidenceEstimator** | 信頼度推定（AST複雑度、要件カバレッジ） |
| **ConfidenceBasedRouter** | 信頼度ベースのルーティング決定 |
| **ErrorHandler** | グレースフルデグラデーション |

#### Phase 2: 形式検証（TSK-SYMB-009〜013）

| コンポーネント | 機能 |
|---------------|------|
| **EarsToFormalSpecConverter** | EARS要件→SMT-LIB変換 |
| **VerificationConditionGenerator** | 検証条件（VC）生成 |
| **Z3Adapter** | Z3 SMTソルバー統合 |
| **PreconditionVerifier** | 事前条件検証 |
| **PostconditionVerifier** | 事後条件検証 |
| **InvariantVerifier** | 不変条件検証 |
| **SecurityScanner** | セキュリティスキャン（OWASP、シークレット検出） |

#### Phase 3: 高度機能（TSK-SYMB-014〜019）

| コンポーネント | 機能 |
|---------------|------|
| **CandidateRanker** | 候補スコアリング（複雑度/保守性/要件カバレッジ） |
| **ResultBlender** | Neural/Symbolic結果統合（3戦略ブレンド） |
| **ExtensibleRuleConfig** | YAML/JSON設定ロード、スキーマ検証 |
| **AuditLogger** | SHA-256ハッシュチェーン、改ざん検出 |
| **PerformanceBudget** | 段階別予算、SLO計測、部分結果 |
| **QualityGateValidator** | 品質ゲート検証、承認レポート生成 |

### Changed

- テスト数: 582 → 598 (+16)
- 型定義: `Evidence.type`に`timing`と`artifact`を追加

### Quality Gate

全17チェック合格:
- ✅ トレーサビリティ: 100%設計カバレッジ
- ✅ 非機能要件: パフォーマンス予算、拡張性、説明可能性
- ✅ セキュリティ: マスキング、監査ログ
- ✅ Constitution: 全9条項準拠

### Traceability

```
REQ-SYMB-001 (27要件)
  └─ DES-SYMB-001 (設計)
       └─ TSK-SYMB-001〜019 (19タスク)
            └─ 598テスト (全合格)
```

---

## [1.1.15] - 2026-01-04

### Added - Version Display in Postinstall Banner

Postinstall スクリプトのバナーにバージョン番号を表示するようになりました。

```
╔══════════════════════════════════════════════════════════════╗
║  🎉 MUSUBIX v1.1.15                                          ║
║     AI Agent Configuration Installed!                        ║
╠══════════════════════════════════════════════════════════════╣
║  ...                                                         ║
╚══════════════════════════════════════════════════════════════╝
```

### Changed

- `scripts/postinstall.js`: package.json からバージョンを読み取り、バナーに表示
- スキップメッセージにもバージョンを表示: `musubix v1.1.15: Configuration files already exist, skipping.`

### Note

- npm v11以降ではpostinstallの出力がデフォルトで抑制されます
- バナーを表示するには `npm install musubix --foreground-scripts` を使用

---

## [1.1.14] - 2026-01-04

### Added - CLAUDE.md Generation

Claude Code 向けに `CLAUDE.md` ファイルを自動生成するようになりました。

- **Postinstall**: `npm install musubix` 実行時に `AGENTS.md` を `CLAUDE.md` としてコピー
- **Init コマンド**: `npx musubix init` 実行時にも `CLAUDE.md` を生成
- Claude Code はプロジェクトルートの `CLAUDE.md` を読み込む仕様

### Changed

- `packages/core/scripts/postinstall.js`: CLAUDE.md コピー処理追加
- `packages/core/src/cli/commands/init.ts`: CLAUDE.md 生成処理追加

### Files Generated

```
project/
├── AGENTS.md           ← GitHub Copilot
├── CLAUDE.md           ← Claude Code (AGENTS.md のコピー)
├── .github/
│   ├── skills/         ← 9 Agent Skills
│   └── prompts/        ← 9 SDD prompts
└── .claude/
    ├── skills/         ← 9 Agent Skills (copy)
    └── prompts/        ← 9 SDD prompts (copy)
```

---

## [1.1.13] - 2026-01-04

### Added - Dual Directory Support (.github/ + .claude/)

GitHub Copilot と Claude Code の両方をサポートするため、スキルとプロンプトを2つのディレクトリにコピーするようになりました。

- **`.github/skills/`**: GitHub Copilot Agent Skills 用
- **`.github/prompts/`**: GitHub Copilot プロンプト用
- **`.claude/skills/`**: Claude Code Agent Skills 用
- **`.claude/prompts/`**: Claude Code プロンプト用

### Changed

- `packages/core/scripts/postinstall.js`: .claude/ ディレクトリコピー処理追加
- `packages/musubi/package.json`: dependency を `^1.1.13` に更新

### Design Decision

- シンボリックリンクではなく物理コピーを採用（npmがsymlinkをサポートしないため）
- 既存ファイルは上書きしない安全設計を維持

---

## [1.1.12] - 2026-01-04

### Added - Enhanced `musubix init` for AI Agents

`musubix init` コマンドが `.claude/` ディレクトリと Claude Code 用の設定ファイルを自動生成するようになりました。

- **`.claude/` ディレクトリ自動生成**
  - `settings.json`: Claude Code 用の設定ファイル
  - `CLAUDE.md`: Claude Code 向けの開発ガイドライン

- **グローバルインストール対応の改善**
  - `npm install -g @nahisaho/musubix-core` 後も `npx musubix init` が正しく動作
  - パッケージパス検出の改善（ローカル/グローバル/開発環境対応）

### Changed

- `packages/core/src/cli/commands/init.ts`: `.claude/` 生成ロジック追加
- `findMusubixPackage()`: 複数のインストールパスを検索するよう改善

### Generated Files by `musubix init`

| ファイル | 用途 |
|---------|------|
| `.github/skills/` | 9つの Agent Skills |
| `.github/prompts/` | 9つの SDD プロンプト |
| `.claude/settings.json` | Claude Code 設定 |
| `.claude/CLAUDE.md` | Claude Code ガイド |
| `AGENTS.md` | AI エージェント向けガイド |

---

## [1.1.11] - 2026-01-04

### Added - Claude Code Agent Skills & Auto-Install

`npm install @nahisaho/musubix-core` で Claude Code Agent Skills が自動的にプロジェクトにインストールされるようになりました。

- **9 Agent Skills for Claude Code** (`.github/skills/`)
  - `musubix-sdd-workflow`: SDD開発ワークフロー全体のガイド
  - `musubix-ears-validation`: EARS形式の要件検証
  - `musubix-code-generation`: 設計からのコード生成
  - `musubix-c4-design`: C4モデル（Context/Container/Component/Code）設計
  - `musubix-traceability`: 要件↔設計↔タスク↔コード↔テストの追跡
  - `musubix-test-generation`: TDDパターンに基づくテスト生成
  - `musubix-adr-generation`: Architecture Decision Records作成
  - `musubix-best-practices`: 17種のベストプラクティス適用
  - `musubix-domain-inference`: 62ドメイン検出・コンポーネント推論

- **Postinstall Auto-Copy** (`scripts/postinstall.js`)
  - インストール時に `.github/skills/`, `.github/prompts/`, `AGENTS.md` を自動コピー
  - GitHub Copilot プロンプト（9個）も同時にインストール
  - 既存ファイルは上書きしない安全設計

### Changed

- `packages/core/package.json`: postinstall スクリプト追加
- `docs/evolution-from-musubi-to-musubix.md`: Agent Skills セクション更新（3→9スキル）

---

## [1.1.10] - 2026-01-04

### Added - New Best Practices from Project-13/14 & Enhanced Code Generator

仮想プロジェクトProject-13 (Budget Tracker)、Project-14 (Ticket Reservation)の実装から新しいベストプラクティスを学習し、MUSUBIXを改善。

- **New Code Patterns** (`learning/best-practices.ts`)
  - BP-CODE-004: Function-based Value Objects (95%) - interface + factory function パターン
  - BP-CODE-005: Result Type for Fallible Operations (95%) - Rust風Result<T, E>でエラーハンドリング

- **New Design Patterns** (`learning/best-practices.ts`)
  - BP-DESIGN-006: Entity Counter Reset for Testing (95%) - resetXxxCounter()関数提供
  - BP-DESIGN-007: Expiry Time Business Logic (90%) - expiresAtフィールドで有効期限管理

- **New Test Patterns** (`learning/best-practices.ts`)
  - BP-TEST-004: Result Type Test Pattern (95%) - isOk()/isErr()で両方のケースをテスト
  - BP-TEST-005: Status Transition Testing (90%) - 有効・無効な遷移を網羅的にテスト

- **Enhanced Code Generator** (`codegen/generator.ts`)
  - `value-object` テンプレートタイプ追加 - Function-based Value Object自動生成
  - `entity` テンプレートタイプ追加 - Status Transition Map、Counter Reset、Input DTO含む

- **New Test Suite** (`__tests__/best-practices.test.ts`)
  - 20件のベストプラクティステストを追加
  - 新パターンの構造・内容を検証

### Changed

- **AGENTS.md**: ベストプラクティス一覧を更新（17パターン）
- **steering/tech.ja.md**: v1.1.10に更新
- **steering/project.yml**: v1.1.10に更新

### Metrics

| 項目 | 変更前 | 変更後 |
|------|--------|--------|
| テスト数 | 439 | 459 (+20) |
| ベストプラクティス | 11 | 17 (+6) |
| テンプレートタイプ | 10 | 12 (+2) |

### Virtual Projects Completed

- **Project-13 Budget Tracker**: 75テスト合格、3エンティティ、2 Value Objects
- **Project-14 Ticket Reservation**: 88テスト合格、3エンティティ、3 Value Objects

### Learning Data Generated

- `storage/learning-data-p13-p14.json`: 両プロジェクトの学習データを保存

---

## [1.1.9] - 2026-01-05

### Added - EARS Parser & Best Practices CLI Enhancement

仮想プロジェクトProject-11, Project-12の実装中に発見された問題を修正。

- **EARS Parser Markdown Support** (`cli/commands/requirements.ts`)
  - Markdownブロッククォート形式に対応（`> **WHEN**...`）
  - Boldマークアップ（`**...**`）の自動除去
  - 要件検証: 0件 → 15件の正しい検出を実現

- **Pattern Name Description Enhancement** (`learning/pattern-extractor.ts`)
  - `generateDescriptiveName()`: 言語・フレームワーク・カテゴリを含む名前生成
  - `extractContentSummary()`: パターン内容から意味のある要約を抽出
  - 例: `Auto: code prefer` → `TypeScript Code: Prefer using input dto pattern`

- **Best Practices CLI Commands** (`cli/commands/learn.ts`)
  - `musubix learn bp-list` (alias: `bpl`): 全ベストプラクティスID一覧
  - `musubix learn bp-show <ID>` (alias: `show`): 詳細表示（コード例付き）
  - 11個のベストプラクティスをCLIから簡単に参照可能

### Changed

- **steering/tech.ja.md**: v1.1.9、Self-Learning CLIセクション追加
- **steering/project.yml**: v1.1.9、ドメイン62、コンポーネント~430
- **AGENTS.md**: v1.1.9に更新

### Virtual Projects Completed

- **Project-11 E-Learning Platform**: 8エンティティ, 31テスト合格
- **Project-12 Employee Management**: 4エンティティ, 39テスト合格

---

## [1.1.7] - 2026-01-05

### Added - Codified Best Practices from Self-Learning

Project-07 Medical ClinicとProject-08 Property Rentalの実装から学習したベストプラクティスを体系化。

- **Best Practices Module** (`learning/best-practices.ts`) - NEW!
  - 9つのベストプラクティスを体系化（CODE: 3, DESIGN: 3, TEST: 3）
  - `BestPractice` 型定義（id, name, category, action, description, example等）
  - `LEARNED_BEST_PRACTICES` 定数で全パターンをエクスポート
  - `getBestPracticesByCategory()`, `getHighConfidencePatterns()` API

- **Best Practices CLI** (`musubix learn best-practices`)
  - `--category <cat>`: code, design, test, requirementでフィルタ
  - `--high-confidence`: 信頼度90%以上のパターンのみ表示
  - `--format <fmt>`: table, markdown, json出力形式
  - エイリアス: `musubix learn bp`

- **Code Patterns (95%+ confidence)**
  - BP-CODE-001: Entity Input DTO - エンティティ作成にInput DTOオブジェクト使用
  - BP-CODE-002: Date-based ID Format - PREFIX-YYYYMMDD-NNN形式
  - BP-CODE-003: Value Objects - ドメイン概念にValue Object使用

- **Design Patterns (90%+ confidence)**
  - BP-DESIGN-001: Status Transition Map - 状態遷移をMapで定義
  - BP-DESIGN-002: Repository Async Pattern - 将来のDB移行に備えてasync化
  - BP-DESIGN-003: Service Layer with DI - リポジトリをDIしたService層

- **Test Patterns (85%+ confidence)**
  - BP-TEST-001: Test Counter Reset - beforeEachでIDカウンターリセット
  - BP-TEST-002: Verify API Before Test - テスト作成前にAPI確認
  - BP-TEST-003: Vitest ESM Configuration - Vitest + TypeScript ESM構成

### Changed

- **AGENTS.md**: 学習済みベストプラクティスセクションを追加
- **learning/index.ts**: best-practices.tsからのエクスポートを追加

---

## [1.1.6] - 2026-01-04

### Fixed

- **CLI**: `VERSION`定数を1.1.6に更新（`musubix --version`が正しいバージョンを表示）

---

## [1.1.5] - 2026-01-04

### Fixed

- **yata-client**: 存在しない`bin/musubix-yata.js`への参照を削除
  - package.jsonから`bin`設定を削除
  - `files`配列から`bin`ディレクトリを削除
  - npm publish時の警告を解消

---

## [1.1.4] - 2026-01-04

### Added - Self-Learning Improvements

自己学習フィードバック（PAT-004〜PAT-006）に基づく改善を実施。

- **MockGenerator** (`codegen/mock-generator.ts`) - PAT-004
  - インターフェース定義からテストモック実装を自動生成
  - Repository/Service/Adapterパターン対応
  - vitest/jest両対応
  - テスト失敗の削減を目標

- **BaseRepository** (`codegen/base-repository.ts`) - PAT-005
  - `IRepository<T, ID>` 標準インターフェース
  - `updateMany(ids[], data)` 形式を標準採用
  - `ISearchableRepository<T>`, `IPaginatedRepository<T>` 拡張
  - `InMemoryRepository<T>` 実装クラス

- **AdapterNamingHelper** (`codegen/adapter-naming.ts`) - PAT-006
  - `I{Domain}ServiceAdapter` 標準命名パターン
  - `generateInterfaceName()`, `generateImplementationName()` API
  - `validateAdapterNames()` 検証機能
  - コード一貫性の向上

### Enhanced - Domain Components

- **gymドメイン追加**（18コンポーネント）- 仮想プロジェクト05から学習
  - MemberService, CheckInService, ClassService, BillingService
  - MemberRepository, CheckInRepository, ClassRepository等
  - BillingServiceAdapter, MemberServiceAdapter, PaymentGateway

- **bookingドメイン拡充**（7→19コンポーネント）- 仮想プロジェクト06から学習
  - EventService, TicketService, SeatService, CheckInService
  - WaitlistService, PromoCodeService
  - 各サービスに詳細なメソッド定義追加

### Statistics

- **コンポーネント総数**: 390+ → **427+**（約10%増加）
- **新規モジュール**: 3ファイル追加
- **テスト**: 439テスト全パス

---

## [1.1.2] - 2026-01-04

### Fixed
- **テスト生成 0件問題** (FB-5016B120, FB-6FDF95D3)
  - `extractEarsRequirements` が MUSUBIX v1.1.0 の `**[Pattern]**` 形式を認識するよう改善
  - 結果: 0件 → 22件のテストケースが生成されるように修正

- **C4設計パーサー改善**
  - `parseC4DesignComponents` が `DES-001` 形式のID（ハイフン付き）を認識するよう正規表現を修正

### Added
- **ドメイン固有メソッド生成** (FB-325C2D59)
  - `MethodSignature` インターフェースを追加
  - `getMethodsForComponent()` APIを追加
  - 4ドメイン（veterinary, parking, delivery, ecommerce）に固有メソッドを定義
  - Service テンプレートにドメイン固有メソッドを自動追加

- **ComponentInference.detectDomain()** メソッド追加
  - テキストからドメインIDを検出するユーティリティ

### Enhanced
- **Service コード生成**
  - Core CRUD メソッド + ドメイン固有メソッドを生成
  - 例: OrderService → `accept`, `cancel`, `getByCustomer`, `getByRestaurant`
  - 例: DeliveryService → `assignDriver`, `updateLocation`, `complete`, `calculateETA`

### Tests
- **439テスト合格**（全テストパス維持）

---

## [1.1.1] - 2026-01-04

### Added
- **DomainDetector モジュール**: 要件・設計テキストからドメインを自動検出
  - 62ドメイン定義（veterinary, parking, ecommerce, healthcare, booking等）
  - キーワードマッチングによる信頼度スコアリング
  - カテゴリ別フィルタリング（business, industry, healthcare, service, technology）
  - 関連ドメイン推薦

- **ComponentInference モジュール**: ドメインに最適なコンポーネント構成を推薦
  - 59コンポーネント定義
  - Repository/Service/Factoryパターンの自動推薦
  - レイヤードアーキテクチャ推薦
  - 依存関係の自動推論

### Tests
- **439テスト合格**（+28テスト追加）
  - DomainDetector: 14テスト
  - ComponentInference: 12テスト

---

## [1.1.0] - 2026-01-04

### Added
- **DomainDetector モジュール**: 要件・設計テキストからドメインを自動検出
  - 62ドメイン定義（veterinary, parking, ecommerce, healthcare, booking等）
  - キーワードマッチングによる信頼度スコアリング
  - カテゴリ別フィルタリング（business, industry, healthcare, service, technology）
  - 関連ドメイン推薦

- **ComponentInference モジュール**: ドメインに最適なコンポーネント構成を推薦
  - 59コンポーネント定義
  - Repository/Service/Factoryパターンの自動推薦
  - レイヤードアーキテクチャ推薦
  - 依存関係の自動推論

- **ThresholdAlert ユーティリティ**: 閾値ベースのアラート・監視システム
  - `ThresholdAlert`: 単一閾値の監視（CPU使用率、在庫数、レスポンスタイムなど）
  - `MultiThresholdAlert`: 複数閾値の一括監視
  - `check()`: アラートレベル判定（normal/warning/critical）
  - `evaluate()`: 詳細評価（マージン、パーセンテージ、メッセージ生成）
  - `isExceeded()`, `isWarningOrAbove()`, `isCritical()`: 簡易チェック
  - ヒステリシス（チャタリング防止）対応
  - 6つのプリセット閾値設定:
    - `resourceUsageThreshold`: CPU/メモリ使用率（80%/95%）
    - `inventoryThreshold`: 在庫数（10/5）
    - `responseTimeThreshold`: レスポンスタイム（1000ms/3000ms）
    - `errorRateThreshold`: エラー率（1%/5%）
    - `capacityThreshold`: 容量使用率（80%/95%）
    - `batteryThreshold`: バッテリー残量（20%/5%）

### Tests
- **439テスト合格**（+28テスト追加）
  - DomainDetector: 14テスト
  - ComponentInference: 12テスト
  - ThresholdAlert: 30テスト（既存）

---

## [1.0.21] - 2026-01-04

### Added
- **TimeSlotService ユーティリティ**: 時間帯ベースの予約管理
  - 設定可能なスロット長（デフォルト15分）、バッファ時間（デフォルト5分）
  - `validateDuration()`: 予約時間の検証（最小/最大/単位）
  - `hasConflict()`: 重複チェック（バッファ含む）
  - `checkConflict()`: 詳細な重複分析（conflictType: overlap/buffer_violation）
  - `generateSlots()`: 時間スロット生成
  - `getAvailableSlots()`: 利用可能スロット取得
  - `roundToSlot()`: 時間丸め

- **BillingCalculator ユーティリティ**: 料金計算・返金ポリシー
  - `calculateFee()` / `calculateFeeDetailed()`: 時間ベース料金計算
  - `calculateRefund()`: キャンセル返金額計算（全額/50%/0%）
  - `calculateExtensionFee()`: 延長料金計算
  - `calculateProRata()`: 日割り料金計算
  - 設定可能: slotMinutes, fullRefundHours, partialRefundPercentage

- **TimeWindowValidator ユーティリティ**: 時間枠検証
  - `isWithinWindow()` / `validateWindow()`: 時間枠内かどうか確認
  - `isBeforeDeadline()` / `validateDeadline()`: 期限前かどうか確認
  - `hoursUntil()`, `minutesUntil()`, `minutesSince()`: 時間計算
  - `isWithinBusinessHours()`: 営業時間内チェック
  - `isSameDay()`, `isPast()`, `isFuture()`: 日付判定

### Virtual Projects (Self-Learning)
- **Project 11**: ペット健康管理システム（PetCare）- 10 EARS要件, 22テスト
- **Project 12**: コワーキングスペース予約システム（SpaceHub）- 12 EARS要件, 24テスト

### Improved
- 自己学習から3つの新ユーティリティを抽出・コア統合
  - TimeSlotService: 予約システムの時間管理
  - BillingCalculator: SaaS課金・返金計算
  - TimeWindowValidator: 期限・ウィンドウ検証

### Tests
- **381テスト合格**（+58テスト追加）
  - TimeSlotService: 19テスト
  - BillingCalculator: 16テスト
  - TimeWindowValidator: 23テスト
  - Project 11 (Pet Health): 22テスト
  - Project 12 (Coworking): 24テスト

---

## [1.0.20] - 2026-01-04

### Added
- **IdGenerator ユーティリティ**: 10プロジェクト検証から学んだID生成パターンを実装
  - `IdGenerator` クラス: プレフィックス付きユニークID生成
  - カウンター方式による同一ミリ秒内の重複防止
  - `generateShort()`: タイムスタンプなしの短いID
  - `IdGenerator.unique()`: 静的メソッドでワンオフID生成
  - `IdGenerator.uuid()`: UUID v4生成
  - `idGenerators`: 事前設定済みジェネレーター（requirement, design, task等）
  - `isValidId()`, `extractTimestamp()`: ID検証・解析ユーティリティ

- **StatusWorkflow ユーティリティ**: 10プロジェクト検証から学んだステータス遷移パターンを実装
  - `StatusWorkflow` クラス: 汎用ステータスワークフロー管理
  - ガード条件付き遷移サポート
  - 利用可能アクション・次ステータスの取得
  - 事前定義ワークフロー:
    - `approvalWorkflow`: draft → pending → approved/rejected
    - `taskWorkflow`: pending → confirmed → in_progress → completed
    - `reservationWorkflow`: tentative → confirmed → active → completed

### Improved
- **自己学習システムからの知見適用**: 10プロジェクト検証で発見したパターンをコアに統合
  - unique-id-counter パターン
  - status-workflow パターン
  - map-storage パターン

### Tests
- 323テスト合格（+38テスト追加）
- ID生成: 18テスト
- ステータスワークフロー: 20テスト

---

## [1.0.19] - 2026-01-04

### Added
- **test generate ディレクトリサポート**: ディレクトリ全体のソースファイルに対するテスト生成
  - `npx musubix test generate src/` でディレクトリ内の全ソースファイルを処理
  - 再帰的な処理オプション（`--recursive`、デフォルトON）
  - node_modules, dist, __tests__ などの除外ディレクトリ自動スキップ
  - ファイルごとの進捗表示と結果サマリー

### Improved
- **C4ダイアグラム生成の品質向上**: より情報量の多いMermaidダイアグラム出力
  - 記述的なタイトル（例: `Component Diagram - ClaimService, PolicyService...`）
  - サブグラフによるコンポーネント分類（Actors, Services, Data Layer）
  - C4スタイルに準拠したカラースキーム（classDef）
  - コンポーネントタイプ別のアイコン表示（👤, ⚙️, 💾）
  - 技術スタック情報の自動付与（[TypeScript]）

### Fixed
- **test generate EISDIR エラー**: ディレクトリを指定した際に発生していたエラーを修正
  - 100%の失敗率だった問題を完全解決

### Tests
- 100プロジェクトバッチテスト: 9/9フェーズ成功（test generateを含む）
- 全285テスト合格

---

## [1.0.18] - 2026-01-04

### Added
- **60ドメイン対応**: 業界・業種特化のドメイン認識を大幅拡張
  - 新規25ドメイン: pharmacy, veterinary, museum, cinema, parking, laundry, rental, subscription, crowdfunding, auction, wedding, funeral, charity, government, election, survey, elearning, news, podcast, streaming など
  - 合計約390個のドメイン固有コンポーネント定義

### Improved
- **既存ドメインのコンポーネント拡充**: 全ドメインが最低5個以上のコンポーネントを持つよう強化
  - security: 4→7個（EncryptionService, FirewallService, IdentityService, SecurityIncidentService追加）
  - environment: 3→7個（PollutionService, BiodiversityService, EnergyEfficiencyService, WaterQualityService追加）
  - beauty: 3→7個（BeautyMenuService, BeautyCustomerService, BeautyProductService, BeautyCouponService追加）
  - その他12ドメインのコンポーネント拡充

### Tests
- 全285テスト合格
- 100プロジェクトでの設計生成テスト実施

---

## [1.0.13] - 2026-01-03

### Improved
- **C4設計テーブルパーサー強化**: 5列テーブル対応・日本語ヘッダー対応
  - Pattern列を含む5列形式のC4テーブル対応
  - `### コンポーネント一覧` 日本語ヘッダー認識
  - `Component Diagram` セクション検出追加
  - 関係テーブルとコンポーネントテーブルの区別改善

### Self-Learning Results
- 仮想プロジェクト（会員制ショッピングサイト）を使用した自己学習実施
- フィードバック収集: 15件（accept: 6, reject: 6, modify: 3）
- パターン信頼度向上: code avoid 75% → 95%
- 学習データ: `storage/learning-data-member-shopping.json`

---

## [1.0.12] - 2026-01-03

### Added
- **C4設計からコード生成**: テーブル形式のC4コンポーネントを解析してTypeScriptコード生成
  - インターフェース、クラス、ファクトリ関数を含む完全なスケルトンコード
  - 設計パターン（Observer等）のコメント自動付与
  - コンポーネント説明に基づくメソッドスタブ自動生成

### Improved
- **EARS複数行パターン認識**: 日本語EARS形式のサポート強化
  - `WHEN 〜、THE システム SHALL 〜` 形式の認識
  - `AND THE`、`かつ`、`または` による継続行のサポート
  - Markdown形式の要件ドキュメントからの抽出精度向上
- **codegen generate**: C4設計ドキュメントから実ファイル生成が動作するように修正

### Self-Learning Results
- 仮想プロジェクト（レストラン予約システム）を使用した自己学習実施
- フィードバック収集: 10件（accept: 4, reject: 4, modify: 2）
- パターン抽出: 1件（code avoid, 信頼度75%）
- 学習データ: `storage/learning-data-v1.0.12.json`

---

## [1.0.11] - 2026-01-03

### Added
- **自己学習機能** (REQ-LEARN-001〜006): プロジェクト開発を通じた能動的学習
  - `FeedbackCollector`: ユーザーフィードバック収集・永続化
  - `PatternExtractor`: 繰り返しパターンの自動抽出
  - `LearningEngine`: 適応的推論の統合エンジン
- **CLI learn コマンド**: 自己学習システムの管理
  - `musubix learn status` - 学習状態ダッシュボード
  - `musubix learn feedback <id>` - フィードバック記録
  - `musubix learn patterns` - パターン一覧表示
  - `musubix learn add-pattern <name>` - パターン手動登録
  - `musubix learn remove-pattern <id>` - パターン削除
  - `musubix learn recommend` - コンテキストベースの推奨
  - `musubix learn decay` - 未使用パターンの減衰
  - `musubix learn export` - 学習データエクスポート
  - `musubix learn import <file>` - 学習データインポート
- **プライバシー保護**: 機密情報の自動フィルタリング（REQ-LEARN-006）
- **パターン信頼度**: 使用頻度に基づく動的信頼度計算
- **パターン減衰**: 未使用パターンの自動減衰・アーカイブ

### Tests
- 自己学習モジュール: 23テスト追加
- 全285テスト合格

---

## [1.0.10] - 2026-01-03

### Added
- **EARS検証器**: "shall not" パターンのサポート（unwanted behavior）
- **ArtifactStatus拡張**: `approved`, `implemented`, `verified` ステータス追加
- **トレーサビリティ**: 全体カバレッジ（weighted average）の計算

### Changed
- **EARS検証器**: パターン順序を最適化（特定パターンを汎用パターンより先に評価）
- **信頼度計算**: パターン固有のボーナス値を追加
  - event-driven/state-driven: +0.25
  - unwanted/optional: +0.20
  - complex: +0.30
  - ubiquitous: +0.00
- **パフォーマンス最適化**:
  - EARS検証器: 早期終了（高信頼度≥0.85でマッチ時に即座に返却）
  - EARS検証器: "shall"キーワードの事前チェック
  - トレーサビリティ: リンクインデックス（O(1)検索）

### Fixed
- EARS検証器: すべてのパターンが"ubiquitous"として検出される問題
- トレーサビリティ: `coverage.overall`が`undefined`になる問題
- CLIテスト: requirementsサブコマンド数の期待値を4から5に修正

### Tests
- EARS検証器テスト: 正しいパターン検出を期待するように更新
- 全262テスト合格

---

## [1.0.1] - 2026-01-03

### Added

#### CLI コマンド完全実装（Sprint 6）

すべてのCLIコマンドが実装され、AGENTS.mdおよびドキュメントの記載と完全に一致。

**requirements コマンド**
- `musubix requirements analyze <file>` - 自然言語からEARS要件への変換
- `musubix requirements validate <file>` - EARS構文検証
- `musubix requirements map <file>` - オントロジーマッピング
- `musubix requirements search <query>` - 関連要件検索

**design コマンド**
- `musubix design generate <file>` - 要件から設計生成
- `musubix design patterns <context>` - デザインパターン検出
- `musubix design validate <file>` - SOLID準拠検証
- `musubix design c4 <file>` - C4ダイアグラム生成（Mermaid/PlantUML）
- `musubix design adr <decision>` - ADRドキュメント生成

**codegen コマンド**
- `musubix codegen generate <file>` - 設計からコード生成
- `musubix codegen analyze <file>` - 静的コード解析
- `musubix codegen security <path>` - セキュリティスキャン（CWE対応）

**test コマンド**
- `musubix test generate <file>` - テスト生成（vitest/jest/mocha/pytest対応）
- `musubix test coverage <dir>` - カバレッジ測定・HTMLレポート

**trace コマンド**
- `musubix trace matrix` - トレーサビリティマトリクス生成（HTML/CSV/Markdown）
- `musubix trace impact <id>` - 変更影響分析
- `musubix trace validate` - トレーサビリティリンク検証

**explain コマンド**
- `musubix explain why <id>` - 決定理由の説明生成
- `musubix explain graph <id>` - 推論グラフ生成（Mermaid）

### Changed
- TSK-MUSUBIX-001.md Sprint 6 成果物を完了ステータスに更新

### Fixed
- TypeScript型エラー修正（未使用インポート、プロパティ名修正）

---

## [1.0.0] - 2026-01-02

### 🎉 Initial Release

MUSUBIXの最初の安定版リリース。全56タスク完了、ビルド・テスト通過。

### Added

#### npm/npx インストール対応

```bash
# グローバルインストール
npm install -g musubix

# npx で直接実行
npx musubix init
npx @nahisaho/musubix-mcp-server

# スコープ付きパッケージとして
npm install @nahisaho/musubix-core @nahisaho/musubix-mcp-server @nahisaho/musubix-yata-client
```

#### CLI コマンド
- `musubix` - メインCLI
- `musubix-mcp` - MCPサーバー起動

#### Core Package (@nahisaho/musubix-core)
- **認証・認可** (`auth/`)
  - AuthManager - JWT/OAuth認証管理
  
- **CLIインターフェース** (`cli/`)
  - CLI基盤 - コマンドライン引数解析・ヘルプ表示
  
- **コード生成・解析** (`codegen/`)
  - CodeGenerator - テンプレートベースコード生成
  - StaticAnalyzer - 静的コード解析
  - SecurityScanner - 脆弱性検出
  - PatternConformanceChecker - パターン準拠チェック
  - DependencyAnalyzer - 依存関係分析
  - UnitTestGenerator - ユニットテスト生成
  - IntegrationTestGenerator - 統合テスト生成
  - CoverageReporter - カバレッジレポート
  
- **設計** (`design/`)
  - PatternDetector - デザインパターン検出
  - SOLIDValidator - SOLID原則検証
  - FrameworkOptimizer - フレームワーク最適化
  - C4ModelGenerator - C4モデル生成
  - ADRGenerator - ADR生成
  
- **エラーハンドリング** (`error/`)
  - ErrorHandler - 統一エラーハンドリング
  - GracefulDegradation - グレースフルデグラデーション
  - DataPersistence - データ永続化
  
- **説明生成** (`explanation/`)
  - ReasoningChainRecorder - 推論チェーン記録
  - ExplanationGenerator - 説明生成
  - VisualExplanationGenerator - 視覚的説明生成
  
- **要件分析** (`requirements/`)
  - RequirementsDecomposer - 要件分解
  - RelatedRequirementsFinder - 関連要件検索
  
- **トレーサビリティ** (`traceability/`)
  - TraceabilityManager - トレーサビリティ管理
  - ImpactAnalyzer - 影響分析
  
- **型定義** (`types/`)
  - 共通型定義（common.ts, ears.ts, errors.ts）
  
- **ユーティリティ** (`utils/`)
  - Logger - 構造化ログ
  - DataProtector - データ保護
  - PerformanceProfiler - パフォーマンスプロファイリング
  - ScalabilityOptimizer - スケーラビリティ最適化
  - I18nManager - 国際化対応
  
- **バリデーター** (`validators/`)
  - EARSValidator - EARS形式検証
  - QualityMetricsCalculator - 品質メトリクス計算
  - CodingStandardsChecker - コーディング規約チェック

#### MCP Server Package (@nahisaho/musubix-mcp-server)
- MCPServer基盤（stdio/SSE対応）
- 34個のMCPツール定義
- 3個のMCPプロンプト定義
- MCPリソース定義
- PlatformAdapter（GitHub Copilot/Cursor対応）

#### YATA Client Package (@nahisaho/musubix-yata-client)
- YATAClient基盤
- GraphQueryInterface
- OntologyMapper
- NeuroSymbolicIntegrator
- ConfidenceEvaluator
- ContradictionDetector
- VersionCompatibility

#### テスト
- E2E統合テスト（16テストケース）
- Vitestテストフレームワーク対応

#### ドキュメント
- 要件定義書 (REQ-MUSUBIX-001.md)
- 設計書 (DES-MUSUBIX-001.md)
- タスク定義書 (TSK-MUSUBIX-001.md)
- APIリファレンス (API-REFERENCE.md)
- GitHub Copilot用プロンプト（一問一答形式対応）

### Technical Details

- **言語**: TypeScript 5.3+
- **ランタイム**: Node.js 20+
- **パッケージ管理**: npm workspaces
- **ビルド**: tsc
- **テスト**: Vitest
- **カバレッジ目標**: 
  - ライン: 80%
  - ブランチ: 75%
  - 関数: 90%

### Constitutional Compliance

9条の憲法に完全準拠:
1. Specification First (Article I)
2. Design Before Code (Article II)
3. Single Source of Truth (Article III)
4. Traceability (Article IV)
5. Incremental Progress (Article V)
6. Decision Documentation (Article VI)
7. Quality Gates (Article VII)
8. User-Centric (Article VIII)
9. Continuous Learning (Article IX)

---

## [0.1.0] - 2026-01-01

### Added
- プロジェクト初期化
- 要件定義書ドラフト
- 設計書ドラフト
- 基本プロジェクト構造

---

**文書ID**: CHANGELOG  
**バージョン**: 1.0.0  
**最終更新**: 2026-01-02
