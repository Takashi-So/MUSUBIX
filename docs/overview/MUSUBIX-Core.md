# MUSUBIX Core パッケージ

**パッケージ名**: `@nahisaho/musubix-core`  
**バージョン**: 1.7.5  
**最終更新**: 2026-01-06

---

## 1. 概要

`@nahisaho/musubix-core` は、MUSUBIXシステムの中核となるライブラリです。CLI、EARS検証、コード生成、設計パターン検出、トレーサビリティ管理、シンボリック推論など、すべての基本機能を提供します。

### 1.1 モジュール構成

```
packages/core/src/
├── auth/           # 認証・認可
├── cli/            # CLIインターフェース
├── codegen/        # コード生成・解析
├── design/         # 設計パターン・C4モデル
├── error/          # エラーハンドリング
├── explanation/    # 説明生成・可視化
├── learning/       # 自己学習システム
├── perf/           # パフォーマンス最適化
├── requirements/   # 要件分析・分解
├── symbolic/       # シンボリック推論
├── testing/        # テスト支援
├── traceability/   # トレーサビリティ
├── types/          # 型定義
├── utils/          # ユーティリティ
└── validators/     # EARS検証
```

---

## 2. auth/ - 認証・認可モジュール

### 2.1 概要

ユーザー認証・認可管理を提供します。マルチプロバイダ対応で、エンタープライズ環境での利用を想定しています。

### 2.2 主要機能

| 機能 | 説明 |
|------|------|
| **マルチプロバイダ** | local, OAuth, SAML, LDAP, API-key |
| **トークン管理** | access, refresh, api-key |
| **セッション管理** | 有効期限、自動更新 |
| **MFA対応** | 二要素認証 |
| **RBAC** | ロールベースアクセス制御 |

### 2.3 主要な型

```typescript
// 認証プロバイダ
type AuthProvider = 'local' | 'oauth' | 'saml' | 'ldap' | 'api-key';

// ユーザー情報
interface User {
  id: string;
  email: string;
  roles: string[];
  permissions: string[];
}

// トークン
interface Token {
  accessToken: string;
  refreshToken?: string;
  expiresAt: Date;
}

// 認可チェック
interface AuthorizationCheck {
  resource: string;
  action: 'read' | 'write' | 'delete' | 'admin';
  allowed: boolean;
}
```

### 2.4 トレーサビリティ

- **REQ-SEC-002**: 認証・認可要件
- **Article VIII**: Decision Records（認証方式の決定記録）

---

## 3. cli/ - CLIモジュール

### 3.1 概要

Commander.jsベースのCLIフレームワークを提供します。すべてのMUSUBIX機能にコマンドラインからアクセスできます。

### 3.2 主要コマンド

#### 初期化

```bash
npx musubix init [path] [--name <name>] [--force]
```

#### 要件分析

```bash
npx musubix requirements analyze <file>    # 自然言語 → EARS変換
npx musubix requirements validate <file>   # EARS構文検証
npx musubix requirements map <file>        # オントロジーマッピング
npx musubix requirements search <query>    # 関連要件検索
```

#### 設計生成

```bash
npx musubix design generate <file>         # 要件から設計生成
npx musubix design patterns <context>      # パターン検出
npx musubix design validate <file>         # SOLID準拠検証
npx musubix design c4 <file>               # C4ダイアグラム生成
npx musubix design adr <decision>          # ADR生成
```

#### コード生成

```bash
npx musubix codegen generate <file>        # 設計からコード生成
npx musubix codegen analyze <file>         # 静的解析
npx musubix codegen security <path>        # セキュリティスキャン
```

#### テスト

```bash
npx musubix test generate <file>           # テスト生成
npx musubix test coverage <dir>            # カバレッジ測定
```

#### トレーサビリティ

```bash
npx musubix trace matrix                   # トレーサビリティマトリクス
npx musubix trace impact <id>              # 影響分析
npx musubix trace validate                 # リンク検証
npx musubix trace sync                     # 自動更新
```

#### 自己学習

```bash
npx musubix learn status                   # 学習状態ダッシュボード
npx musubix learn feedback <id>            # フィードバック記録
npx musubix learn patterns                 # パターン一覧
npx musubix learn recommend                # 推奨パターン
npx musubix learn export                   # エクスポート
npx musubix learn import <file>            # インポート
```

#### REPL

```bash
npx musubix repl                           # 対話的シェル
```

#### KGPR（Knowledge Graph Pull Request）

```bash
npx musubix kgpr create -t "title"         # KGPR作成
npx musubix kgpr diff                      # 差分プレビュー
npx musubix kgpr list                      # 一覧
npx musubix kgpr submit <id>               # 送信
```

### 3.3 グローバルオプション

| オプション | 説明 |
|-----------|------|
| `--verbose, -v` | 詳細出力 |
| `--json` | JSON形式出力 |
| `--config <file>` | 設定ファイル指定 |
| `--quiet, -q` | 静音モード |

### 3.4 終了コード

| コード | 意味 |
|--------|------|
| 0 | 成功 |
| 1 | 一般エラー |
| 2 | 検証エラー |
| 3 | 設定エラー |
| 4 | 入出力エラー |
| 5 | 内部エラー |

---

## 4. codegen/ - コード生成モジュール

### 4.1 概要

設計ドキュメントからマルチ言語対応のコードを自動生成します。静的解析、品質メトリクス、セキュリティスキャン機能も提供します。

### 4.2 対応言語

| 言語 | ファイル拡張子 |
|------|---------------|
| TypeScript | `.ts` |
| JavaScript | `.js` |
| Python | `.py` |
| Java | `.java` |
| C# | `.cs` |
| Go | `.go` |
| Rust | `.rs` |

### 4.3 主要クラス

#### CodeGenerator

メインのコード生成器。

```typescript
import { CodeGenerator } from '@nahisaho/musubix-core';

const generator = new CodeGenerator({
  language: 'typescript',
  outputDir: './src',
  patterns: ['repository', 'service', 'factory'],
});

const result = await generator.generate(designDocument);
```

#### StaticAnalyzer

コードの静的解析を実行。

```typescript
import { StaticAnalyzer } from '@nahisaho/musubix-core';

const analyzer = new StaticAnalyzer();
const issues = await analyzer.analyze('./src');
// 複雑度、デッドコード、未使用変数などを検出
```

#### SecurityScanner

セキュリティ脆弱性をスキャン。

```typescript
import { SecurityScanner } from '@nahisaho/musubix-core';

const scanner = new SecurityScanner();
const vulnerabilities = await scanner.scan('./src');
// SQLインジェクション、XSS、ハードコードされた秘密情報などを検出
```

#### QualityMetrics

コード品質メトリクスを計算。

```typescript
import { QualityMetrics } from '@nahisaho/musubix-core';

const metrics = new QualityMetrics();
const report = await metrics.calculate('./src');
// 循環的複雑度、行数、テストカバレッジなど
```

### 4.4 テスト生成

```typescript
import { UnitTestGenerator, IntegrationTestGenerator } from '@nahisaho/musubix-core';

// ユニットテスト生成
const unitGen = new UnitTestGenerator();
const unitTests = await unitGen.generate(sourceFile);

// 統合テスト生成
const intGen = new IntegrationTestGenerator();
const integrationTests = await intGen.generate(componentSpec);
```

---

## 5. design/ - 設計モジュール

### 5.1 概要

C4モデル図の自動生成、デザインパターン検出、ADR生成、SOLID原則検証を提供します。

### 5.2 C4モデル生成

4つのレベルでシステム設計を構造化します。

| レベル | 説明 |
|--------|------|
| **Context** | システム境界と外部アクター |
| **Container** | 技術選択とコンテナ構成 |
| **Component** | コンテナ内部構造 |
| **Code** | 実装詳細 |

```typescript
import { C4Generator } from '@nahisaho/musubix-core';

const generator = new C4Generator();
const diagram = await generator.generate(requirements, {
  level: 'component',
  format: 'mermaid', // 'structurizr' | 'plantuml' | 'mermaid' | 'json'
});
```

### 5.3 デザインパターン検出

```typescript
import { PatternDetector } from '@nahisaho/musubix-core';

const detector = new PatternDetector();
const patterns = await detector.detect(codebase);
// Repository, Service, Factory, Singleton, Observer など
```

### 5.4 ADR生成

Architecture Decision Record（アーキテクチャ決定記録）を生成。

```typescript
import { AdrGenerator } from '@nahisaho/musubix-core';

const generator = new AdrGenerator();
const adr = await generator.generate({
  title: 'Use PostgreSQL for persistence',
  context: 'Need a reliable database...',
  decision: 'Use PostgreSQL...',
  consequences: ['Pro: ACID compliance', 'Con: More complex setup'],
});
```

### 5.5 SOLID検証

```typescript
import { SolidValidator } from '@nahisaho/musubix-core';

const validator = new SolidValidator();
const violations = await validator.validate('./src');
// SRP, OCP, LSP, ISP, DIP の違反を検出
```

---

## 6. symbolic/ - シンボリック推論モジュール

### 6.1 概要

ニューロシンボリックAI統合の中核モジュール。LLM出力の検証、ハルシネーション検出、憲法ルール施行、形式検証を提供します。

### 6.2 セマンティックフィルタ

LLMが生成したコードをシンボリック検証でフィルタリング。

```typescript
import { SemanticCodeFilterPipeline } from '@nahisaho/musubix-core';

const pipeline = new SemanticCodeFilterPipeline({
  projectContext: { /* プロジェクト情報 */ },
});

const result = await pipeline.filter({
  code: generatedCode,
  prompt: originalPrompt,
});
// valid/invalid/warning を返す
```

### 6.3 ハルシネーション検出

存在しないAPIやインポートを検出。

```typescript
import { HallucinationDetector, ProjectSymbolIndex } from '@nahisaho/musubix-core';

const index = new ProjectSymbolIndex();
await index.buildFromDirectory('./src');

const detector = new HallucinationDetector(index);
const hallucinations = await detector.detect(code);
// 存在しない関数、クラス、モジュールを報告
```

### 6.4 憲法ルールチェック

9条憲法への準拠を検証。

```typescript
import { ConstitutionRuleRegistry, DEFAULT_CONSTITUTION_RULES } from '@nahisaho/musubix-core';

const registry = new ConstitutionRuleRegistry(DEFAULT_CONSTITUTION_RULES);
const report = await registry.checkAll({
  code: sourceCode,
  design: designDoc,
  requirements: reqDoc,
});
// 各条項の準拠状況を報告
```

### 6.5 信頼度ルーティング

```typescript
import { ConfidenceEstimator, ConfidenceBasedRouter } from '@nahisaho/musubix-core';

const estimator = new ConfidenceEstimator();
const confidence = await estimator.estimate(llmOutput);

const router = new ConfidenceBasedRouter();
const decision = router.route({
  symbolicResult: 'valid',
  neuralConfidence: confidence.score,
});
// 'accept' | 'reject' | 'prefer_symbolic'
```

### 6.6 形式検証（Z3）

```typescript
import { Z3Adapter, EarsToFormalSpecConverter } from '@nahisaho/musubix-core';

// EARS→SMT変換
const converter = new EarsToFormalSpecConverter();
const smtSpec = converter.convert(earsRequirement);

// Z3で検証
const z3 = new Z3Adapter();
const result = await z3.verify(smtSpec);
```

---

## 7. traceability/ - トレーサビリティモジュール

### 7.1 概要

要件・設計・コード・テスト間の双方向トレーサビリティを管理します。

### 7.2 リンクタイプ

| タイプ | 説明 |
|--------|------|
| `derives` | 派生関係 |
| `implements` | 実装関係 |
| `satisfies` | 充足関係 |
| `verifies` | 検証関係 |
| `decomposes` | 分解関係 |
| `relates` | 関連関係 |
| `conflicts` | 競合関係 |

### 7.3 使用例

```typescript
import { TraceabilityManager } from '@nahisaho/musubix-core';

const manager = new TraceabilityManager();

// リンク追加
await manager.addLink({
  source: 'REQ-001',
  target: 'DES-001',
  type: 'implements',
  confidence: 0.95,
});

// 影響分析
const impact = await manager.analyzeImpact('REQ-001');

// マトリクス生成
const matrix = await manager.generateMatrix();

// ギャップ検出
const gaps = await manager.detectGaps();
```

---

## 8. validators/ - EARS検証モジュール

### 8.1 概要

EARS（Easy Approach to Requirements Syntax）形式の要件を検証します。

### 8.2 パターン

| パターン | キーワード | 例 |
|---------|-----------|-----|
| **Ubiquitous** | `THE ... SHALL` | THE system SHALL encrypt data |
| **Event-driven** | `WHEN ... THE ... SHALL` | WHEN user logs in, THE system SHALL... |
| **State-driven** | `WHILE ... THE ... SHALL` | WHILE in maintenance, THE system SHALL... |
| **Unwanted** | `SHALL NOT` | THE system SHALL NOT expose... |
| **Optional** | `IF ... THEN ... SHALL` | IF admin, THEN THE system SHALL... |

### 8.3 使用例

```typescript
import { EarsValidator } from '@nahisaho/musubix-core';

const validator = new EarsValidator();
const result = await validator.validate(
  'WHEN a user submits login form, THE system SHALL validate credentials.'
);

console.log(result.pattern);     // 'event-driven'
console.log(result.confidence);  // 0.95
console.log(result.isValid);     // true
console.log(result.suggestions); // 改善提案（もしあれば）
```

---

## 9. learning/ - 自己学習モジュール

### 9.1 概要

フィードバック収集、パターン抽出、適応的推論を提供します。

### 9.2 フィードバックタイプ

| タイプ | 説明 |
|--------|------|
| `accept` | 生成結果を受け入れ |
| `reject` | 生成結果を拒否 |
| `modify` | 修正して使用 |

### 9.3 使用例

```typescript
import { LearningEngine, FeedbackCollector } from '@nahisaho/musubix-core';

const collector = new FeedbackCollector();

// フィードバック収集
await collector.record({
  generationId: 'gen-001',
  type: 'accept',
  context: { language: 'typescript', pattern: 'repository' },
});

// 学習エンジン
const engine = new LearningEngine();
await engine.learn();

// パターン推奨
const recommendations = await engine.recommend(currentContext);
```

---

## 10. error/ - エラーハンドリングモジュール

### 10.1 概要

グレースフルデグラデーションとマルチ戦略フォールバックを提供します。

### 10.2 サービスモード

| モード | 説明 |
|--------|------|
| `full` | 全機能利用可能 |
| `reduced` | 一部機能制限 |
| `minimal` | 最小限の機能 |
| `offline` | オフライン動作 |
| `emergency` | 緊急モード |

### 10.3 フォールバック戦略

| 戦略 | 説明 |
|------|------|
| `use-cache` | キャッシュを利用 |
| `default-value` | デフォルト値を返す |
| `retry` | リトライ（バックオフ付き） |
| `alternative` | 代替サービスを使用 |
| `skip` | スキップ |
| `manual` | 手動介入要求 |

---

## 11. perf/ - パフォーマンスモジュール

### 11.1 概要

遅延ローディング、キャッシュ、並列実行、メモリ監視を提供します。

### 11.2 主要機能

```typescript
import { 
  LazyLoader, 
  LRUCache, 
  ParallelExecutor,
  MemoryMonitor 
} from '@nahisaho/musubix-core';

// 遅延ローディング
const loader = new LazyLoader();
const heavyModule = await loader.load(() => import('./heavy-module'));

// LRUキャッシュ
const cache = new LRUCache<string, Result>({ maxSize: 1000 });
cache.set('key', result);

// 並列実行
const executor = new ParallelExecutor({ concurrency: 4 });
const results = await executor.map(items, processItem);

// メモリ監視
const monitor = new MemoryMonitor();
monitor.onThreshold(0.8, () => {
  console.log('Memory usage above 80%');
});
```

---

## 12. testing/ - テスト支援モジュール

### 12.1 概要

E2Eテストフレームワーク、テストフィクスチャ管理、CLIランナーを提供します。

### 12.2 主要機能

```typescript
import { 
  TestContext, 
  TestProject, 
  TestFixtures,
  CLIRunner,
  assertEarsValid,
  assertDesignComplete
} from '@nahisaho/musubix-core';

// テストコンテキスト
const ctx = new TestContext();
await ctx.setup();

// テストプロジェクト
const project = new TestProject('test-project');
await project.scaffold();

// CLIランナー
const runner = new CLIRunner();
const result = await runner.run('musubix', ['requirements', 'validate', 'req.md']);

// カスタムアサーション
assertEarsValid(requirement);
assertDesignComplete(design);
```

---

## 13. API リファレンス

詳細なAPIリファレンスは [API-REFERENCE.md](API-REFERENCE.md) を参照してください。

---

## 14. 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [MUSUBIX-Overview.md](MUSUBIX-Overview.md) | 全体概要 |
| [MUSUBIX-FormalVerify.md](MUSUBIX-FormalVerify.md) | 形式検証 |
| [MUSUBIX-MCP-Server.md](MUSUBIX-MCP-Server.md) | MCPサーバー |
| [MUSUBIX-YATA.md](MUSUBIX-YATA.md) | YATA知識グラフ |
| [MUSUBIX-Learning.md](MUSUBIX-Learning.md) | 学習システム |

---

**© 2026 MUSUBIX Project**
