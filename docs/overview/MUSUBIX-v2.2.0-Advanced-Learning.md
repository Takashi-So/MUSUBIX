# MUSUBIX v2.2.0 Advanced Learning Enhancement

**バージョン**: 2.2.0  
**最終更新**: 2026-01-08

---

## 1. 概要

MUSUBIX v2.2.0は、**高度な学習機能強化**を実現するメジャーアップデートです。Neural Search、Library Learner、Synthesisの3パッケージに対して、28タスク・464テストを追加しました。

### 1.1 主要機能

| 領域 | 機能 | 説明 |
|------|------|------|
| **Neural Search** | コンテキスト認識埋め込み | AST構造を考慮した意味的埋め込み |
| | ハイブリッドランキング | BM25 + ベクトル類似度の統合 |
| | 埋め込みキャッシュ | LRU + TTL管理による高効率キャッシュ |
| **Library Learner** | セマンティックチャンキング | AST境界認識によるコード分割 |
| | パターンバージョン管理 | Git風のパターン履歴管理 |
| | ドメイン認識抽象化 | ドメイン特化パターン抽出 |
| **Synthesis** | 演繹的合成エンジン | FlashFill風の仕様分解 |
| | メタ学習 | タスク類似度ベースの戦略選択 |
| | DSL拡張 | パターンからの演算子自動生成 |

---

## 2. Neural Search 強化

### 2.1 アーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                    Neural Search Engine                      │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────┐  │
│  │ContextAwareEmb- │  │  ScopeEnhancer  │  │ HybridRanker│  │
│  │     edder       │  │                 │  │             │  │
│  │ ・AST構造認識   │  │ ・スコープ抽出  │  │ ・BM25      │  │
│  │ ・文脈埋め込み  │  │ ・コード強化    │  │ ・ベクトル  │  │
│  └────────┬────────┘  └────────┬────────┘  └──────┬──────┘  │
│           │                    │                  │          │
│           └────────────────────┼──────────────────┘          │
│                                ▼                             │
│  ┌─────────────────────────────────────────────────────────┐│
│  │               EmbeddingCache (LRU + TTL)                ││
│  │  ・最大10,000エントリ  ・TTL管理  ・ヒット率追跡        ││
│  └─────────────────────────────────────────────────────────┘│
│                                │                             │
│                                ▼                             │
│  ┌─────────────────────────────────────────────────────────┐│
│  │                OnlineModelUpdater                        ││
│  │  ・継続学習  ・フィードバック統合  ・モデル更新          ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

### 2.2 主要コンポーネント

#### ContextAwareEmbedder

AST構造を認識したコンテキスト埋め込み:

```typescript
import { ContextAwareEmbedder } from '@nahisaho/musubix-neural-search';

const embedder = new ContextAwareEmbedder({
  windowSize: 5,        // コンテキストウィンドウサイズ
  includeAST: true,     // AST情報を含む
  normalize: true,      // 正規化
});

// コード埋め込み生成
const embedding = embedder.embed(code, {
  surrounding: surroundingCode,
  imports: importStatements,
});

// バッチ埋め込み
const embeddings = embedder.embedBatch(codeSnippets);
```

#### HybridRanker

BM25とベクトル類似度を組み合わせたハイブリッドランキング:

```typescript
import { HybridRanker } from '@nahisaho/musubix-neural-search';

const ranker = new HybridRanker({
  alpha: 0.6,           // BM25の重み (0-1)
  bm25Config: {
    k1: 1.2,
    b: 0.75,
  },
});

const results = ranker.rank(query, documents);
// results: [{ document, score, bm25Score, vectorScore }]
```

#### EmbeddingCache

LRU + TTL管理による高効率キャッシュ:

```typescript
import { EmbeddingCache } from '@nahisaho/musubix-neural-search';

const cache = new EmbeddingCache({
  maxSize: 10000,       // 最大エントリ数
  ttlMs: 3600000,       // TTL (1時間)
});

// キャッシュ操作
cache.set('key', embedding);
const cached = cache.get('key');

// 統計取得
const stats = cache.getStats();
// { hits, misses, hitRate, size }
```

#### TrajectoryLogger (P2)

検索軌跡のロギングとエクスポート:

```typescript
import { createTrajectoryLogger } from '@nahisaho/musubix-neural-search';

const logger = createTrajectoryLogger();

// 分岐ログ
logger.logBranch({
  depth: 1,
  score: 0.85,
  action: 'expand',
  metadata: { nodeType: 'function' },
});

// 軌跡取得
const trajectory = logger.getTrajectory();

// エクスポート
const json = logger.export('json');
const parquet = logger.export('parquet');

// 統計
const stats = logger.getStatistics();
// { maxDepth, bestScore, averageScore, branchesByDepth }
```

---

## 3. Library Learner 強化

### 3.1 アーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                   Library Learner Engine                     │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────┐  │
│  │ SemanticChunker │  │AbstractionEngine│  │ Iterative-  │  │
│  │                 │  │                 │  │ Compressor  │  │
│  │ ・AST境界認識   │  │ ・階層抽象化    │  │ ・反復圧縮  │  │
│  │ ・サイズ制御    │  │ ・変数正規化    │  │ ・最適化    │  │
│  └────────┬────────┘  └────────┬────────┘  └──────┬──────┘  │
│           │                    │                  │          │
│           └────────────────────┼──────────────────┘          │
│                                ▼                             │
│  ┌─────────────────────────────────────────────────────────┐│
│  │              ConflictResolver                            ││
│  │  ・競合検出  ・自動マージ  ・優先度解決                  ││
│  └─────────────────────────────────────────────────────────┘│
│                                │                             │
│                                ▼                             │
│  ┌─────────────────────────────────────────────────────────┐│
│  │           PatternVersionManager                          ││
│  │  ・コミット  ・ブランチ  ・マージ  ・履歴追跡            ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

### 3.2 主要コンポーネント

#### SemanticChunker

AST境界を認識したセマンティックチャンキング:

```typescript
import { SemanticChunker } from '@nahisaho/musubix-library-learner';

const chunker = new SemanticChunker({
  minSize: 50,          // 最小チャンクサイズ
  maxSize: 500,         // 最大チャンクサイズ
  respectBoundaries: true,  // AST境界を尊重
});

const chunks = chunker.chunk(code);
// chunks: [{ content, startLine, endLine, type }]
```

#### PatternVersionManager

Git風のパターンバージョン管理:

```typescript
import { PatternVersionManager } from '@nahisaho/musubix-library-learner';

const manager = new PatternVersionManager();

// コミット
const commitId = manager.commit(pattern, 'Add validation pattern');

// 履歴
const history = manager.getHistory(patternId);

// 差分
const diff = manager.diff(commitId1, commitId2);

// ロールバック
manager.rollback(patternId, commitId);
```

#### DomainAwareAbstractor

ドメイン特化パターン抽出:

```typescript
import { DomainAwareAbstractor } from '@nahisaho/musubix-library-learner';

const abstractor = new DomainAwareAbstractor();

// ドメイン指定抽象化
const pattern = abstractor.abstract(code, 'web-api');

// ドメイン自動検出
const detectedPattern = abstractor.abstractWithAutoDetection(code);
```

#### MetricsExporter (P2)

学習メトリクスのエクスポート:

```typescript
import { createMetricsExporter } from '@nahisaho/musubix-library-learner';

const exporter = createMetricsExporter(library);

// メトリクス収集
const metrics = exporter.collectMetrics();

// エクスポート
const json = exporter.export('json');
const markdown = exporter.export('markdown');

// サマリー取得
const summary = exporter.getSummary();
// { totalPatterns, averageConfidence, healthStatus }

// 健全性評価
// healthStatus: 'good' | 'warning' | 'poor'
```

---

## 4. Synthesis 強化

### 4.1 アーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                    Synthesis Engine                          │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────┐  │
│  │DeductiveEngine  │  │WitnessFunction  │  │MetaLearning │  │
│  │                 │  │                 │  │   Engine    │  │
│  │ ・仕様分解      │  │ ・部分仕様生成  │  │ ・戦略選択  │  │
│  │ ・演繹的探索    │  │ ・分解ルール    │  │ ・類似度    │  │
│  └────────┬────────┘  └────────┬────────┘  └──────┬──────┘  │
│           │                    │                  │          │
│           └────────────────────┼──────────────────┘          │
│                                ▼                             │
│  ┌─────────────────────────────────────────────────────────┐│
│  │                   DSLExtender                            ││
│  │  ・パターン分析  ・演算子提案  ・DSL拡張                 ││
│  └─────────────────────────────────────────────────────────┘│
│                                │                             │
│                                ▼                             │
│  ┌─────────────────────────────────────────────────────────┐│
│  │               ExampleAnalyzer                            ││
│  │  ・品質分析  ・カバレッジ  ・曖昧性検出                  ││
│  └─────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────┘
```

### 4.2 主要コンポーネント

#### DeductiveEngine

FlashFill風の演繹的合成:

```typescript
import { DeductiveEngine } from '@nahisaho/musubix-synthesis';

const engine = new DeductiveEngine(grammar);

const result = engine.synthesize({
  examples: [
    { input: 'hello', output: 'HELLO' },
    { input: 'world', output: 'WORLD' },
  ],
});

console.log(result.program); // input.toUpperCase()
console.log(result.confidence); // 0.95
```

#### MetaLearningEngine

タスク類似度ベースの戦略選択:

```typescript
import { createMetaLearningEngine } from '@nahisaho/musubix-synthesis';

const meta = createMetaLearningEngine({
  historySize: 100,
  similarityThreshold: 0.7,
});

// タスク記録
meta.recordTask(task, result);

// 戦略選択
const strategy = meta.selectStrategy(newTask);
// strategy: { algorithm, params, expectedTime }

// 類似タスク検索
const similar = meta.findSimilarTasks(task, 5);
```

#### DSLExtender

パターンからのDSL演算子自動生成:

```typescript
import { createDSLExtender } from '@nahisaho/musubix-synthesis';

const extender = createDSLExtender(baseDSL);

// パターンからギャップ検出
const gaps = extender.detectGaps(patterns);

// 演算子提案
const suggestions = extender.suggestOperators(gaps);
// suggestions: [{ name, signature, implementation }]

// DSL拡張
const extendedDSL = extender.extend(suggestions);
```

#### ExampleAnalyzer

例題品質分析:

```typescript
import { createExampleAnalyzer } from '@nahisaho/musubix-synthesis';

const analyzer = createExampleAnalyzer();

// 品質分析
const quality = analyzer.analyzeQuality(examples);
// quality: { score, issues, suggestions }

// カバレッジ分析
const coverage = analyzer.analyzeCoverage(examples, dsl);

// 曖昧性検出
const ambiguities = analyzer.detectAmbiguity(examples);
```

#### ExplanationGenerator (P2)

合成プログラムの自然言語説明:

```typescript
import { createExplanationGenerator } from '@nahisaho/musubix-synthesis';

const explainer = createExplanationGenerator();

// 説明生成
const explanation = explainer.generate(program);
// explanation: { description, steps, exampleWalkthrough, confidence }

// 詳細説明
const detailed = explainer.explain(program);
// detailed: { ...explanation, rationale, limitations, relationship }

// 一行サマリー
const summary = explainer.summarize(program);
// "Converts to uppercase"

// 信頼度
const confidence = explainer.getConfidence(program);
```

---

## 5. MCP統合

### 5.1 Synthesisツール（5ツール）

| ツール | 説明 |
|--------|------|
| `synthesis_from_examples` | 例からプログラム合成 |
| `synthesis_analyze_examples` | 例題品質分析 |
| `synthesis_learn_patterns` | パターン学習 |
| `synthesis_query_patterns` | パターン検索 |
| `synthesis_get_stats` | 統計取得 |

### 5.2 Synthesisプロンプト（2プロンプト）

| プロンプト | 説明 |
|-----------|------|
| `synthesis_guidance` | 合成ガイダンス |
| `synthesis_explain_pattern` | パターン説明 |

---

## 6. CLIコマンド

### 6.1 プログラム合成

```bash
# 例からプログラム合成
npx musubix synthesize <examples.json>

# PBE特化合成
npx musubix synthesize pbe <examples.json>

# エイリアス
npx musubix syn <examples.json>
```

### 6.2 パターンライブラリ管理

```bash
# コードからパターン学習
npx musubix library learn <file>

# パターン検索
npx musubix library query <query>

# 統計表示
npx musubix library stats
npx musubix lib stats  # エイリアス
```

---

## 7. テスト統計

| EPIC | タスク数 | テスト数 |
|------|---------|---------|
| Neural Search強化 | 7 | 138 |
| Library Learner強化 | 7 | 145 |
| Synthesis強化 | 6 | 108 |
| 統合・CLI | 4 | 73 |
| **合計** | **28** | **464** |

### 7.1 パッケージ別テスト数

| パッケージ | v2.1.0 | v2.2.0 | 増分 |
|-----------|--------|--------|------|
| `@nahisaho/musubix-neural-search` | 144 | 165 | +21 |
| `@nahisaho/musubix-library-learner` | 132 | 158 | +26 |
| `@nahisaho/musubix-synthesis` | 146 | 163 | +17 |

---

## 8. マイグレーションガイド

### v2.1.x → v2.2.0

v2.2.0は完全な後方互換性を維持しています。新機能を使用するには:

```typescript
// v2.1.x (引き続き動作)
import { PBESynthesizer } from '@nahisaho/musubix-synthesis';

// v2.2.0 新機能
import {
  createMetaLearningEngine,
  createExampleAnalyzer,
  createExplanationGenerator,
} from '@nahisaho/musubix-synthesis';
```

---

## 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [MUSUBIX-Learning.md](MUSUBIX-Learning.md) | 学習システム概要 |
| [MUSUBIX-Overview.md](MUSUBIX-Overview.md) | システム全体概要 |
| [USER-GUIDE.md](../USER-GUIDE.md) | ユーザーガイド |

---

**バージョン**: 2.2.0  
**最終更新**: 2026-01-08  
**MUSUBIX Project**
