# MUSUBIX 学習システム パッケージ群

**関連パッケージ**:
- `@nahisaho/musubix-pattern-mcp`
- `@nahisaho/musubix-ontology-mcp`
- `@nahisaho/musubix-wake-sleep`
- `@nahisaho/musubix-sdd-ontology`

**バージョン**: 1.7.5  
**最終更新**: 2026-01-06

---

## 1. 学習システム概要

MUSUBIXの学習システムは、AIエージェントの継続的な改善を実現します。Wake-Sleepサイクル、パターン学習、オントロジー管理を統合した自律学習機能を提供します。

### 1.1 学習アーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                   Wake-Sleep Cycle                           │
│  ┌──────────────────────┐    ┌──────────────────────┐       │
│  │      Wake Phase      │    │     Sleep Phase      │       │
│  │  ・コード観察        │    │  ・パターン統合      │       │
│  │  ・パターン抽出      │    │  ・類似パターン圧縮  │       │
│  │  ・知識グラフ更新    │    │  ・メモリ最適化      │       │
│  └──────────┬───────────┘    └───────────┬──────────┘       │
│             │                            │                   │
│             └────────────┬───────────────┘                   │
│                          ▼                                   │
│  ┌───────────────────────────────────────────────────────┐  │
│  │               Pattern Library                          │  │
│  │  ・抽出パターン  ・圧縮パターン  ・信頼度スコア       │  │
│  └───────────────────────────────────────────────────────┘  │
│                          │                                   │
│                          ▼                                   │
│  ┌───────────────────────────────────────────────────────┐  │
│  │              Ontology Store (N3)                       │  │
│  │  ・RDF/OWL知識  ・推論ルール  ・ドメインオントロジー  │  │
│  └───────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 パッケージ構成

| パッケージ | 役割 |
|-----------|------|
| **pattern-mcp** | パターン抽出・圧縮・ライブラリ管理 |
| **ontology-mcp** | N3Store・推論エンジン・オントロジー管理 |
| **wake-sleep** | Wake-Sleep学習サイクル制御 |
| **sdd-ontology** | SDD方法論のオントロジー定義 |

---

## 2. Pattern MCP

### 2.1 概要

`@nahisaho/musubix-pattern-mcp` は、コードからパターンを抽出・圧縮し、再利用可能な形式で管理します。

### 2.2 アーキテクチャ

```
packages/pattern-mcp/src/
├── extractor/
│   ├── ast-analyzer.ts      # AST解析
│   ├── pattern-detector.ts  # パターン検出
│   └── feature-extractor.ts # 特徴抽出
├── compressor/
│   ├── similarity.ts        # 類似度計算
│   ├── merger.ts            # パターン統合
│   └── abstractor.ts        # 抽象化
├── library/
│   ├── pattern-store.ts     # パターンストア
│   ├── indexer.ts           # インデックス
│   └── search.ts            # 検索
├── tools/
│   └── pattern-tools.ts     # MCPツール
└── index.ts
```

### 2.3 主要機能

#### 2.3.1 パターン抽出

コードからパターンを自動抽出します。

```typescript
import { PatternExtractor } from '@nahisaho/musubix-pattern-mcp';

const extractor = new PatternExtractor();

const patterns = await extractor.extract(`
  class UserService {
    constructor(private readonly userRepo: UserRepository) {}
    
    async findUser(id: string): Promise<User | null> {
      return this.userRepo.findById(id);
    }
  }
`);

// 抽出結果
// {
//   patterns: [
//     {
//       name: 'repository-pattern',
//       type: 'design-pattern',
//       confidence: 0.95,
//       features: ['dependency-injection', 'async-method', 'repository-access']
//     }
//   ]
// }
```

#### 2.3.2 パターン圧縮

類似パターンを統合・抽象化します。

```typescript
import { PatternCompressor } from '@nahisaho/musubix-pattern-mcp';

const compressor = new PatternCompressor();

// 類似パターンの統合
const compressed = await compressor.compress(patterns, {
  similarityThreshold: 0.8,
  minOccurrences: 3,
});

// 抽象化
const abstracted = await compressor.abstract(pattern, {
  level: 'high',  // 'low' | 'medium' | 'high'
});
```

#### 2.3.3 パターンライブラリ

学習したパターンを永続化・検索します。

```typescript
import { PatternLibrary } from '@nahisaho/musubix-pattern-mcp';

const library = new PatternLibrary({
  storagePath: './patterns.db',
});

// パターン保存
await library.store(pattern);

// パターン検索
const matches = await library.search({
  type: 'design-pattern',
  domain: 'authentication',
  minConfidence: 0.9,
});

// パターン推奨
const recommendations = await library.recommend({
  context: 'user-service-implementation',
  maxResults: 5,
});
```

### 2.4 パターンスキーマ

```typescript
interface Pattern {
  id: string;
  name: string;
  type: PatternType;
  description: string;
  
  // 構造情報
  structure: {
    ast: ASTNode;
    features: string[];
    relationships: Relationship[];
  };
  
  // メタデータ
  metadata: {
    domain: string;
    language: string;
    framework?: string;
  };
  
  // 品質情報
  quality: {
    confidence: number;      // 0-1
    occurrences: number;
    successRate: number;     // 適用成功率
    lastUsed: Date;
  };
  
  // 抽象化レベル
  abstraction: {
    level: 'concrete' | 'semi-abstract' | 'abstract';
    generalizedFrom: string[];  // 元パターンID
  };
}

type PatternType = 
  | 'design-pattern'
  | 'code-idiom'
  | 'architecture-pattern'
  | 'test-pattern'
  | 'error-handling';
```

---

## 3. Ontology MCP

### 3.1 概要

`@nahisaho/musubix-ontology-mcp` は、N3Store基盤のオントロジー管理と推論エンジンを提供します。

### 3.2 アーキテクチャ

```
packages/ontology-mcp/src/
├── store/
│   ├── n3-store.ts          # N3Store実装
│   ├── graph-manager.ts     # グラフ管理
│   └── namespace.ts         # 名前空間管理
├── inference/
│   ├── reasoner.ts          # 推論エンジン
│   ├── rules.ts             # 推論ルール
│   └── forward-chain.ts     # 前向き連鎖
├── validation/
│   ├── consistency.ts       # 整合性検証
│   ├── circular.ts          # 循環検出
│   └── schema-validator.ts  # スキーマ検証
├── tools/
│   └── ontology-tools.ts    # MCPツール
└── index.ts
```

### 3.3 主要機能

#### 3.3.1 N3Store

RDF/OWLデータを格納・操作します。

```typescript
import { N3Store } from '@nahisaho/musubix-ontology-mcp';

const store = new N3Store();

// トリプル追加
store.addQuad(
  namedNode('http://example.org/User'),
  namedNode('http://www.w3.org/1999/02/22-rdf-syntax-ns#type'),
  namedNode('http://www.w3.org/2002/07/owl#Class')
);

// クエリ
const results = store.getQuads(
  null,  // 任意のsubject
  namedNode('http://www.w3.org/1999/02/22-rdf-syntax-ns#type'),
  null   // 任意のobject
);
```

#### 3.3.2 推論エンジン

オントロジーに基づく推論を実行します。

```typescript
import { Reasoner } from '@nahisaho/musubix-ontology-mcp';

const reasoner = new Reasoner(store);

// 組み込みルールで推論
await reasoner.infer({
  rules: ['rdfs', 'owl-lite'],
});

// カスタムルール追加
reasoner.addRule({
  name: 'transitivity-rule',
  condition: '?a sdd:dependsOn ?b . ?b sdd:dependsOn ?c',
  conclusion: '?a sdd:transitivelyDependsOn ?c',
});

// 推論実行
const inferred = await reasoner.query({
  subject: 'comp:UserService',
  predicate: 'sdd:transitivelyDependsOn',
});
```

#### 3.3.3 整合性検証

オントロジーの整合性をチェックします。

```typescript
import { ConsistencyValidator } from '@nahisaho/musubix-ontology-mcp';

const validator = new ConsistencyValidator(store);

// 整合性検証
const result = await validator.validate();

// 結果
// {
//   valid: false,
//   violations: [
//     {
//       type: 'domain-violation',
//       subject: 'req:REQ-001',
//       predicate: 'sdd:implements',
//       message: 'sdd:implements requires subject of type sdd:Design'
//     }
//   ]
// }

// 循環依存検出
const circular = await validator.checkCircular({
  predicate: 'sdd:dependsOn',
});
```

### 3.4 MCPツール

| ツール名 | 説明 |
|---------|------|
| `ontology_query` | オントロジーグラフへのクエリ |
| `ontology_infer` | 推論実行 |
| `consistency_validate` | 整合性検証 |
| `validate_triple` | トリプル事前検証 |
| `check_circular` | 循環依存検出 |

---

## 4. Wake-Sleep

### 4.1 概要

`@nahisaho/musubix-wake-sleep` は、Wake-Sleepアルゴリズムに基づく継続的学習サイクルを実装します。

### 4.2 アーキテクチャ

```
packages/wake-sleep/src/
├── cycle/
│   ├── wake-sleep-cycle.ts  # メインサイクル
│   ├── scheduler.ts         # スケジューラー
│   └── state-machine.ts     # 状態管理
├── wake/
│   ├── observer.ts          # コード観察
│   ├── extractor.ts         # パターン抽出
│   └── updater.ts           # 知識更新
├── sleep/
│   ├── consolidator.ts      # パターン統合
│   ├── compressor.ts        # 圧縮処理
│   └── optimizer.ts         # メモリ最適化
├── bridge/
│   └── pattern-ontology-bridge.ts  # パターン↔オントロジー変換
└── index.ts
```

### 4.3 Wake-Sleepサイクル

```
┌─────────────────────────────────────────────────────────────┐
│                    Wake-Sleep Cycle                          │
└─────────────────────────────────────────────────────────────┘

                    ┌─────────────┐
                    │    Idle     │
                    └──────┬──────┘
                           │ trigger
                           ▼
            ┌──────────────────────────┐
            │       Wake Phase         │
            │  ┌────────────────────┐  │
            │  │     Observe        │  │
            │  └─────────┬──────────┘  │
            │            ▼             │
            │  ┌────────────────────┐  │
            │  │     Extract        │  │
            │  └─────────┬──────────┘  │
            │            ▼             │
            │  ┌────────────────────┐  │
            │  │     Update KG      │  │
            │  └────────────────────┘  │
            └────────────┬─────────────┘
                         │
                         ▼
            ┌──────────────────────────┐
            │      Sleep Phase         │
            │  ┌────────────────────┐  │
            │  │   Consolidate      │  │
            │  └─────────┬──────────┘  │
            │            ▼             │
            │  ┌────────────────────┐  │
            │  │     Compress       │  │
            │  └─────────┬──────────┘  │
            │            ▼             │
            │  ┌────────────────────┐  │
            │  │     Optimize       │  │
            │  └────────────────────┘  │
            └────────────┬─────────────┘
                         │
                         ▼
                    ┌─────────────┐
                    │    Idle     │
                    └─────────────┘
```

### 4.4 主要機能

#### 4.4.1 サイクル制御

```typescript
import { WakeSleepCycle } from '@nahisaho/musubix-wake-sleep';

const cycle = new WakeSleepCycle({
  patternLibrary: patternLib,
  ontologyStore: ontologyStore,
  schedule: {
    wakeInterval: 3600,    // 1時間ごとにWake
    sleepAfterWake: true,  // Wake後に自動Sleep
  },
});

// サイクル開始
await cycle.start();

// 手動トリガー
await cycle.triggerWake();
await cycle.triggerSleep();

// 状態確認
const status = cycle.getStatus();
// { phase: 'idle', lastWake: '...', lastSleep: '...' }
```

#### 4.4.2 Wakeフェーズ

```typescript
import { WakePhase } from '@nahisaho/musubix-wake-sleep';

const wake = new WakePhase({
  observers: ['file-system', 'git-changes', 'test-results'],
});

// コード観察
const observations = await wake.observe({
  paths: ['./src'],
  since: lastWakeTime,
});

// パターン抽出
const patterns = await wake.extractPatterns(observations);

// 知識グラフ更新
await wake.updateKnowledge(patterns);
```

#### 4.4.3 Sleepフェーズ

```typescript
import { SleepPhase } from '@nahisaho/musubix-wake-sleep';

const sleep = new SleepPhase({
  compressionThreshold: 0.8,
  retentionPolicy: {
    minConfidence: 0.5,
    minOccurrences: 2,
  },
});

// パターン統合
const consolidated = await sleep.consolidate();

// 圧縮
const compressed = await sleep.compress(consolidated);

// メモリ最適化
await sleep.optimize({
  pruneUnused: true,
  defragment: true,
});
```

### 4.5 パターン-オントロジーブリッジ

パターンとオントロジー間の相互変換を行います。

```typescript
import { PatternOntologyBridge } from '@nahisaho/musubix-wake-sleep';

const bridge = new PatternOntologyBridge({
  patternLibrary,
  ontologyStore,
});

// パターン → オントロジー
const triples = bridge.patternToTriples(pattern);
await ontologyStore.addQuads(triples);

// オントロジー → パターン
const pattern = bridge.triplesToPattern(triples);
await patternLibrary.store(pattern);
```

---

## 5. SDD Ontology

### 5.1 概要

`@nahisaho/musubix-sdd-ontology` は、SDD（Symbolic-Driven Development）方法論のオントロジー定義を提供します。

### 5.2 オントロジー構造

```
packages/sdd-ontology/src/
├── schema/
│   ├── sdd.ttl              # SDDコアオントロジー
│   ├── requirements.ttl     # 要件オントロジー
│   ├── design.ttl           # 設計オントロジー
│   ├── code.ttl             # コードオントロジー
│   └── traceability.ttl     # トレーサビリティオントロジー
├── rules/
│   ├── ears-rules.ttl       # EARS推論ルール
│   ├── c4-rules.ttl         # C4推論ルール
│   └── quality-rules.ttl    # 品質推論ルール
├── loader.ts                # オントロジーローダー
└── index.ts
```

### 5.3 SDDコアオントロジー

```turtle
@prefix sdd: <http://musubix.dev/sdd#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

# === クラス定義 ===

sdd:Artifact a owl:Class ;
    rdfs:label "Software Artifact" ;
    rdfs:comment "Base class for all SDD artifacts" .

sdd:Requirement a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Requirement" .

sdd:Design a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Design" .

sdd:Code a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Code" .

sdd:Test a owl:Class ;
    rdfs:subClassOf sdd:Artifact ;
    rdfs:label "Test" .

# === EARSパターン ===

sdd:EARSPattern a owl:Class ;
    rdfs:label "EARS Pattern" .

sdd:UbiquitousPattern a owl:Class ;
    rdfs:subClassOf sdd:EARSPattern ;
    rdfs:label "Ubiquitous Pattern" .

sdd:EventDrivenPattern a owl:Class ;
    rdfs:subClassOf sdd:EARSPattern ;
    rdfs:label "Event-Driven Pattern" .

sdd:StateDrivenPattern a owl:Class ;
    rdfs:subClassOf sdd:EARSPattern ;
    rdfs:label "State-Driven Pattern" .

sdd:UnwantedPattern a owl:Class ;
    rdfs:subClassOf sdd:EARSPattern ;
    rdfs:label "Unwanted Pattern" .

sdd:OptionalPattern a owl:Class ;
    rdfs:subClassOf sdd:EARSPattern ;
    rdfs:label "Optional Pattern" .

# === プロパティ定義 ===

sdd:implements a owl:ObjectProperty ;
    rdfs:domain sdd:Design ;
    rdfs:range sdd:Requirement ;
    rdfs:label "implements" .

sdd:realizedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Requirement ;
    rdfs:range sdd:Code ;
    rdfs:label "realizedBy" .

sdd:testedBy a owl:ObjectProperty ;
    rdfs:domain sdd:Code ;
    rdfs:range sdd:Test ;
    rdfs:label "testedBy" .

sdd:hasPattern a owl:ObjectProperty ;
    rdfs:domain sdd:Requirement ;
    rdfs:range sdd:EARSPattern ;
    rdfs:label "hasPattern" .

sdd:priority a owl:DatatypeProperty ;
    rdfs:domain sdd:Requirement ;
    rdfs:range xsd:string ;
    rdfs:label "priority" .
```

### 5.4 推論ルール

```turtle
@prefix sdd: <http://musubix.dev/sdd#> .
@prefix rule: <http://musubix.dev/rules#> .

# トレーサビリティ推論
rule:TraceabilityInference a rule:Rule ;
    rule:condition """
        ?req a sdd:Requirement .
        ?des sdd:implements ?req .
        ?code sdd:realizes ?des .
    """ ;
    rule:conclusion """
        ?req sdd:realizedBy ?code .
    """ .

# テストカバレッジ推論
rule:TestCoverageInference a rule:Rule ;
    rule:condition """
        ?code a sdd:Code .
        ?test sdd:tests ?code .
        ?code sdd:realizes ?des .
        ?des sdd:implements ?req .
    """ ;
    rule:conclusion """
        ?req sdd:hasCoverage true .
    """ .

# 依存関係推移閉包
rule:TransitiveDependency a rule:Rule ;
    rule:condition """
        ?a sdd:dependsOn ?b .
        ?b sdd:dependsOn ?c .
    """ ;
    rule:conclusion """
        ?a sdd:transitivelyDependsOn ?c .
    """ .
```

### 5.5 使用例

```typescript
import { SDDOntology } from '@nahisaho/musubix-sdd-ontology';

const ontology = new SDDOntology();

// オントロジーをN3Storeにロード
const store = await ontology.load();

// 推論ルールを適用
await ontology.applyRules(store);

// 要件に対するトレーサビリティ検証
const coverage = await ontology.checkTraceability(store, 'REQ-001');
```

---

## 6. 学習フロー統合

### 6.1 全体フロー

```
┌─────────────────────────────────────────────────────────────┐
│                   Complete Learning Flow                     │
└─────────────────────────────────────────────────────────────┘

1. [Input] Code Changes
       │
       ▼
2. [Pattern MCP] Extract patterns from code
       │
       ├─── AST Analysis
       ├─── Feature Extraction  
       └─── Pattern Detection
       │
       ▼
3. [Ontology MCP] Map patterns to ontology
       │
       ├─── Triple Generation
       ├─── Schema Validation
       └─── Consistency Check
       │
       ▼
4. [Wake-Sleep] Consolidate and optimize
       │
       ├─── Wake: Update Knowledge
       └─── Sleep: Compress & Prune
       │
       ▼
5. [SDD Ontology] Apply inference rules
       │
       ├─── Traceability Inference
       ├─── Coverage Analysis
       └─── Quality Metrics
       │
       ▼
6. [Output] Updated Knowledge Graph
```

### 6.2 統合API

```typescript
import { LearningSystem } from '@nahisaho/musubix-core';

const learningSystem = new LearningSystem({
  patternMCP: patternMCP,
  ontologyMCP: ontologyMCP,
  wakeSleep: wakeSleepCycle,
  sddOntology: sddOntology,
});

// コード変更から学習
await learningSystem.learnFromCode({
  files: ['src/user-service.ts'],
  context: 'user-authentication',
});

// フィードバックから学習
await learningSystem.learnFromFeedback({
  patternId: 'pattern-123',
  feedback: 'accept',  // 'accept' | 'reject' | 'modify'
  comment: 'Good pattern for DI',
});

// 推奨パターン取得
const recommendations = await learningSystem.getRecommendations({
  context: 'implementing-user-service',
  maxResults: 5,
});
```

---

## 7. CLI コマンド

```bash
# 学習ダッシュボード
npx musubix learn status

# パターン操作
npx musubix learn patterns
npx musubix learn add-pattern <name>
npx musubix learn remove-pattern <id>

# フィードバック
npx musubix learn feedback <id>

# 推奨
npx musubix learn recommend

# Wake-Sleepサイクル
npx musubix learn wake
npx musubix learn sleep
npx musubix learn decay

# データ管理
npx musubix learn export --output patterns.json
npx musubix learn import patterns.json

# オントロジー
npx musubix ontology validate -f knowledge.ttl
npx musubix ontology check-circular -f knowledge.ttl
npx musubix ontology stats -f knowledge.ttl
```

---

## 8. 設定

### 8.1 環境変数

| 変数名 | 説明 | デフォルト |
|--------|------|-----------|
| `MUSUBIX_LEARNING_PATH` | 学習データパス | `~/.musubix/learning` |
| `MUSUBIX_PATTERN_THRESHOLD` | パターン登録閾値 | `0.8` |
| `MUSUBIX_WAKE_INTERVAL` | Wake間隔（秒） | `3600` |
| `MUSUBIX_SLEEP_AFTER_WAKE` | Wake後自動Sleep | `true` |

### 8.2 設定ファイル

`learning.config.json`:

```json
{
  "patterns": {
    "extractionThreshold": 0.7,
    "compressionThreshold": 0.8,
    "minOccurrences": 3,
    "retentionDays": 90
  },
  "wakeSleep": {
    "wakeInterval": 3600,
    "sleepAfterWake": true,
    "observers": ["file-system", "git-changes"]
  },
  "ontology": {
    "schemaPath": "./schema",
    "rulesPath": "./rules",
    "inferenceEnabled": true
  }
}
```

---

## 9. 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [MUSUBIX-Overview.md](MUSUBIX-Overview.md) | 全体概要 |
| [MUSUBIX-Core.md](MUSUBIX-Core.md) | Coreパッケージ |
| [MUSUBIX-YATA.md](MUSUBIX-YATA.md) | YATAシステム |
| [API-REFERENCE.md](API-REFERENCE.md) | APIリファレンス |

---

**© 2026 MUSUBIX Project**
