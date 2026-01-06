# MUSUBIX ユーザーガイド

> Neuro-Symbolic AI による仕様駆動開発システム

## 目次

1. [はじめに](#はじめに)
2. [インストール](#インストール)
3. [CLIの使い方](#cliの使い方)
4. [クイックスタート](#クイックスタート)
5. [基本的なワークフロー](#基本的なワークフロー)
6. [要件フェーズ](#要件フェーズ)
7. [設計フェーズ](#設計フェーズ)
8. [タスクフェーズ](#タスクフェーズ)
9. [検証フェーズ](#検証フェーズ)
10. [自己学習システム](#自己学習システム)
11. [C4コード生成](#c4コード生成)
12. [シンボリック推論](#シンボリック推論) *(v1.2.0)*
13. [正誤性検証](#正誤性検証) *(v1.4.1)*
14. [高度な推論](#高度な推論) *(v1.4.5)*
15. [対話的REPLモード](#対話的replモード) *(v1.5.0)*
16. [YATA Local](#yata-local) *(v1.6.3)*
17. [YATA Global](#yata-global) *(v1.6.3)*
18. [KGPR - Knowledge Graph Pull Request](#kgpr---knowledge-graph-pull-request) *(v1.6.4)*
19. [YATA プラットフォーム拡張](#yata-プラットフォーム拡張) *(v1.7.0)*
20. [形式検証](#形式検証) *(v1.7.5)*
21. [セキュリティ分析](#セキュリティ分析) *(v1.8.0)*
22. [MCPサーバー連携](#mcpサーバー連携)
23. [YATA知識グラフ](#yata知識グラフ)
24. [ベストプラクティス](#ベストプラクティス)
25. [トラブルシューティング](#トラブルシューティング)

---

## はじめに

### MUSUBIXとは？

MUSUBIXは、**MUSUBI**（仕様駆動開発LLM）と**YATA**（知識グラフ）を組み合わせた**ニューロシンボリックAIシステム**です。

```
MUSUBIX = MUSUBI (LLM) + YATA (Knowledge Graph)
```

### 主な特徴

- 🎯 **仕様駆動開発**: EARS形式の要件から実装まで一貫した開発
- 🏛️ **9条憲法**: 品質を保証する9つの原則に基づく開発
- 🔗 **完全なトレーサビリティ**: 要件→設計→タスク→テストの追跡
- 🧠 **知識グラフ統合**: YATAによるコンテキスト認識
- 🌐 **MCP対応**: Model Context Protocol による柔軟な統合

### 9条憲法（Constitutional Articles）

| 条項 | 名称 | 説明 |
|------|------|------|
| I | プロジェクトメモリ | 一貫したプロジェクトコンテキストの維持 |
| II | 要件仕様 | EARS形式の完全な要件定義 |
| III | 設計文書 | C4モデル + ADRによる設計 |
| IV | タスク分解 | トレーサブルなタスク生成 |
| V | トレーサビリティ | 双方向の追跡性 |
| VI | 説明可能性 | AI判断の透明性 |
| VII | 統合性 | シームレスな統合 |
| VIII | 適応性 | 柔軟な方法論対応 |
| IX | 品質保証 | 継続的な品質確保 |

---

## インストール

### 前提条件

| 項目 | 要件 |
|------|------|
| **Node.js** | >= 20.0.0 |
| **npm** | >= 10.0.0 |
| **TypeScript** | >= 5.3（開発時） |

### 方法1: npm グローバルインストール（推奨）

```bash
# グローバルインストール
npm install -g musubix

# バージョン確認
musubix --version
musubix-mcp --version
```

### 方法2: npx で直接実行

```bash
# インストールなしで実行
npx musubix --help
npx musubix init my-project

# MCPサーバー起動
npx @nahisaho/musubix-mcp-server
npx musubix-mcp --transport stdio
```

### 方法3: プロジェクトへのインストール

```bash
# 個別パッケージのインストール
npm install @nahisaho/musubix-core
npm install @nahisaho/musubix-mcp-server
npm install @nahisaho/musubix-yata-client  # YATA連携用（オプション）
```

### 方法4: ソースからビルド

```bash
# リポジトリをクローン
git clone https://github.com/nahisaho/MUSUBIX.git
cd MUSUBIX

# 依存関係インストール & ビルド
npm install
npm run build
```

### YATA のインストール（オプション）

知識グラフ機能を使用する場合は、YATA を別途インストールします：

```bash
# YATA リポジトリをクローン
git clone https://github.com/nahisaho/YATA.git
cd YATA

# uv で依存関係をインストール
uv sync --all-packages

# サーバー起動
uv run yata serve
```

詳細は [INSTALL-GUIDE.ja.md](INSTALL-GUIDE.ja.md) を参照してください。

### プロジェクト初期化

```bash
# MUSUBIXプロジェクトの初期化
musubix init my-project
# または
npx musubix init my-project

# steering ディレクトリの確認
ls steering/
# product.md  structure.md  tech.md  rules/
```

---

## CLIの使い方

### musubix コマンド

MUSUBIXのメインCLI：

```bash
# ヘルプ表示
musubix --help

# バージョン表示
musubix --version

# プロジェクト初期化
musubix init [path] [options]

# オプション
#   --name <name>      プロジェクト名
#   --template <type>  テンプレート（default, minimal, full）
#   --force            既存ファイルを上書き
#   --json             JSON形式で出力
#   --verbose          詳細出力
```

### musubix-mcp コマンド

MCPサーバーの起動：

```bash
# ヘルプ表示
musubix-mcp --help

# stdio モードで起動（デフォルト）
musubix-mcp
musubix-mcp --transport stdio

# SSE モードで起動
musubix-mcp --transport sse --port 8080
```

| オプション | 説明 |
|-----------|------|
| `-t, --transport` | トランスポート: `stdio` または `sse` |
| `-p, --port` | SSE モードのポート（デフォルト: 3000） |
| `-h, --help` | ヘルプ表示 |
| `-v, --version` | バージョン表示 |

---

## クイックスタート

### 5分で始めるMUSUBIX

```typescript
import {
  createRequirementsAnalyzer,
  createC4ModelGenerator,
  createTaskGenerator,
  createConstitutionalValidator
} from '@nahisaho/musubix-core';

// 1. 要件の分析
const analyzer = createRequirementsAnalyzer();
const requirement = analyzer.analyze(`
  ユーザーがログインボタンをクリックしたとき、
  システムは認証画面を表示しなければならない。
`);

console.log('要件ID:', requirement.id);
console.log('タイプ:', requirement.type);

// 2. 設計の生成
const c4Generator = createC4ModelGenerator();
const diagram = c4Generator.generateContext({
  name: '認証システム',
  description: 'ユーザー認証を管理するシステム'
});

console.log('C4図:', diagram.export('mermaid'));

// 3. タスクの生成
const taskGenerator = createTaskGenerator();
const tasks = taskGenerator.generate([requirement]);

console.log('生成されたタスク:', tasks.length);

// 4. 検証
const validator = createConstitutionalValidator();
const result = validator.validate(requirement);

console.log('検証結果:', result.valid ? '合格' : '不合格');
```

---

## 基本的なワークフロー

### SDDワークフロー概要

```
┌─────────────────────────────────────────────────────────────┐
│                    SDDワークフロー                           │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ① ステアリング     プロジェクトコンテキストの設定          │
│       ↓                                                      │
│  ② 要件定義        EARS形式で要件を記述                     │
│       ↓                                                      │
│  ③ 設計            C4モデル + ADRの作成                     │
│       ↓                                                      │
│  ④ タスク生成      実装タスクへの分解                       │
│       ↓                                                      │
│  ⑤ 実装            コード生成・開発                         │
│       ↓                                                      │
│  ⑥ 検証            憲法に基づく検証                         │
│       ↓                                                      │
│  ⑦ レビュー        品質レビューゲート                       │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### ステアリングファイル

プロジェクトの基盤となる設定ファイル：

```
steering/
├── product.md      # プロダクト情報
├── structure.md    # アーキテクチャパターン
├── tech.md         # 技術スタック
└── rules/
    └── constitution.md  # 9条憲法
```

---

## 要件フェーズ

### EARS形式による要件定義

**EARS (Easy Approach to Requirements Syntax)** は、明確で検証可能な要件を書くための形式です。

#### 基本パターン

```
[条件] [主語] [助動詞] [動作] [目的語]
```

#### 例

```
【機能要件】
ユーザーがログインフォームで正しい認証情報を入力したとき、
システムはダッシュボード画面を表示しなければならない。

【非機能要件】
システムは、すべてのAPIリクエストに対して
500ミリ秒以内にレスポンスを返さなければならない。

【制約】
システムは、個人情報保護法に準拠して
ユーザーデータを暗号化しなければならない。
```

### RequirementsAnalyzer の使用

```typescript
import { createRequirementsAnalyzer } from '@nahisaho/musubix-core';

const analyzer = createRequirementsAnalyzer({
  strictMode: true,    // 厳密な検証
  validateEARS: true,  // EARS形式の検証
  autoClassify: true   // 自動分類
});

// 要件テキストの分析
const result = analyzer.analyze(`
  ユーザーが商品をカートに追加したとき、
  システムはカート内の合計金額を更新しなければならない。
`);

console.log('ID:', result.id);           // REQ-001
console.log('タイプ:', result.type);     // functional
console.log('優先度:', result.priority); // must
```

### RequirementsDecomposer の使用

複雑な要件を小さな単位に分解：

```typescript
import { createRequirementsDecomposer } from '@nahisaho/musubix-core';

const decomposer = createRequirementsDecomposer({
  maxDepth: 4,        // 最大分解深度
  targetUnitSize: 4   // 目標単位サイズ（時間）
});

const result = decomposer.decompose(requirement, 'functional');

console.log('分解単位数:', result.units.length);
console.log('推定総工数:', result.stats.estimatedTotalEffort);

// Markdownでエクスポート
const markdown = decomposer.exportMarkdown(result);
```

---

## 設計フェーズ

### C4モデルの生成

C4モデルは4つのレベルでシステムを表現します：

1. **Context**: システムの境界と外部エンティティ
2. **Container**: アプリケーション・データストアの構成
3. **Component**: コンテナ内のコンポーネント
4. **Code**: コードレベルの詳細

```typescript
import { createC4ModelGenerator } from '@nahisaho/musubix-core';

const generator = createC4ModelGenerator({
  defaultFormat: 'mermaid'
});

// コンテキスト図の生成
const contextDiagram = generator.generateContext({
  name: 'Eコマースシステム',
  description: 'オンラインショッピングプラットフォーム',
  actors: [
    { name: '顧客', description: '商品を購入するユーザー' },
    { name: '管理者', description: 'システムを管理するスタッフ' }
  ],
  externalSystems: [
    { name: '決済システム', description: 'クレジットカード決済' },
    { name: '配送システム', description: '物流管理' }
  ]
});

// Mermaidでエクスポート
console.log(generator.export(contextDiagram, 'mermaid'));
```

### ADR（アーキテクチャ決定記録）

重要なアーキテクチャ決定を記録：

```typescript
import { createADRGenerator } from '@nahisaho/musubix-core';

const adrGenerator = createADRGenerator({
  template: 'madr',
  outputFormat: 'markdown'
});

const adr = adrGenerator.generate({
  title: 'TypeScriptの採用',
  status: 'accepted',
  context: 'プロジェクトの言語選定が必要',
  decision: 'TypeScriptを採用する',
  rationale: '型安全性とIDEサポートの向上',
  consequences: {
    positive: ['バグの早期発見', 'リファクタリングの容易さ'],
    negative: ['学習コスト', 'ビルド時間の増加']
  },
  alternatives: [
    { name: 'JavaScript', reason: '型がないため却下' },
    { name: 'Flow', reason: 'エコシステムが小さいため却下' }
  ]
});

console.log(adr.export());
```

---

## タスクフェーズ

### タスクの自動生成

要件から実装タスクを生成：

```typescript
import { createTaskGenerator } from '@nahisaho/musubix-core';

const taskGenerator = createTaskGenerator({
  estimateEffort: true,   // 工数見積もり
  includeTests: true,     // テストタスクを含む
  assignmentStrategy: 'balanced'
});

const tasks = taskGenerator.generate(requirements);

for (const task of tasks) {
  console.log(`
    タスク: ${task.id}
    タイトル: ${task.title}
    要件参照: ${task.requirementRef}
    推定工数: ${task.estimatedHours}時間
    ステータス: ${task.status}
  `);
}
```

### タスクの優先順位付け

```typescript
// 優先順位付け
const prioritized = taskGenerator.prioritize(tasks, {
  criteria: ['dependency', 'risk', 'value'],
  weights: [0.4, 0.3, 0.3]
});

console.log('優先度順タスク:');
prioritized.forEach((task, index) => {
  console.log(`${index + 1}. ${task.title} (スコア: ${task.priorityScore})`);
});
```

---

## 検証フェーズ

### 憲法に基づく検証

```typescript
import { createConstitutionalValidator } from '@nahisaho/musubix-core';

const validator = createConstitutionalValidator({
  strictMode: true,
  articles: ['all']  // すべての条項を検証
});

const result = validator.validate(artifact);

console.log('検証結果:', result.valid ? '✅ 合格' : '❌ 不合格');
console.log('スコア:', result.score);
console.log('エラー数:', result.errors.length);
console.log('警告数:', result.warnings.length);

// 詳細レポート
if (!result.valid) {
  for (const error of result.errors) {
    console.log(`
      条項: ${error.article}
      メッセージ: ${error.message}
      推奨対応: ${error.recommendation}
    `);
  }
}
```

### カバレッジの確認

```typescript
console.log('カバレッジ:');
console.log(`  要件: ${result.coverage.requirements}%`);
console.log(`  設計: ${result.coverage.design}%`);
console.log(`  タスク: ${result.coverage.tasks}%`);
console.log(`  テスト: ${result.coverage.tests}%`);
```

---

## 自己学習システム

MUSUBIXには、フィードバック収集とパターン抽出により改善を続ける自己学習システムが含まれています。

### 学習CLIコマンド

```bash
# 学習状態ダッシュボードを表示
musubix learn status

# 成果物にフィードバックを記録
musubix learn feedback <artifact-id> --type accept|reject|modify --artifact-type requirement|design|code|test --reason "説明"

# 学習済みパターン一覧を表示
musubix learn patterns

# パターンを手動登録
musubix learn add-pattern <name> --category code|design|requirement|test --action prefer|avoid --description "パターンの説明"

# パターンを削除
musubix learn remove-pattern <pattern-id>

# コンテキストベースの推奨を取得
musubix learn recommend --artifact-type code

# 未使用パターンの減衰を適用
musubix learn decay

# 学習データをエクスポート（v1.4.0 拡張）
musubix learn export --output learning-data.json
# オプション:
#   --privacy-filter         機密情報を除去（APIキー、パスワード等）
#   --patterns-only          パターンのみエクスポート
#   --feedback-only          フィードバックのみエクスポート
#   --min-confidence <n>     最小信頼度（0-1）

# 学習データをインポート（v1.4.0 マージ戦略対応）
musubix learn import learning-data.json
# オプション:
#   --merge-strategy <skip|overwrite|merge>  重複の処理方法
#   --dry-run                                変更をプレビュー
#   --patterns-only                          パターンのみインポート
#   --feedback-only                          フィードバックのみインポート
```

### プログラムからの使用

```typescript
import { createLearningEngine } from '@nahisaho/musubix-core';

const learningEngine = createLearningEngine();

// フィードバックを記録
await learningEngine.recordFeedback({
  type: 'accept',
  artifactType: 'code',
  artifactId: 'AUTH-001',
  reason: 'JWT認証の良い実装'
});

// 推奨を取得
const recommendations = await learningEngine.getRecommendations({
  artifactType: 'code',
  context: 'authentication'
});

// 学習データをエクスポート
const data = await learningEngine.exportData();
```

### パターン抽出

類似のフィードバックが複数回（デフォルト閾値：3回）記録されると、パターンが自動的に抽出されます。

```typescript
// パターンは出現ごとに信頼度が上昇
// 高信頼度パターン（≥70%）は推奨に表示される
const stats = await learningEngine.getStats();
console.log(`総パターン数: ${stats.totalPatterns}`);
console.log(`高信頼度パターン: ${stats.highConfidencePatterns}`);
```

---

## C4コード生成

C4設計ドキュメントからTypeScriptスケルトンコードを生成します。

### CLIの使用

```bash
# C4設計からコード生成
musubix codegen generate design-c4.md --output src/

# 言語を指定
musubix codegen generate design-c4.md --output src/ --language typescript
```

### 生成されるコード構造

以下のようなコンポーネントを持つC4設計から：

| ID | Name | Type | Description |
|----|------|------|-------------|
| auth | AuthService | component | 認証 |

MUSUBIXは以下を生成します：

```typescript
// auth-service.ts
export interface IAuthService {
  authenticate(credentials: { username: string; password: string }): Promise<{ token: string }>;
  validate(token: string): Promise<boolean>;
}

export class AuthService implements IAuthService {
  async authenticate(credentials: { username: string; password: string }): Promise<{ token: string }> {
    // TODO: authenticateを実装
    throw new Error('Not implemented');
  }
  
  async validate(token: string): Promise<boolean> {
    // TODO: validateを実装
    throw new Error('Not implemented');
  }
}

export function createAuthService(): IAuthService {
  return new AuthService();
}
```

---

## シンボリック推論

*(v1.2.0 新機能)*

### 概要

シンボリック推論は、形式検証と知識グラフベースの推論を適用して、LLM出力を強化します。このハイブリッドアプローチ（ニューロシンボリック）は、ニューラルネットワークの創造性とシンボリックロジックの精度を組み合わせます。

### 主要コンポーネント

| コンポーネント | 説明 |
|--------------|------|
| `SemanticCodeFilterPipeline` | コード品質のためのLLM出力フィルタリング |
| `HallucinationDetector` | ハルシネーション（幻覚）出力の検出と防止 |
| `EarsToFormalSpecConverter` | EARS要件からZ3形式仕様への変換 |
| `Z3Adapter` | 形式検証のためのZ3ソルバーインターフェース |
| `QualityGateValidator` | 17品質ゲートチェックに対する検証 |

### 使用方法

#### セマンティックコードフィルタリング

```typescript
import { SemanticCodeFilterPipeline } from '@nahisaho/musubix-core';

const pipeline = new SemanticCodeFilterPipeline({
  enableHallucinationDetection: true,
  maxRetries: 3
});

const result = await pipeline.filter({
  code: generatedCode,
  context: { language: 'typescript', domain: 'authentication' }
});

if (result.isValid) {
  console.log('コードが検証に合格:', result.filteredCode);
} else {
  console.log('問題が検出されました:', result.issues);
}
```

#### ハルシネーション検出

```typescript
import { HallucinationDetector } from '@nahisaho/musubix-core';

const detector = new HallucinationDetector();

const analysis = await detector.analyze({
  response: llmResponse,
  groundTruth: knownFacts,
  context: projectContext
});

console.log('信頼度スコア:', analysis.confidence);
console.log('ハルシネーションリスク:', analysis.risks);
```

#### EARSから形式仕様への変換

```typescript
import { EarsToFormalSpecConverter } from '@nahisaho/musubix-core';

const converter = new EarsToFormalSpecConverter();

const formalSpec = await converter.convert({
  earsRequirement: 'WHEN user clicks login, THE system SHALL authenticate within 2 seconds',
  requirementId: 'REQ-AUTH-001'
});

// Z3互換の仕様を返す
console.log(formalSpec.z3Expression);
```

#### 品質ゲート検証

```typescript
import { QualityGateValidator } from '@nahisaho/musubix-core';

const validator = new QualityGateValidator();

const gateResult = await validator.validate({
  requirements: requirementsList,
  designs: designDocuments,
  tasks: taskList
});

console.log('全ゲート合格:', gateResult.allPassed);
console.log('ゲート詳細:', gateResult.gates);
// EARS準拠、トレーサビリティなど17の品質チェック
```

### 品質ゲートチェック

| ゲート | 説明 |
|--------|------|
| EARS準拠 | 要件がEARSパターンに従っているか |
| 一意のID | すべての成果物に一意の識別子があるか |
| トレーサビリティ | 完全なトレーサビリティチェーンが存在するか |
| 設計カバレッジ | すべての要件に設計があるか |
| タスクカバレッジ | すべての設計にタスクがあるか |
| 孤立なし | 孤立した要件やタスクがないか |
| 完全性 | すべての必須フィールドが存在するか |
| ... | その他10の品質チェック |

---

## 正誤性検証

*(v1.4.1 新機能)*

### 概要

正誤性検証は、知識グラフへのトリプル追加時にデータの整合性を確保します。OWL制約に基づいて違反を検出し、不正なデータの登録を防止します。

### 検証タイプ

| タイプ | 説明 | 重大度 |
|--------|------|--------|
| `disjoint-class-membership` | 排他的クラスの両方に所属 | error |
| `functional-property-violation` | 関数型プロパティに複数値 | error |
| `inverse-functional-violation` | 同じ値が複数の主語にマップ | error |
| `asymmetric-violation` | 非対称プロパティに逆方向が存在 | error |
| `irreflexive-violation` | 非反射プロパティで自己参照 | error |
| `duplicate-triple` | 完全一致の重複トリプル | warning |
| `circular-dependency` | subClassOfの循環チェーン | error |

### 使用方法

#### 検証付きトリプル追加

```typescript
import { N3Store } from '@nahisaho/musubix-ontology-mcp';

// 追加時検証を有効化
const store = new N3Store({}, true);

// 検証付き追加
const result = store.addTripleValidated({
  subject: 'http://example.org/Person1',
  predicate: 'http://example.org/hasMother',
  object: 'http://example.org/Mother1'
});

if (!result.success) {
  console.error('検証エラー:', result.validation.errors);
}
```

#### ストア全体の整合性チェック

```typescript
// ストア全体をチェック
const consistency = store.checkConsistency();

if (!consistency.consistent) {
  for (const violation of consistency.violations) {
    console.log(`${violation.type}: ${violation.message}`);
    console.log('関連トリプル:', violation.triples);
  }
  
  // 修正提案を取得
  for (const suggestion of consistency.suggestions) {
    console.log(`提案: ${suggestion.suggestion}`);
    console.log(`自動修正可能: ${suggestion.autoFixable}`);
  }
}
```

#### 直接バリデータを使用

```typescript
import { ConsistencyValidator } from '@nahisaho/musubix-ontology-mcp';

const validator = new ConsistencyValidator({
  checkDisjointClasses: true,
  checkFunctionalProperties: true,
  checkDuplicates: true,
  checkCircularDependencies: true
});

// 追加前に検証
const validation = validator.validateTriple(newTriple, existingTriples);
if (!validation.valid) {
  console.error(validation.errors);
}

// 重複を検出
const duplicates = validator.findDuplicates(allTriples);
const semanticDuplicates = validator.findSemanticDuplicates(allTriples);
```

---

## 高度な推論

*(v1.4.5 新機能)*

### 概要

高度な推論は、知識グラフにOWL 2 RL推論とDatalog評価機能を提供します。暗黙的な事実の実体化、ルールベースの推論、人間が理解しやすい説明の生成をサポートします。

### 主要コンポーネント

| コンポーネント | 説明 |
|--------------|------|
| `OWL2RLReasoner` | 20以上のビルトインルールを持つOWL 2 RL推論エンジン |
| `DatalogEngine` | 階層化評価対応のDatalogエンジン |
| `InferenceExplainer` | 自然言語での説明生成 |
| `ProgressReporter` | リアルタイム推論進捗追跡 |

### OWL 2 RL 推論

```typescript
import { OWL2RLReasoner } from '@nahisaho/musubix-ontology-mcp';

const reasoner = new OWL2RLReasoner({
  maxIterations: 100,
  enablePropertyChains: true,
  enableInverseProperties: true
});

// ストアに対して推論を実行
const result = await reasoner.reason(store, {
  onProgress: (progress) => {
    console.log(`反復 ${progress.iteration}: ${progress.newTriples} 新規トリプル`);
  }
});

console.log(`${result.inferredCount} 個の新しい事実を推論`);
console.log(`適用ルール: ${result.rulesApplied.join(', ')}`);
```

### OWL 2 RL ルール

| ルールID | 名称 | 説明 |
|---------|------|------|
| `prp-dom` | Property Domain | プロパティのドメインから型を推論 |
| `prp-rng` | Property Range | プロパティのレンジから型を推論 |
| `prp-inv1/2` | Inverse Properties | 逆関係を推論 |
| `prp-trp` | Transitive Properties | 推移的プロパティを連鎖 |
| `prp-symp` | Symmetric Properties | 対称関係を推論 |
| `cax-sco` | SubClassOf | クラスメンバーシップを伝播 |
| `scm-spo` | SubPropertyOf | プロパティの包摂関係 |
| `eq-rep-s/p/o` | SameAs Replacement | 同一個体の置換 |

### Datalog 評価

```typescript
import { DatalogEngine } from '@nahisaho/musubix-ontology-mcp';

const engine = new DatalogEngine();

// ルールを定義
const rules = [
  {
    head: { predicate: 'ancestor', args: ['?x', '?y'] },
    body: [
      { predicate: 'parent', args: ['?x', '?y'] }
    ]
  },
  {
    head: { predicate: 'ancestor', args: ['?x', '?z'] },
    body: [
      { predicate: 'parent', args: ['?x', '?y'] },
      { predicate: 'ancestor', args: ['?y', '?z'] }
    ]
  }
];

// ルールを評価
const result = await engine.evaluate(rules, facts, {
  onProgress: (progress) => {
    console.log(`階層 ${progress.stratum}: ${progress.rule} を評価中`);
  }
});

console.log(`${result.derivedFacts.length} 個の新しい事実を導出`);
```

### 推論説明

```typescript
import { InferenceExplainer, ExplanationFormat } from '@nahisaho/musubix-ontology-mcp';

const explainer = new InferenceExplainer(reasoner.getProvenanceLog());

// 特定のトリプルの説明を取得
const explanation = explainer.explain(
  'http://example.org/Animal',
  'rdf:type',
  'owl:Class',
  ExplanationFormat.TEXT
);

console.log(explanation);
// 出力: "Animal は owl:Class として宣言されているため Class です（ルール cax-sco）"

// HTML形式の説明を生成
const htmlExplanation = explainer.explain(
  subject, predicate, object,
  ExplanationFormat.HTML
);
```

### 進捗レポート

```typescript
import { createProgressReporter } from '@nahisaho/musubix-ontology-mcp';

const reporter = createProgressReporter({
  onProgress: (info) => {
    console.log(`フェーズ: ${info.phase}`);
    console.log(`反復: ${info.iteration}/${info.maxIterations}`);
    console.log(`トリプル数: ${info.totalTriples}`);
    console.log(`新規推論: ${info.newInferences}`);
  },
  throttleMs: 500  // 500ms間隔でレポート
});

await reasoner.reason(store, { progressReporter: reporter });
```

---

## 対話的REPLモード

*(v1.5.0 新規、v1.6.0 強化)*

MUSUBIXは、リアルタイムでコマンドを実行・探索できる対話的REPLシェルを提供します。

### REPLの起動

```bash
# 対話的REPLを起動
musubix repl

# カスタム履歴ファイルを指定
musubix repl --history ~/.musubix-repl-history

# カラー表示なし
musubix repl --no-color
```

### REPL機能

| 機能 | 説明 |
|------|------|
| コマンド補完 | TABキーでコマンド・オプションを補完 |
| 履歴ナビゲーション | 上下矢印、履歴検索 |
| セッション変数 | `$name=value` で設定、`$name` で参照 |
| 出力フォーマット | JSON、YAML、テーブル自動整形 |
| CLI統合 | CLIコマンドをそのまま実行可能 |

### 基本的な使い方

```bash
musubix> help                          # すべてのコマンドを表示
musubix> help requirements             # コマンド詳細を表示
musubix> requirements analyze input.md # CLIコマンドを実行
musubix> $project=my-app               # セッション変数を設定
musubix> design generate $project      # 変数をコマンドで使用
musubix> history                       # コマンド履歴を表示
musubix> exit                          # REPLを終了
```

### セッション変数

```bash
# 変数の設定
musubix> $req=REQ-001
musubix> $file=./docs/requirements.md

# コマンドで使用
musubix> requirements validate $file
musubix> trace impact $req

# 特殊変数: $_ は前回の実行結果を保持
musubix> requirements analyze input.md
musubix> $_                           # 前回の結果にアクセス
```

### 出力フォーマット

```bash
# 自動検出（デフォルト）
musubix> learn status

# JSON出力を強制
musubix> set format json
musubix> learn patterns

# YAML出力を強制
musubix> set format yaml

# テーブル出力を強制
musubix> set format table
```

### 履歴管理

```bash
# 最近のコマンドを表示
musubix> history

# 履歴を検索（Ctrl+Rスタイル）
musubix> history search requirements

# 履歴をクリア
musubix> history clear
```

### REPLコンポーネント

| コンポーネント | 役割 |
|---------------|------|
| `ReplEngine` | REPLメインコントローラー |
| `CommandCompleter` | TAB補完プロバイダー |
| `HistoryManager` | コマンド履歴の永続化 |
| `SessionState` | 変数ストレージ |
| `OutputFormatter` | JSON/YAML/テーブル出力 |
| `PromptRenderer` | 動的プロンプト表示 |

---

## YATA Local

*(v1.6.3 新規)*

YATA Localは、高性能なSQLiteベースのローカル知識グラフです。推論機能を内蔵し、シングルユーザー・オフライン環境でデータ主権と速度が重要な場合に最適です。

### 機能

| 機能 | 説明 |
|------|------|
| **SQLiteストレージ** | WALモードで並行読み取り、シングルライター |
| **全文検索** | FTS5ベースのトリプル検索 |
| **グラフ探索** | BFS/DFSアルゴリズム、深度制御 |
| **推論エンジン** | 4つのOWL-liteルール（推移性、対称性、逆関係、ドメイン/レンジ） |
| **制約** | 4つの検証ルール（カーディナリティ、排他、一意性、必須） |
| **ACIDトランザクション** | 完全なトランザクションサポート |

### インストール

```bash
npm install @nahisaho/yata-local
```

### クイックスタート

```typescript
import { YataLocal } from '@nahisaho/yata-local';

// デフォルト設定で初期化
const yata = new YataLocal('./knowledge.db');
await yata.initialize();

// トリプルを追加
await yata.addTriple({
  subject: 'Person:john',
  predicate: 'hasParent',
  object: 'Person:mary'
});

// トリプルをクエリ
const results = await yata.query({
  subject: 'Person:john',
  predicate: 'hasParent'
});

// 全文検索
const searchResults = await yata.search('john parent');

// グラフ探索（BFS）
const ancestors = await yata.traverse('Person:john', 'hasParent', {
  direction: 'outgoing',
  maxDepth: 5,
  algorithm: 'bfs'
});

// クリーンアップ
await yata.close();
```

### 推論エンジン

YATA Localは4つのOWL-lite推論ルールをサポートします：

| ルール | 説明 | 例 |
|--------|------|-----|
| **推移性** | A→BかつB→CならA→C | hasAncestorは推移的 |
| **対称性** | A→BならB→A | friendOfは対称的 |
| **逆関係** | A→B（P経由）ならB→A（P⁻¹経由） | hasChild ↔ hasParent |
| **ドメイン/レンジ** | 述語から型を推論 | hasAgeはPersonを示唆 |

```typescript
// 推論を実行
const inferred = await yata.infer();
console.log(`${inferred.length}個の新しいトリプルを推論`);
```

### 制約

```typescript
// 制約を定義
await yata.addConstraint({
  type: 'cardinality',
  predicate: 'hasSpouse',
  max: 1
});

// 検証
const violations = await yata.validate();
if (violations.length > 0) {
  console.error('制約違反:', violations);
}
```

### 設定オプション

```typescript
const yata = new YataLocal('./knowledge.db', {
  // WALモードで並行性向上（デフォルト: true）
  walMode: true,
  
  // FTS5検索を有効化（デフォルト: true）
  enableSearch: true,
  
  // 書き込み時に自動推論（デフォルト: false）
  autoInfer: false,
  
  // ジャーナルモード（デフォルト: 'wal'）
  journalMode: 'wal'
});
```

---

## YATA Global

*(v1.6.3 新規)*

YATA Globalは、チームコラボレーション向けの分散型知識グラフプラットフォームです。共有知識グラフへのREST APIアクセスと、オフラインサポート・インテリジェントな同期機能を提供します。

### 機能

| 機能 | 説明 |
|------|------|
| **REST API** | HTTP経由の完全なCRUD操作 |
| **オフラインキャッシュ** | SQLiteベースのローカルキャッシュ |
| **同期エンジン** | Push/Pullと競合解決 |
| **競合解決** | Last-write-winsまたはカスタム戦略 |
| **認証** | APIキーベースの認証 |
| **バッチ操作** | 一括トリプル操作 |

### インストール

```bash
npm install @nahisaho/yata-global
```

### クイックスタート

```typescript
import { YataGlobal } from '@nahisaho/yata-global';

// クライアントを初期化
const yata = new YataGlobal({
  endpoint: 'https://yata.example.com/api',
  apiKey: 'your-api-key',
  graphId: 'project-knowledge'
});

await yata.initialize();

// トリプルを追加（バッチ）
await yata.addTriples([
  { subject: 'Task:001', predicate: 'assignedTo', object: 'User:alice' },
  { subject: 'Task:001', predicate: 'status', object: 'in-progress' }
]);

// フィルタ付きクエリ
const tasks = await yata.query({
  predicate: 'assignedTo',
  object: 'User:alice'
});

// クリーンアップ
await yata.close();
```

### オフラインサポート

YATA Globalは自動同期によるオフラインファースト操作をサポートします：

```typescript
const yata = new YataGlobal({
  endpoint: 'https://yata.example.com/api',
  apiKey: 'your-api-key',
  graphId: 'project-knowledge',
  
  // オフライン設定
  offlineMode: true,
  cachePath: './yata-cache.db',
  syncInterval: 60000  // 60秒ごとに自動同期
});

// オフラインでも動作 - ローカルにキャッシュ
await yata.addTriple({
  subject: 'Note:001',
  predicate: 'content',
  object: '重要な会議メモ'
});

// オンライン時に手動同期
await yata.sync();
```

### 競合解決

```typescript
const yata = new YataGlobal({
  // ... その他のオプション
  
  conflictStrategy: 'last-write-wins',  // デフォルト
  // または: 'server-wins', 'client-wins', 'manual'
  
  onConflict: async (local, remote) => {
    // カスタム解決ロジック
    console.log('競合を検出:', local, remote);
    return remote;  // リモート版を優先
  }
});
```

### 同期ステータス

```typescript
// 同期ステータスを確認
const status = await yata.getSyncStatus();
console.log(`保留中の変更: ${status.pendingPush}`);
console.log(`最終同期: ${status.lastSyncAt}`);

// 完全同期を強制
await yata.sync({ force: true });
```

### YATA Local vs YATA Global の選択

| ユースケース | 推奨 |
|-------------|------|
| 個人用ナレッジベース | YATA Local |
| シングルユーザーアプリ | YATA Local |
| プライバシー重視のデータ | YATA Local |
| チームコラボレーション | YATA Global |
| クロスデバイスアクセス | YATA Global |
| 共有プロジェクト知識 | YATA Global |
| 同期付きオフラインファースト | YATA Global |

---

## KGPR - Knowledge Graph Pull Request

*(v1.6.4)*

KGPR（Knowledge Graph Pull Request）は、GitHub PRと同様のワークフローで、YATA LocalからYATA Globalへ安全に知識グラフを共有する機能です。

### ワークフロー

```
┌─────────────┐     ┌──────────────┐     ┌───────────────┐
│ YATA Local  │ ──► │ KGPR (Draft) │ ──► │ YATA Global   │
│ (ローカルKG) │     │ (差分抽出)    │     │ (レビュー・マージ) │
└─────────────┘     └──────────────┘     └───────────────┘

ステータス遷移:
draft → open → reviewing → approved/changes_requested → merged/closed
```

### プライバシーレベル

| レベル | フィルタ対象 |
|-------|------------|
| `strict` | ファイルパス、URL、認証情報、全メタデータ |
| `moderate` | ファイルパス、URL、認証情報 |
| `none` | フィルタなし |

### CLIコマンド

```bash
# KGPRを作成
musubix kgpr create -t "認証パターンの追加"

# 作成前に差分をプレビュー
musubix kgpr diff --namespace myproject --privacy moderate

# KGPR一覧を表示
musubix kgpr list

# KGPRをレビューに送信
musubix kgpr submit <id>

# KGPR詳細を表示
musubix kgpr show <id>

# マージせずにクローズ
musubix kgpr close <id>
```

### MCPツール

| ツール | 説明 |
|-------|------|
| `kgpr_create` | ローカル知識グラフからKGPRを作成 |
| `kgpr_diff` | KGPR作成前に差分をプレビュー |
| `kgpr_list` | 全KGPRを一覧表示 |
| `kgpr_submit` | KGPRをレビューに送信 |
| `kgpr_review` | KGPRをレビュー（approve/changes_requested/commented） |

### 使用例

```bash
# 1. 共有内容をプレビュー
musubix kgpr diff --privacy strict

# 2. 説明付きでKGPRを作成
musubix kgpr create -t "Reactパターンの共有" -d "project-xから学習したパターン"

# 3. KGPRを確認
musubix kgpr show KGPR-001

# 4. レビューに送信
musubix kgpr submit KGPR-001
```

---

## YATA プラットフォーム拡張

*(v1.7.0)*

バージョン1.7.0では、YATAプラットフォームに5つの主要機能が追加されました。

### Phase 1: インデックス最適化

YATA Localのクエリパフォーマンスを複合インデックスで最適化。

```typescript
import { IndexOptimizer } from '@nahisaho/yata-local';

const optimizer = new IndexOptimizer(database);

// クエリパターンを分析して最適なインデックスを作成
const analysis = await optimizer.analyzeQueryPatterns();
const created = await optimizer.createOptimalIndexes();

// インデックスの健全性をチェック
const health = await optimizer.checkIndexHealth();
```

**主な機能:**
- 一般的なクエリパターン用の複合インデックス作成
- 断片化検出によるインデックス健全性監視
- 自動最適化推奨

### Phase 2: 拡張エクスポートパイプライン

増分エクスポートと複数フォーマット対応の強力なエクスポート機能。

```typescript
import { ExportPipeline } from '@nahisaho/yata-local';

const pipeline = new ExportPipeline(database);

// フルエクスポート
const fullData = await pipeline.exportFull({ namespace: 'myproject' });

// 増分エクスポート（前回エクスポート以降の変更）
const changes = await pipeline.exportIncremental({
  since: lastExportTimestamp,
  format: 'json'
});

// 変換付きエクスポート
const transformed = await pipeline.exportWithTransform({
  format: 'rdf',
  includeMetadata: true
});
```

**対応フォーマット:**
- JSON（デフォルト）
- RDF/Turtle
- N-Triples
- カスタムトランスフォーマー

### Phase 3: Global同期統合

YATA LocalとYATA Global間のシームレスな同期。

```typescript
import { GlobalSyncClient, SyncEngine } from '@nahisaho/yata-global';

const client = new GlobalSyncClient({
  endpoint: 'https://yata-global.example.com',
  offlineMode: true
});

// 同期を初期化
await client.initialize();

// ローカル変更をプッシュ
const syncResult = await client.sync({
  namespace: 'myproject',
  direction: 'push'
});

// グローバルから更新をプル
await client.sync({
  namespace: 'shared-patterns',
  direction: 'pull'
});
```

**機能:**
- オフラインファーストと自動同期
- 競合解決戦略
- 選択的な名前空間同期
- フレームワークパターンリポジトリ

### Phase 4: コードジェネレーター強化

設計ドキュメントからの高度なコード生成。

```typescript
import { CodeGenerator } from '@nahisaho/yata-local';

const generator = new CodeGenerator({
  language: 'typescript',
  outputDir: './src/generated'
});

// C4設計から生成
const result = await generator.generateFromC4(designDocument);

// カスタムテンプレートで生成
await generator.generate({
  template: 'repository-pattern',
  context: { entityName: 'User' }
});
```

**対応パターン:**
- Repositoryパターン
- Serviceレイヤー
- Factoryパターン
- ドメインイベント
- Value Objects

### Phase 5: YATA UI（Web可視化）

知識グラフのWebベース可視化・管理インターフェース。

```typescript
import { YataUIServer, createYataUIServer } from '@nahisaho/yata-ui';

// サーバーを作成して起動
const server = createYataUIServer({
  port: 3000,
  enableRealtime: true
});

// データプロバイダーを設定
server.setDataProvider(async () => ({
  nodes: await getEntities(),
  edges: await getRelationships()
}));

await server.start();
console.log(`UI: ${server.getUrl()}`);
```

**UI機能:**
- インタラクティブなグラフ可視化
- WebSocketによるリアルタイム更新
- 名前空間フィルタリング
- エンティティ/リレーションシップ編集
- エクスポート/インポート機能

### v1.7.0 パッケージ概要

| パッケージ | 説明 |
|-----------|------|
| `@nahisaho/yata-local` | IndexOptimizer, ExportPipeline, CodeGenerator |
| `@nahisaho/yata-global` | GlobalSyncClient, SyncEngine, CacheManager |
| `@nahisaho/yata-ui` | YataUIServer, グラフ可視化 |

---

## 形式検証

*(v1.7.5)*

`@nahisaho/musubix-formal-verify` パッケージは、Z3 SMTソルバーを使用した形式検証機能を提供します。

### インストール

```bash
npm install @nahisaho/musubix-formal-verify
# オプション: WebAssemblyサポート用にz3-solverをインストール
npm install z3-solver
```

### Z3 SMTソルバー統合

```typescript
import { Z3Adapter, PreconditionVerifier, PostconditionVerifier } from '@nahisaho/musubix-formal-verify';

// Z3アダプター作成（バックエンド自動選択）
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

console.log(result.status); // 'valid' | 'invalid' | 'unknown' | 'error'
```

### Hoareトリプル検証

```typescript
// {P} C {Q} の検証
const postVerifier = new PostconditionVerifier(z3);
const hoareResult = await postVerifier.verify({
  precondition: { expression: 'balance >= amount', format: 'javascript' },
  postcondition: { expression: 'balance_new == balance - amount', format: 'javascript' },
  preVariables: [{ name: 'balance', type: 'Int' }, { name: 'amount', type: 'Int' }],
  postVariables: [{ name: 'balance_new', type: 'Int' }],
  transition: 'balance_new == balance - amount',
});
```

### EARS→SMT変換

```typescript
import { EarsToSmtConverter } from '@nahisaho/musubix-formal-verify';

const converter = new EarsToSmtConverter();

// EARS要件をSMT-LIB2に変換
const results = converter.convertMultiple([
  'THE system SHALL validate inputs',           // ubiquitous
  'WHEN error, THE system SHALL notify user',   // event-driven
  'WHILE busy, THE system SHALL queue requests', // state-driven
  'THE system SHALL NOT expose secrets',        // unwanted
  'IF admin, THEN THE system SHALL allow edit', // optional
]);

results.forEach(r => {
  console.log(`パターン: ${r.formula?.metadata.earsPattern.type}`);
  console.log(`SMT: ${r.formula?.smtLib2}`);
});
```

### トレーサビリティデータベース

```typescript
import { TraceabilityDB, ImpactAnalyzer } from '@nahisaho/musubix-formal-verify';

// SQLiteベースのトレーサビリティDB作成
const db = new TraceabilityDB('./trace.db');

// ノード追加
await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'ユーザー認証' });
await db.addNode({ id: 'DES-001', type: 'design', title: 'AuthService' });
await db.addNode({ id: 'CODE-001', type: 'code', title: 'auth.ts' });

// トレーサビリティリンク追加
await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });
await db.addLink({ source: 'CODE-001', target: 'DES-001', type: 'implements' });

// 影響分析
const analyzer = new ImpactAnalyzer(db);
const impact = await analyzer.analyze('REQ-001');
console.log(`影響ノード数: ${impact.totalImpacted}`);
```

### v1.7.5 パッケージ概要

| パッケージ | 説明 |
|-----------|------|
| `@nahisaho/musubix-formal-verify` | Z3統合、Hoare検証、EARS→SMT、トレーサビリティDB |

### サポートされる変数型

| 型 | 説明 |
|----|------|
| `Int` | 整数値 |
| `Real` | 実数 |
| `Bool` | 真偽値 |
| `String` | 文字列 |
| `Array` | 配列型 |
| `BitVec` | ビットベクトル |

---

## セキュリティ分析

*(v1.8.0)*

`@nahisaho/musubix-security` パッケージは、TypeScript/JavaScriptプロジェクト向けの包括的なセキュリティ分析機能を提供します。

### インストール

```bash
npm install @nahisaho/musubix-security
```

### 脆弱性スキャン

AST解析によりOWASP Top 10およびCWE Top 25の脆弱性を検出します：

```typescript
import { VulnerabilityScanner, createSecurityService } from '@nahisaho/musubix-security';

// 単一ファイルのスキャン
const scanner = new VulnerabilityScanner();
const vulnerabilities = scanner.scanFile('src/api.ts');

// ディレクトリのスキャン
const result = await scanner.scanDirectory('./src');
console.log(`検出された脆弱性: ${result.vulnerabilities.length}`);
console.log(`スキャンしたファイル: ${result.scannedFiles}`);
```

### 検出可能な脆弱性

| カテゴリ | CWE | 重要度 |
|---------|-----|--------|
| SQLインジェクション | CWE-89 | Critical |
| コマンドインジェクション | CWE-78 | Critical |
| XSS | CWE-79 | High |
| パストラバーサル | CWE-22 | High |
| コードインジェクション | CWE-94 | Critical |
| NoSQLインジェクション | CWE-943 | High |

### シークレット検出

ハードコードされた認証情報や機密情報を検出します：

```typescript
import { SecretDetector } from '@nahisaho/musubix-security';

const detector = new SecretDetector();
const secrets = detector.scanContent(content, 'config.ts');
const result = await detector.scan('./src');

console.log(`検出されたシークレット: ${result.summary.total}`);
```

### 検出可能なシークレットタイプ

| タイプ | パターン |
|--------|--------|
| AWS Access Key | `AKIA...` |
| AWS Secret Key | 40文字のbase64 |
| GitHub Token | `ghp_*`, `gho_*`, `ghu_*` |
| 秘密鍵 | PEM形式 |
| データベースURL | `postgres://`, `mongodb://` |
| JWTシークレット | JWT署名シークレット |
| Stripe Key | `sk_live_*`, `sk_test_*` |

### テイント解析

ユーザー入力（ソース）から危険な関数（シンク）へのデータフローを追跡します：

```typescript
import { TaintAnalyzer } from '@nahisaho/musubix-security';

const analyzer = new TaintAnalyzer();
const result = analyzer.analyze('./src');

console.log(`ソース: ${result.sources.length}`);
console.log(`シンク: ${result.sinks.length}`);
console.log(`テイントパス: ${result.paths.length}`);
```

### 依存関係監査

npm auditと統合して脆弱な依存関係を検出します：

```typescript
import { DependencyAuditor } from '@nahisaho/musubix-security';

const auditor = new DependencyAuditor();
const result = await auditor.audit('./project');

console.log(`Critical: ${result.summary.critical}`);
console.log(`High: ${result.summary.high}`);
```

### 統合セキュリティサービス

すべてのセキュリティ分析機能を統合：

```typescript
import { createSecurityService } from '@nahisaho/musubix-security';

const service = createSecurityService();

// フルセキュリティスキャン
const result = await service.scan({
  target: './src',
  vulnerabilities: true,
  taint: true,
  secrets: true,
  dependencies: true,
  generateFixes: true,
});

console.log(`総脆弱性数: ${result.summary.totalVulnerabilities}`);
console.log(`総シークレット数: ${result.summary.totalSecrets}`);
console.log(`生成された修正: ${result.summary.fixesGenerated}`);
```

### レポート生成

複数のフォーマットでレポートを生成：

```typescript
// SARIF形式（GitHub Code Scanning対応）
const sarifReport = await service.generateReport(result, 'sarif');

// Markdown形式
const mdReport = await service.generateReport(result, 'markdown');

// HTML形式
const htmlReport = await service.generateReport(result, 'html');
```

### CLIの使い方

```bash
# フルセキュリティスキャン
npx musubix-security scan ./src

# 脆弱性スキャンのみ
npx musubix-security scan ./src --vulnerabilities-only

# シークレット検出
npx musubix-security secrets ./src

# テイント解析
npx musubix-security taint ./src

# 依存関係監査
npx musubix-security audit ./project

# SARIFレポート生成
npx musubix-security scan ./src --format sarif --output report.sarif
```

### v1.8.0 パッケージ概要

| パッケージ | 説明 |
|-----------|------|
| `@nahisaho/musubix-security` | 脆弱性スキャン、シークレット検出、テイント解析、依存関係監査 |

---

## MCPサーバー連携

### MCPサーバーの起動

#### CLI から起動

```bash
# stdio モード（推奨）
musubix-mcp
npx @nahisaho/musubix-mcp-server

# SSE モード
musubix-mcp --transport sse --port 8080
```

#### プログラムから起動

```typescript
import { startServer, createMCPServer } from '@nahisaho/musubix-mcp-server';

// 簡易起動
await startServer({ transport: 'stdio' });

// カスタム設定
const server = createMCPServer({
  name: 'my-musubix-server',
  version: '1.0.0',
  transport: 'stdio'
});

await server.start();
console.log('MCPサーバーが起動しました');
```

### GitHub Copilot (VS Code) との連携

`.vscode/mcp.json`:

```json
{
  "mcpServers": {
    "musubix": {
      "command": "npx",
      "args": ["@nahisaho/musubix-mcp-server"]
    },
    "yata": {
      "command": "uv",
      "args": ["run", "yata", "serve"],
      "cwd": "/path/to/YATA"
    }
  }
}
```

### Claude Desktop との連携

設定ファイルの場所：
- **macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
- **Windows**: `%APPDATA%\Claude\claude_desktop_config.json`
- **Linux**: `~/.config/Claude/claude_desktop_config.json`

```json
{
  "mcpServers": {
    "musubix": {
      "command": "npx",
      "args": ["@nahisaho/musubix-mcp-server"]
    },
    "yata": {
      "command": "uv",
      "args": ["run", "yata", "serve"],
      "cwd": "/path/to/YATA"
    }
  }
}
```

### Cursor IDE との連携

`.cursor/mcp.json`:

```json
{
  "mcpServers": {
    "musubix": {
      "command": "npx",
      "args": ["@nahisaho/musubix-mcp-server"]
    }
  }
}
```

### ツールの呼び出し

```typescript
// MCP経由でのツール呼び出し例
const response = await client.callTool({
  tool: 'analyze_requirements',
  arguments: {
    text: 'システムは...',
    options: { validateEARS: true }
  }
});
```

---

## YATA知識グラフ

### YATAとは？

YATA（八咫）は、AIコーディング支援のための知識グラフMCPサーバーです。MUSUBIXと組み合わせることで、ニューロシンボリックAI機能を実現します。

| 機能 | 説明 |
|------|------|
| **コード解析** | Tree-sitterによる24言語対応AST解析 |
| **知識グラフ** | NetworkXによるエンティティ・関係性グラフ |
| **フレームワーク知識** | 47フレームワーク、457K+エンティティ |
| **MCP対応** | 34 Tools, 3 Prompts, 1 Resource |

### YATAサーバーの起動

```bash
# YATAディレクトリに移動
cd /path/to/YATA

# stdio モードで起動
uv run yata serve

# SSE モードで起動
uv run yata serve --transport sse --port 8080
```

### YATAクライアントの設定

```typescript
import { createYATAClient } from '@nahisaho/musubix-yata-client';

const yata = createYATAClient({
  transport: 'stdio',  // または { type: 'sse', endpoint: 'http://localhost:8080' }
});

await yata.connect();
```

### 知識のクエリ

```typescript
// 要件の検索
const requirements = await yata.query({
  type: 'requirement',
  filters: {
    priority: 'must',
    status: 'approved'
  }
});

// 関連エンティティの取得
const related = await yata.getRelated({
  entityId: 'REQ-001',
  relationTypes: ['implements', 'depends_on']
});
```

### 知識の保存

```typescript
// 新しい要件を保存
await yata.store({
  type: 'requirement',
  data: requirement,
  relations: [
    { type: 'part_of', target: 'EPIC-001' }
  ]
});

// エンティティ間のリンク
await yata.link({
  source: 'TSK-001',
  target: 'REQ-001',
  type: 'implements'
});
```

---

## ベストプラクティス

### 1. 要件定義のベストプラクティス

✅ **推奨**:
- EARS形式を使用する
- 検証可能な受け入れ基準を含める
- 1つの要件に1つの機能

❌ **避けるべき**:
- 曖昧な表現（「適切に」「迅速に」など）
- 複数の機能を1つの要件に含める
- 実装詳細を要件に含める

### 2. 設計のベストプラクティス

✅ **推奨**:
- C4の4レベルを活用
- 重要な決定はADRで記録
- 要件とのトレーサビリティを維持

❌ **避けるべき**:
- 詳細すぎる最初の設計
- 決定理由の省略
- 孤立した設計ドキュメント

### 3. タスク管理のベストプラクティス

✅ **推奨**:
- 4時間以内の粒度
- 要件への明確なリンク
- 完了条件の明記

❌ **避けるべき**:
- 大きすぎるタスク（8時間超）
- 要件リンクのないタスク
- 曖昧な完了条件

---

## トラブルシューティング

### よくある問題と解決策

#### 要件の検証エラー

```
エラー: EARS形式が検出されませんでした
```

**解決策**: 要件テキストにEARSパターンを含めてください。

```typescript
// 修正前
const text = '認証機能を実装する';

// 修正後
const text = 'ユーザーがログインしたとき、システムは認証を行わなければならない';
```

#### トレーサビリティの警告

```
警告: 要件 REQ-001 に設計参照がありません
```

**解決策**: 設計ドキュメントを作成し、リンクしてください。

```typescript
requirementsService.linkDesign('REQ-001', 'DES-001');
```

#### MCPサーバー接続エラー

```
エラー: MCPサーバーに接続できません
```

**解決策**:
1. サーバーが起動しているか確認
2. ポート番号を確認
3. ファイアウォール設定を確認

```bash
# サーバーの状態確認
ps aux | grep musubix
```

#### YATA接続エラー

```
エラー: YATAエンドポイントに接続できません
```

**解決策**:
1. エンドポイントURLを確認
2. APIキーを確認
3. ネットワーク設定を確認

```typescript
const client = createYATAClient({
  endpoint: 'http://localhost:8000',  // 正しいURL
  apiKey: process.env.YATA_API_KEY    // 環境変数を確認
});
```

---

## 次のステップ

- 📚 [APIリファレンス](./API-REFERENCE.md)を参照
- 💡 [サンプルプロジェクト](./examples/)を確認
- 🤝 [コントリビューションガイド](./CONTRIBUTING.md)を読む

---

## 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [INSTALL-GUIDE.ja.md](INSTALL-GUIDE.ja.md) | 詳細インストールガイド |
| [API-REFERENCE.md](API-REFERENCE.md) | APIリファレンス |
| [evolution-from-musubi-to-musubix.md](evolution-from-musubi-to-musubix.md) | MUSUBIからの進化 |

---

**バージョン**: 1.8.0  
**最終更新**: 2026-01-06  
**MUSUBIX Project**
