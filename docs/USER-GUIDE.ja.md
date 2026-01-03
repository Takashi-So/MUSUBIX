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
12. [MCPサーバー連携](#mcpサーバー連携)
13. [YATA知識グラフ](#yata知識グラフ)
14. [ベストプラクティス](#ベストプラクティス)
15. [トラブルシューティング](#トラブルシューティング)

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

# 学習データをエクスポート
musubix learn export --output learning-data.json

# 学習データをインポート
musubix learn import learning-data.json
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

**バージョン**: 1.0.12  
**最終更新**: 2026-01-03  
**MUSUBIX Project**
