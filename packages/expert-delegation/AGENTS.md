# MUSUBIX Expert Delegation System

> **AI Coding Agent向け**: このファイルはAIエージェント（GitHub Copilot、Claude等）がExpert Delegation Systemを理解するためのガイドです。

## 🎯 パッケージ概要

**@nahisaho/musubix-expert-delegation**は、VS Code Language Model APIを活用したAIエキスパート委任システムです。

| 項目 | 詳細 |
|------|------|
| **バージョン** | 3.2.0 |
| **パッケージ名** | `@nahisaho/musubix-expert-delegation` |
| **ビルドシステム** | TypeScript + ESM |
| **テストフレームワーク** | Vitest |
| **VS Code API** | vscode.lm (Language Model API) |

---

## 📦 アーキテクチャ

### ディレクトリ構成

```
packages/expert-delegation/
├── src/
│   ├── types/           # 型定義
│   │   ├── index.ts     # Core型定義
│   │   └── errors.ts    # エラー型・DelegationError
│   ├── providers/       # LLMプロバイダー
│   │   ├── vscode-lm-provider.ts    # VS Code LM API
│   │   ├── model-selector.ts        # モデル選択
│   │   └── usage-statistics.ts      # 使用統計
│   ├── experts/         # 7エキスパート定義
│   │   ├── expert-manager.ts        # 管理
│   │   ├── architect.ts
│   │   ├── security-analyst.ts
│   │   ├── code-reviewer.ts
│   │   ├── plan-reviewer.ts
│   │   ├── ears-analyst.ts          # MUSUBIX独自
│   │   ├── formal-verifier.ts       # MUSUBIX独自
│   │   └── ontology-reasoner.ts     # MUSUBIX独自
│   ├── triggers/        # トリガー検出
│   │   ├── trigger-patterns.ts      # パターン定義
│   │   ├── semantic-router.ts       # 意図解析
│   │   └── proactive-delegation.ts  # 先行検出
│   ├── delegation/      # 委任ロジック
│   │   ├── delegation-engine.ts     # メインエンジン
│   │   ├── prompt-builder.ts        # プロンプト構築
│   │   ├── advisory-mode.ts         # アドバイスモード
│   │   ├── implementation-mode.ts   # 実装モード
│   │   └── retry-handler.ts         # リトライ・エスカレーション
│   ├── mcp/             # MCPツール
│   │   ├── schemas.ts               # スキーマ定義
│   │   └── handlers.ts              # ハンドラ
│   ├── test/            # テストユーティリティ
│   └── index.ts         # パッケージエントリ
└── test/                # テストファイル
```

---

## 🔑 主要コンポーネント

### 1. エキスパートタイプ（7種）

| タイプ | 説明 | 特徴 |
|--------|------|------|
| `architect` | アーキテクチャ設計 | C4モデル、設計パターン |
| `security-analyst` | セキュリティ分析 | 脆弱性、脅威モデリング |
| `code-reviewer` | コードレビュー | 品質、ベストプラクティス |
| `plan-reviewer` | 計画レビュー | 10憲法条項準拠 |
| `ears-analyst` | EARS分析 | **MUSUBIX独自** - 要件形式化 |
| `formal-verifier` | 形式検証 | **MUSUBIX独自** - Z3/Lean統合 |
| `ontology-reasoner` | オントロジー推論 | **MUSUBIX独自** - 知識グラフ |

### 2. 実行モード

| モード | 説明 | 出力 |
|--------|------|------|
| `advisory` | 分析・アドバイス | テキスト形式のレビュー |
| `implementation` | コード生成 | 実行可能なコード |

### 3. MCPツール（11ツール）

| ツール | 説明 |
|--------|------|
| `expert_delegate` | 汎用委任（自動エキスパート選択） |
| `expert_architect` | アーキテクチャ設計委任 |
| `expert_security` | セキュリティ分析委任 |
| `expert_review` | コードレビュー委任 |
| `expert_plan` | 計画レビュー委任 |
| `expert_ears` | EARS形式変換委任 |
| `expert_formal` | 形式検証委任 |
| `expert_ontology` | オントロジー推論委任 |
| `trigger_detect` | トリガーパターン検出 |
| `delegation_retry` | リトライ実行 |
| `provider_select` | モデル選択 |

---

## 💻 使用方法

### 基本的な委任

```typescript
import {
  DelegationEngine,
  createVSCodeLMProvider,
  ExpertManager,
} from '@nahisaho/musubix-expert-delegation';

// プロバイダー作成
const provider = createVSCodeLMProvider();

// エンジン作成
const engine = new DelegationEngine(provider);

// 簡易委任
const result = await engine.delegateSimple(
  'このアーキテクチャを評価してください',
  { mode: 'advisory' }
);

// 明示的なエキスパート指定
const result2 = await engine.delegateSimple(
  'セキュリティリスクを分析してください',
  { expertType: 'security-analyst', mode: 'advisory' }
);
```

### MCPツール経由

```typescript
import { MCPHandlers } from '@nahisaho/musubix-expert-delegation';

const handlers = new MCPHandlers(provider);

// expert_delegate
const result = await handlers.handleExpertDelegate({
  message: 'アーキテクチャを設計してください',
  mode: 'implementation',
});

// expert_security
const secResult = await handlers.handleExpertSecurity({
  code: 'const password = "secret123";',
  analysisType: 'vulnerability',
});
```

---

## 🧪 テスト

```bash
# テスト実行
npm test

# カバレッジ付き
npm run test:coverage
```

### モック

VS Code APIはモックで置換されます：

```typescript
// test/__mocks__/vscode.ts
export const lm = {
  selectChatModels: vi.fn().mockResolvedValue([...]),
};
```

---

## ⚙️ 設定

### DelegationEngineConfig

```typescript
interface DelegationEngineConfig {
  retry?: {
    maxRetries?: number;           // デフォルト: 3
    initialDelayMs?: number;       // デフォルト: 1000
    backoffMultiplier?: number;    // デフォルト: 2
  };
  escalation?: {
    escalationThreshold?: number;  // デフォルト: 3
    escalationMap?: Record<ExpertType, ExpertType | null>;
  };
  defaultMode?: ExecutionMode;     // デフォルト: 'advisory'
  enableConstitutionCheck?: boolean; // デフォルト: true
  enforceTraceability?: boolean;   // デフォルト: true
}
```

---

## 🔗 トレーサビリティ

| 要件ID | 設計ID | 実装ファイル |
|--------|--------|-------------|
| REQ-EXP-001 | DES-EXP-001 | `experts/*.ts` |
| REQ-PRV-001 | DES-PRV-001 | `providers/vscode-lm-provider.ts` |
| REQ-TRG-001 | DES-TRG-001 | `triggers/*.ts` |
| REQ-DEL-001 | DES-DEL-001 | `delegation/*.ts` |
| REQ-INT-001 | DES-MCP-001 | `mcp/*.ts` |

---

## 🛡️ 10憲法条項の強制

Plan Reviewerエキスパートが自動的にチェック：

- **Article X**: 実装前提条件（要件・設計なしの実装禁止）
- **Article IV**: EARS形式（要件はEARS形式で記述）
- **Article V**: トレーサビリティ（REQ→DES→TSK→コード追跡）

```typescript
// 憲法チェックが有効な場合（デフォルト）
const engine = new DelegationEngine(provider, undefined, {
  enableConstitutionCheck: true,
});

// 実装モードで要件・設計なしの場合、エラーを返す
const result = await engine.delegateSimple(
  '新機能を実装して',
  { mode: 'implementation' }
);
// result.success === false
// result.content includes "Article X violation"
```

---

## 📚 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [REQ-MUSUBIX-v3.2.0.md](../../storage/specs/REQ-MUSUBIX-v3.2.0.md) | 要件定義書 |
| [DES-MUSUBIX-v3.2.0.md](../../storage/design/DES-MUSUBIX-v3.2.0.md) | 設計書 |
| [TSK-MUSUBIX-v3.2.0.md](../../storage/tasks/TSK-MUSUBIX-v3.2.0.md) | タスク分解書 |

---

**Version**: 3.2.0  
**Last Updated**: 2026-01-13
