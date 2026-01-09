# MUSUBIX CodeGraph v2.3.4 設計書

> **Document ID**: DES-CG-v234  
> **Date**: 2026-01-10  
> **Status**: Draft  
> **Author**: AI Agent (GitHub Copilot)

---

## 1. 概要

本設計書は、v2.3.3 で発見された以下の問題を修正する v2.3.4 の設計を定義する。

| 要件ID | 問題 | 設計ID |
|--------|------|--------|
| REQ-CG-v234-001 | PR preview に GitHub 認証が必要 | DES-CG-v234-001 |
| REQ-CG-v234-002 | CLI に index/query/stats コマンドがない | DES-CG-v234-002 |
| REQ-CG-v234-003 | PRCreator の初期化が分離されていない | DES-CG-v234-003 |
| REQ-CG-v234-004 | エラーメッセージが不親切 | DES-CG-v234-004 |

---

## 2. C4 Context Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           External Actors                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ┌─────────┐        ┌─────────────┐        ┌──────────────────┐        │
│   │  User   │        │   GitHub    │        │  File System     │        │
│   │ (CLI)   │        │    API      │        │  (Repository)    │        │
│   └────┬────┘        └──────┬──────┘        └────────┬─────────┘        │
│        │                    │                        │                   │
│        │                    │ (Optional)             │                   │
│        ▼                    ▼                        ▼                   │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                     MUSUBIX CodeGraph v2.3.4                     │   │
│   │  ┌───────────┐  ┌───────────────┐  ┌───────────────────────┐   │   │
│   │  │  CLI      │  │  PRCreator    │  │  CodeGraph Core       │   │   │
│   │  │ (cg)      │  │  (Offline/    │  │  (Index, Query,       │   │   │
│   │  │           │  │   Online)     │  │   Stats)              │   │   │
│   │  └───────────┘  └───────────────┘  └───────────────────────┘   │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 3. C4 Container Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          MUSUBIX CodeGraph v2.3.4                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                            CLI Layer                                   │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐     │   │
│  │  │ cg pr      │  │ cg index   │  │ cg query   │  │ cg stats   │     │   │
│  │  │ (既存)     │  │ (v2.3.4)   │  │ (v2.3.4)   │  │ (v2.3.4)   │     │   │
│  │  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘     │   │
│  └────────┼───────────────┼───────────────┼───────────────┼─────────────┘   │
│           │               │               │               │                  │
│           ▼               ▼               ▼               ▼                  │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                         Core Layer                                     │   │
│  │  ┌──────────────────────────────────────────────────────────────┐    │   │
│  │  │                       PRCreator (Refactored)                   │    │   │
│  │  │  ┌─────────────────┐  ┌────────────────────┐                  │    │   │
│  │  │  │ initializeOffline│  │ initialize()       │                  │    │   │
│  │  │  │ () [v2.3.4]     │  │ (Full Auth)        │                  │    │   │
│  │  │  │ - No GitHub Auth │  │ - GitHub Auth      │                  │    │   │
│  │  │  │ - Local Preview  │  │ - Push/PR Create   │                  │    │   │
│  │  │  └─────────────────┘  └────────────────────┘                  │    │   │
│  │  └──────────────────────────────────────────────────────────────┘    │   │
│  │                                                                       │   │
│  │  ┌──────────────────────────────────────────────────────────────┐    │   │
│  │  │                       CodeGraph (既存)                         │    │   │
│  │  │  ┌────────────┐  ┌────────────┐  ┌────────────┐               │    │   │
│  │  │  │ index()    │  │ query()    │  │ getStats() │               │    │   │
│  │  │  └────────────┘  └────────────┘  └────────────┘               │    │   │
│  │  └──────────────────────────────────────────────────────────────┘    │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 4. DES-CG-v234-001: Offline Preview 設計

### 4.1 目的

GitHub 認証なしで PR プレビューを生成可能にする。

### 4.2 インターフェース設計

```typescript
// packages/codegraph/src/pr/pr-creator.ts

export class PRCreator extends EventEmitter {
  // 既存
  async initialize(): Promise<{ success: boolean; error?: string }>;
  
  // v2.3.4 NEW: オフライン初期化
  async initializeOffline(): Promise<{ success: boolean; error?: string }>;
  
  // v2.3.4 NEW: オフライン対応プレビュー
  async preview(suggestion: RefactoringSuggestion): Promise<PRPreview>;
  
  // 既存（GitHub 認証必須）
  async create(options: PRCreateOptions): Promise<PRCreateResult>;
}

// v2.3.4 NEW: PRPreview 型拡張
export interface PRPreview {
  branchName: string;
  commitMessage: string;
  title: string;
  body: string;
  diffs: FileDiff[];
  filesChanged: string[];
  linesAdded: number;
  linesDeleted: number;
}
```

### 4.3 シーケンス図

```
User              CLI              PRCreator          TemplateGenerator
  │                │                   │                     │
  │  cg pr preview │                   │                     │
  │  --offline     │                   │                     │
  │───────────────>│                   │                     │
  │                │ initializeOffline │                     │
  │                │──────────────────>│                     │
  │                │    ✓ (no auth)    │                     │
  │                │<──────────────────│                     │
  │                │                   │                     │
  │                │ preview(suggestion)                     │
  │                │──────────────────>│                     │
  │                │                   │  generate()         │
  │                │                   │────────────────────>│
  │                │                   │    PRPreview        │
  │                │                   │<────────────────────│
  │                │   PRPreview       │                     │
  │                │<──────────────────│                     │
  │  Display       │                   │                     │
  │<───────────────│                   │                     │
```

### 4.4 設計決定

| 決定 | 理由 |
|------|------|
| `initializeOffline()` を追加 | 既存の `initialize()` との後方互換性維持 |
| `preview()` メソッドを追加 | GitHub 認証なしでプレビュー生成可能に |
| `--offline` フラグを追加 | CLI から明示的にオフラインモード指定 |

---

## 5. DES-CG-v234-002: CLI 拡張設計

### 5.1 目的

`cg index`, `cg query`, `cg stats` コマンドを追加し、ドキュメントと実装を一致させる。

### 5.2 コマンド設計

```bash
# cg index - コードベースのインデックス化
cg index <path>
  -d, --depth <n>      # 最大深度（デフォルト: 3）
  --json               # JSON出力
  --languages <langs>  # 対象言語（カンマ区切り）

# cg query - エンティティ検索
cg query <query>
  --type <type>        # entity type (function, class, method, etc.)
  --limit <n>          # 結果数制限（デフォルト: 10）
  --json               # JSON出力

# cg stats - 統計情報
cg stats
  --json               # JSON出力
```

### 5.3 CLI 構造

```typescript
// packages/codegraph/src/cli.ts

program
  .name('cg')
  .description('MUSUBIX CodeGraph - Code Graph Analysis CLI')
  .version(packageJson.version);

// v2.3.4 NEW: Index command
program
  .command('index <path>')
  .description('Index a codebase')
  .option('-d, --depth <n>', 'Max depth', '3')
  .option('--json', 'Output as JSON')
  .option('--languages <langs>', 'Target languages (comma-separated)')
  .action(indexAction);

// v2.3.4 NEW: Query command
program
  .command('query <query>')
  .description('Query entities in the graph')
  .option('--type <type>', 'Entity type filter')
  .option('--limit <n>', 'Result limit', '10')
  .option('--json', 'Output as JSON')
  .action(queryAction);

// v2.3.4 NEW: Stats command
program
  .command('stats')
  .description('Show graph statistics')
  .option('--json', 'Output as JSON')
  .action(statsAction);

// 既存: PR commands
const prCommand = program.command('pr').description('PR operations');
```

### 5.4 依存関係

```
cli.ts
  ├── index command → CodeGraph.index()
  ├── query command → CodeGraph.query() / GraphEngine.findEntities()
  ├── stats command → CodeGraph.getStats() / GraphEngine.getStats()
  └── pr command    → PRCreator (既存)
```

---

## 6. DES-CG-v234-003: PRCreator 初期化分離

### 6.1 目的

認証が必要な操作と不要な操作を分離し、ユースケースに応じた初期化を可能にする。

### 6.2 状態遷移図

```
          ┌────────────────┐
          │  Uninitialized │
          └───────┬────────┘
                  │
        ┌─────────┴─────────┐
        │                   │
        ▼                   ▼
┌───────────────┐   ┌───────────────┐
│OfflineReady   │   │ FullyReady    │
│               │   │               │
│ - preview()   │   │ - preview()   │
│ - dryRun()    │   │ - dryRun()    │
│               │   │ - create()    │
│ ✗ create()    │   │ - push()      │
└───────────────┘   └───────────────┘
        │                   │
        │  initialize()     │
        └──────────────────>│
```

### 6.3 内部状態管理

```typescript
export class PRCreator extends EventEmitter {
  private state: 'uninitialized' | 'offline' | 'full' = 'uninitialized';
  
  async initializeOffline(): Promise<InitResult> {
    // Git operations setup (local only)
    // Template generator setup
    this.state = 'offline';
  }
  
  async initialize(): Promise<InitResult> {
    if (this.state === 'uninitialized') {
      await this.initializeOffline();
    }
    // GitHub authentication
    this.state = 'full';
  }
  
  async preview(suggestion: RefactoringSuggestion): Promise<PRPreview> {
    this.ensureState('offline', 'full');
    // ...
  }
  
  async create(options: PRCreateOptions): Promise<PRCreateResult> {
    this.ensureState('full');
    // ...
  }
  
  private ensureState(...allowed: State[]): void {
    if (!allowed.includes(this.state)) {
      throw new PRCreatorError(
        `Operation requires ${allowed.join(' or ')} state, but current state is ${this.state}. ` +
        `Call ${this.state === 'uninitialized' ? 'initializeOffline() or initialize()' : 'initialize()'} first.`
      );
    }
  }
}
```

---

## 7. DES-CG-v234-004: エラーメッセージ改善

### 7.1 目的

エラーメッセージに次のアクションを提示し、ユーザーが解決方法を理解できるようにする。

### 7.2 エラーメッセージ設計

| シナリオ | 現在のメッセージ | v2.3.4 改善版 |
|----------|-----------------|---------------|
| 未初期化で preview | `Not initialized` | `PRCreator is not initialized. Call initializeOffline() for preview or initialize() for full functionality.` |
| 認証失敗 | `GitHub authentication failed` | `GitHub authentication failed. Run 'gh auth login' or set GITHUB_TOKEN environment variable. For preview-only, use initializeOffline() instead.` |
| offline で create | N/A | `Cannot create PR in offline mode. Call initialize() to authenticate with GitHub.` |

### 7.3 エラークラス設計

```typescript
// packages/codegraph/src/pr/errors.ts (v2.3.4 NEW)

export class PRCreatorError extends Error {
  constructor(
    message: string,
    public readonly code: PRErrorCode,
    public readonly suggestion?: string
  ) {
    super(message);
    this.name = 'PRCreatorError';
  }
}

export type PRErrorCode =
  | 'NOT_INITIALIZED'
  | 'OFFLINE_MODE'
  | 'AUTH_FAILED'
  | 'REPO_NOT_FOUND'
  | 'REMOTE_PARSE_FAILED'
  | 'APPLY_FAILED';

export const PRErrorMessages: Record<PRErrorCode, { message: string; suggestion: string }> = {
  NOT_INITIALIZED: {
    message: 'PRCreator is not initialized',
    suggestion: 'Call initializeOffline() for preview or initialize() for full functionality'
  },
  OFFLINE_MODE: {
    message: 'Cannot perform this operation in offline mode',
    suggestion: 'Call initialize() to authenticate with GitHub'
  },
  AUTH_FAILED: {
    message: 'GitHub authentication failed',
    suggestion: "Run 'gh auth login' or set GITHUB_TOKEN environment variable"
  },
  // ...
};
```

---

## 8. ファイル変更一覧

| ファイル | 変更種別 | 説明 |
|----------|----------|------|
| `packages/codegraph/src/cli.ts` | 修正 | index, query, stats コマンド追加 |
| `packages/codegraph/src/pr/pr-creator.ts` | 修正 | initializeOffline(), preview() 追加 |
| `packages/codegraph/src/pr/errors.ts` | 新規 | エラークラス定義 |
| `packages/codegraph/src/pr/types.ts` | 修正 | PRPreview 型拡張 |
| `packages/codegraph/src/pr/index.ts` | 修正 | エクスポート追加 |
| `packages/codegraph/package.json` | 修正 | version 2.3.4 |

---

## 9. テスト計画

| テストID | 対象 | 説明 |
|----------|------|------|
| TEST-v234-001 | initializeOffline | オフライン初期化が成功する |
| TEST-v234-002 | preview (offline) | オフラインモードでプレビュー生成 |
| TEST-v234-003 | create (offline → error) | オフラインモードで create はエラー |
| TEST-v234-004 | cg index | CLI からインデックス作成 |
| TEST-v234-005 | cg query | CLI からエンティティ検索 |
| TEST-v234-006 | cg stats | CLI から統計取得 |
| TEST-v234-007 | error messages | エラーメッセージに suggestion 含む |

---

## 10. トレーサビリティマトリクス

| 要件ID | 設計ID | テストID |
|--------|--------|----------|
| REQ-CG-v234-001 | DES-CG-v234-001 | TEST-v234-001, TEST-v234-002 |
| REQ-CG-v234-002 | DES-CG-v234-002 | TEST-v234-004, TEST-v234-005, TEST-v234-006 |
| REQ-CG-v234-003 | DES-CG-v234-003 | TEST-v234-001, TEST-v234-003 |
| REQ-CG-v234-004 | DES-CG-v234-004 | TEST-v234-007 |

---

## 11. 憲法条項準拠チェック

| 条項 | 内容 | 準拠状況 |
|------|------|----------|
| Article II | CLI Interface 必須 | ✅ cg index/query/stats 追加 |
| Article III | Test-First | ✅ テスト計画策定済み |
| Article V | Traceability | ✅ REQ→DES→TEST マトリクス |
| Article VII | Design Patterns | ✅ State パターン適用 |
| Article IX | Quality Gates | ✅ 設計レビュー実施 |

---

**Document Version**: 1.0  
**Last Updated**: 2026-01-10
