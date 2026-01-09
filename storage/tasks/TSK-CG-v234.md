# MUSUBIX CodeGraph v2.3.4 タスク分解書

> **Document ID**: TSK-CG-v234  
> **Date**: 2026-01-10  
> **Status**: Draft  
> **Traced From**: DES-CG-v234

---

## タスク一覧

| タスクID | 設計ID | 内容 | 優先度 | 工数 |
|----------|--------|------|--------|------|
| TSK-v234-001 | DES-CG-v234-004 | エラークラス定義 | P0 | 0.5h |
| TSK-v234-002 | DES-CG-v234-003 | PRCreator 状態管理リファクタ | P0 | 1h |
| TSK-v234-003 | DES-CG-v234-001 | initializeOffline() 実装 | P0 | 1h |
| TSK-v234-004 | DES-CG-v234-001 | preview() メソッド実装 | P0 | 1h |
| TSK-v234-005 | DES-CG-v234-002 | CLI index コマンド追加 | P1 | 0.5h |
| TSK-v234-006 | DES-CG-v234-002 | CLI query コマンド追加 | P1 | 0.5h |
| TSK-v234-007 | DES-CG-v234-002 | CLI stats コマンド追加 | P1 | 0.5h |
| TSK-v234-008 | - | エクスポート・バージョン更新 | P0 | 0.5h |
| TSK-v234-009 | - | テスト作成・実行 | P0 | 1h |

**合計工数**: 約6.5時間

---

## TSK-v234-001: エラークラス定義

### 概要
PRCreator 専用のエラークラスとエラーコード定義を作成

### 対象ファイル
- `packages/codegraph/src/pr/errors.ts` (新規)

### 実装内容

```typescript
// packages/codegraph/src/pr/errors.ts

export type PRErrorCode =
  | 'NOT_INITIALIZED'
  | 'OFFLINE_MODE'
  | 'AUTH_FAILED'
  | 'REPO_NOT_FOUND'
  | 'REMOTE_PARSE_FAILED'
  | 'APPLY_FAILED';

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
  REPO_NOT_FOUND: {
    message: 'Git repository not found',
    suggestion: 'Ensure the path is a valid git repository'
  },
  REMOTE_PARSE_FAILED: {
    message: 'Could not parse GitHub owner/repo from remote URL',
    suggestion: 'Ensure the remote URL is a valid GitHub URL'
  },
  APPLY_FAILED: {
    message: 'Failed to apply refactoring changes',
    suggestion: 'Check file permissions and ensure files exist'
  }
};
```

### テスト
- TEST-v234-007: エラーメッセージに suggestion が含まれることを確認

---

## TSK-v234-002: PRCreator 状態管理リファクタ

### 概要
PRCreator に状態管理（uninitialized/offline/full）を追加

### 対象ファイル
- `packages/codegraph/src/pr/pr-creator.ts` (修正)

### 実装内容

```typescript
// 追加する型定義
type PRCreatorState = 'uninitialized' | 'offline' | 'full';

// PRCreator クラスに追加
export class PRCreator extends EventEmitter {
  private state: PRCreatorState = 'uninitialized';
  
  // 状態チェックメソッド
  private ensureState(...allowed: PRCreatorState[]): void {
    if (!allowed.includes(this.state)) {
      const err = PRErrorMessages[this.state === 'offline' ? 'OFFLINE_MODE' : 'NOT_INITIALIZED'];
      throw new PRCreatorError(
        err.message,
        this.state === 'offline' ? 'OFFLINE_MODE' : 'NOT_INITIALIZED',
        err.suggestion
      );
    }
  }
  
  getState(): PRCreatorState {
    return this.state;
  }
}
```

### 依存関係
- TSK-v234-001 が先に完了している必要がある

---

## TSK-v234-003: initializeOffline() 実装

### 概要
GitHub 認証なしでローカル操作のみ初期化するメソッド

### 対象ファイル
- `packages/codegraph/src/pr/pr-creator.ts` (修正)

### 実装内容

```typescript
/**
 * Initialize for offline operations (preview only)
 * Does not require GitHub authentication
 */
async initializeOffline(): Promise<{ success: boolean; error?: string }> {
  try {
    // Initialize Git operations (local only)
    this.git = new GitOperations({
      repoPath: this.config.repoPath,
      remote: this.config.remote,
    });

    // Initialize refactoring applier
    this.applier = new RefactoringApplier({
      repoPath: this.config.repoPath,
      createBackups: this.config.createBackups,
    });

    // Store current branch for potential rollback
    this.originalBranch = this.git.getCurrentBranch();

    this.state = 'offline';
    return { success: true };
  } catch (error) {
    return {
      success: false,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}
```

### テスト
- TEST-v234-001: initializeOffline() が成功する
- TEST-v234-003: offline 状態で create() はエラー

---

## TSK-v234-004: preview() メソッド実装

### 概要
GitHub 認証なしで PR プレビューを生成するメソッド

### 対象ファイル
- `packages/codegraph/src/pr/pr-creator.ts` (修正)
- `packages/codegraph/src/pr/types.ts` (修正)

### 実装内容

```typescript
// types.ts に PRPreview 型を追加/拡張
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

// pr-creator.ts に preview() メソッド追加
/**
 * Generate PR preview without GitHub authentication
 * @see REQ-CG-v234-001
 */
async preview(suggestion: RefactoringSuggestion): Promise<PRPreview> {
  this.ensureState('offline', 'full');

  const branchName = generateBranchName(suggestion);
  const commitMessage = generateCommitMessage(suggestion);
  const title = this.templateGenerator.generateTitle(suggestion);
  
  // Preview diffs without applying
  const diffs = this.applier!.preview(suggestion);
  const body = this.templateGenerator.generate(suggestion, diffs);
  
  const filesChanged = diffs.map(d => d.filePath);
  const linesAdded = diffs.reduce((sum, d) => sum + d.additions, 0);
  const linesDeleted = diffs.reduce((sum, d) => sum + d.deletions, 0);

  return {
    branchName,
    commitMessage,
    title,
    body,
    diffs,
    filesChanged,
    linesAdded,
    linesDeleted,
  };
}
```

### テスト
- TEST-v234-002: offline モードでプレビュー生成成功

---

## TSK-v234-005: CLI index コマンド追加

### 概要
`cg index <path>` コマンドを追加

### 対象ファイル
- `packages/codegraph/src/cli.ts` (修正)

### 実装内容

```typescript
// Index command
program
  .command('index <path>')
  .description('Index a codebase for graph analysis')
  .option('-d, --depth <n>', 'Maximum directory depth', '3')
  .option('--json', 'Output as JSON')
  .option('--languages <langs>', 'Target languages (comma-separated)')
  .action(async (path, options) => {
    try {
      const { CodeGraph } = await import('./codegraph.js');
      const cg = new CodeGraph({ storage: 'memory' });
      
      const maxDepth = parseInt(options.depth, 10);
      const result = await cg.index(path, { maxDepth });
      
      if (options.json) {
        console.log(JSON.stringify(result, null, 2));
      } else {
        console.log('✅ Indexing complete');
        console.log(`   Entities: ${result.entities}`);
        console.log(`   Relations: ${result.relations}`);
        console.log(`   Files: ${result.files}`);
      }
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });
```

### テスト
- TEST-v234-004: CLI から index 実行可能

---

## TSK-v234-006: CLI query コマンド追加

### 概要
`cg query <query>` コマンドを追加

### 対象ファイル
- `packages/codegraph/src/cli.ts` (修正)

### 実装内容

```typescript
// Query command
program
  .command('query <query>')
  .description('Query entities in the code graph')
  .option('--type <type>', 'Entity type filter (function, class, method, etc.)')
  .option('--limit <n>', 'Maximum results', '10')
  .option('--json', 'Output as JSON')
  .action(async (query, options) => {
    try {
      const { CodeGraph } = await import('./codegraph.js');
      const cg = new CodeGraph({ storage: 'memory' });
      
      const limit = parseInt(options.limit, 10);
      const results = await cg.query(query, { 
        type: options.type,
        limit 
      });
      
      if (options.json) {
        console.log(JSON.stringify(results, null, 2));
      } else {
        console.log(`Found ${results.length} entities:`);
        results.forEach((e, i) => {
          console.log(`  ${i + 1}. ${e.name} (${e.type}) - ${e.filePath}`);
        });
      }
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });
```

### テスト
- TEST-v234-005: CLI から query 実行可能

---

## TSK-v234-007: CLI stats コマンド追加

### 概要
`cg stats` コマンドを追加

### 対象ファイル
- `packages/codegraph/src/cli.ts` (修正)

### 実装内容

```typescript
// Stats command
program
  .command('stats')
  .description('Show code graph statistics')
  .option('--json', 'Output as JSON')
  .action(async (options) => {
    try {
      const { CodeGraph } = await import('./codegraph.js');
      const cg = new CodeGraph({ storage: 'memory' });
      
      const stats = cg.getStats();
      
      if (options.json) {
        console.log(JSON.stringify(stats, null, 2));
      } else {
        console.log('📊 Graph Statistics:');
        console.log(`   Entities: ${stats.entities}`);
        console.log(`   Relations: ${stats.relations}`);
        console.log(`   Files: ${stats.files}`);
        if (stats.languages) {
          console.log(`   Languages: ${stats.languages.join(', ')}`);
        }
      }
    } catch (error) {
      console.error('❌ Error:', error instanceof Error ? error.message : error);
      process.exit(1);
    }
  });
```

### テスト
- TEST-v234-006: CLI から stats 実行可能

---

## TSK-v234-008: エクスポート・バージョン更新

### 概要
新規ファイルのエクスポートとバージョン番号更新

### 対象ファイル
- `packages/codegraph/src/pr/index.ts` (修正)
- `packages/codegraph/package.json` (修正)

### 実装内容

```typescript
// packages/codegraph/src/pr/index.ts に追加
export { PRCreatorError, PRErrorCode, PRErrorMessages } from './errors.js';
export type { PRPreview } from './types.js';
```

```json
// packages/codegraph/package.json
{
  "version": "2.3.4"
}
```

---

## TSK-v234-009: テスト作成・実行

### 概要
全要件のテストを作成し実行

### 対象ファイル
- `packages/codegraph/src/pr/__tests__/pr-creator.test.ts` (修正/追加)

### テスト項目

| テストID | 内容 |
|----------|------|
| TEST-v234-001 | initializeOffline() が成功する |
| TEST-v234-002 | offline モードで preview() 生成成功 |
| TEST-v234-003 | offline モードで create() はエラー |
| TEST-v234-004 | CLI `cg index` が動作する |
| TEST-v234-005 | CLI `cg query` が動作する |
| TEST-v234-006 | CLI `cg stats` が動作する |
| TEST-v234-007 | エラーメッセージに suggestion 含む |

---

## 実行順序

```
TSK-v234-001 (エラークラス)
    │
    ▼
TSK-v234-002 (状態管理)
    │
    ├─────────────────┐
    ▼                 ▼
TSK-v234-003      TSK-v234-005
(initializeOffline) (CLI index)
    │                 │
    ▼                 ▼
TSK-v234-004      TSK-v234-006
(preview)         (CLI query)
    │                 │
    │                 ▼
    │             TSK-v234-007
    │             (CLI stats)
    │                 │
    └────────┬────────┘
             ▼
        TSK-v234-008
        (エクスポート)
             │
             ▼
        TSK-v234-009
        (テスト)
```

---

## トレーサビリティ

| 要件ID | 設計ID | タスクID | テストID |
|--------|--------|----------|----------|
| REQ-CG-v234-001 | DES-CG-v234-001 | TSK-v234-003, TSK-v234-004 | TEST-v234-001, TEST-v234-002 |
| REQ-CG-v234-002 | DES-CG-v234-002 | TSK-v234-005, TSK-v234-006, TSK-v234-007 | TEST-v234-004, TEST-v234-005, TEST-v234-006 |
| REQ-CG-v234-003 | DES-CG-v234-003 | TSK-v234-002, TSK-v234-003 | TEST-v234-001, TEST-v234-003 |
| REQ-CG-v234-004 | DES-CG-v234-004 | TSK-v234-001 | TEST-v234-007 |

---

**Document Version**: 1.0  
**Last Updated**: 2026-01-10
