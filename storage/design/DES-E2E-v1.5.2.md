# Design: E2E Test Enhancement v1.5.2

> **C4モデル** に基づく設計ドキュメント

## Overview

| 項目 | 内容 |
|-----|------|
| バージョン | 1.5.2 |
| 設計パターン | Facade, Factory, Builder, Strategy |
| 関連要件 | REQ-E2E-001〜007 |

---

## 1. Component Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                         E2E Test Framework                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
│  │  TestProject │  │  TestFixtures│  │  CliRunner   │          │
│  │  (Factory)   │  │  (Repository)│  │  (Facade)    │          │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │
│         │                 │                 │                   │
│         └─────────────────┼─────────────────┘                   │
│                           │                                      │
│                    ┌──────▼───────┐                             │
│                    │ TestContext  │                             │
│                    │ (Builder)    │                             │
│                    └──────┬───────┘                             │
│                           │                                      │
│  ┌──────────────┐  ┌──────▼───────┐  ┌──────────────┐          │
│  │ Assertions   │  │ TestRunner   │  │ MockServer   │          │
│  │ (Strategy)   │  │ (Facade)     │  │ (Adapter)    │          │
│  └──────────────┘  └──────────────┘  └──────────────┘          │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Component Details

### 2.1 TestProject (REQ-E2E-001)

**パターン**: Factory

**責務**:
- テスト用プロジェクトディレクトリの作成・削除
- サンプルファイルの配置
- 環境変数のセットアップ

```typescript
interface TestProject {
  readonly path: string;
  readonly name: string;
  
  create(): Promise<void>;
  destroy(): Promise<void>;
  addFile(relativePath: string, content: string): Promise<void>;
  getFile(relativePath: string): Promise<string>;
  fileExists(relativePath: string): boolean;
}

interface TestProjectOptions {
  name?: string;
  template?: 'minimal' | 'full' | 'sdd';
  cleanup?: boolean;
}

function createTestProject(options?: TestProjectOptions): TestProject;
```

### 2.2 TestFixtures (REQ-E2E-001)

**パターン**: Repository

**責務**:
- 共通テストデータの提供
- サンプル要件・設計・コードの管理

```typescript
interface TestFixtures {
  // EARS形式要件サンプル
  requirements: {
    valid: EarsRequirement[];
    invalid: string[];
  };
  
  // C4設計サンプル
  designs: {
    context: C4Diagram;
    container: C4Diagram;
    component: C4Diagram;
  };
  
  // コードサンプル
  code: {
    typescript: string;
    patterns: Record<string, string>;
  };
  
  // トリプルサンプル
  triples: {
    valid: Triple[];
    circular: Triple[];
    inconsistent: Triple[];
  };
}

function getFixtures(): TestFixtures;
```

### 2.3 CliRunner (REQ-E2E-001)

**パターン**: Facade

**責務**:
- CLIコマンドの実行
- 出力・エラー・終了コードの取得
- タイムアウト管理

```typescript
interface CliResult {
  stdout: string;
  stderr: string;
  exitCode: number;
  duration: number;
}

interface CliRunnerOptions {
  cwd?: string;
  env?: Record<string, string>;
  timeout?: number;
  input?: string;
}

class CliRunner {
  constructor(cliPath?: string);
  
  run(args: string[], options?: CliRunnerOptions): Promise<CliResult>;
  runWithInput(args: string[], input: string): Promise<CliResult>;
  
  // ショートカット
  requirements(subcommand: string, ...args: string[]): Promise<CliResult>;
  design(subcommand: string, ...args: string[]): Promise<CliResult>;
  learn(subcommand: string, ...args: string[]): Promise<CliResult>;
  ontology(subcommand: string, ...args: string[]): Promise<CliResult>;
  perf(subcommand: string, ...args: string[]): Promise<CliResult>;
}
```

### 2.4 TestContext (REQ-E2E-002)

**パターン**: Builder

**責務**:
- テストコンテキストの構築
- プロジェクト・フィクスチャ・ランナーの統合

```typescript
class TestContext {
  readonly project: TestProject;
  readonly fixtures: TestFixtures;
  readonly cli: CliRunner;
  
  static builder(): TestContextBuilder;
}

class TestContextBuilder {
  withProject(options?: TestProjectOptions): this;
  withFixtures(fixtures?: Partial<TestFixtures>): this;
  withCliRunner(options?: CliRunnerOptions): this;
  build(): Promise<TestContext>;
}
```

### 2.5 Custom Assertions (REQ-E2E-001)

**パターン**: Strategy

**責務**:
- E2E固有のアサーション提供
- 可読性の高いエラーメッセージ

```typescript
// Vitest拡張
interface CustomMatchers<R = unknown> {
  toBeValidEars(): R;
  toHaveTraceability(id: string): R;
  toMatchC4Schema(): R;
  toBeWithinPerformanceBudget(budget: PerformanceBudget): R;
  toHaveExitCode(code: number): R;
  toContainPattern(pattern: string): R;
}

interface PerformanceBudget {
  maxDuration?: number;
  maxMemory?: number;
}
```

### 2.6 MockMcpServer (REQ-E2E-004)

**パターン**: Adapter

**責務**:
- MCPプロトコルのモック
- ツール呼び出しのシミュレーション

```typescript
interface MockMcpServer {
  start(): Promise<void>;
  stop(): Promise<void>;
  
  // ツール呼び出しの記録
  getToolCalls(): ToolCall[];
  clearCalls(): void;
  
  // レスポンスの設定
  mockToolResponse(toolName: string, response: unknown): void;
  mockToolError(toolName: string, error: Error): void;
}

interface ToolCall {
  name: string;
  arguments: unknown;
  timestamp: Date;
}
```

---

## 3. E2E Test Scenarios

### 3.1 SDD Workflow E2E (REQ-E2E-002)

```typescript
// e2e/sdd-workflow.e2e.test.ts

describe('SDD Workflow E2E', () => {
  let ctx: TestContext;

  beforeAll(async () => {
    ctx = await TestContext.builder()
      .withProject({ template: 'minimal' })
      .withFixtures()
      .build();
  });

  it('should complete full SDD workflow', async () => {
    // 1. 要件分析
    const reqResult = await ctx.cli.requirements('analyze', 'input.md');
    expect(reqResult).toHaveExitCode(0);
    expect(reqResult.stdout).toBeValidEars();

    // 2. 設計生成
    const designResult = await ctx.cli.design('generate', 'requirements.md');
    expect(designResult).toHaveExitCode(0);
    expect(designResult.stdout).toMatchC4Schema();

    // 3. コード生成
    const codeResult = await ctx.cli.codegen('generate', 'design.md');
    expect(codeResult).toHaveExitCode(0);

    // 4. トレーサビリティ確認
    const traceResult = await ctx.cli.trace('matrix');
    expect(traceResult).toHaveExitCode(0);
    expect(traceResult.stdout).toHaveTraceability('REQ-001');
  });
});
```

### 3.2 Learning System E2E (REQ-E2E-003)

```typescript
// e2e/learning.e2e.test.ts

describe('Learning System E2E', () => {
  it('should process feedback and extract patterns', async () => {
    // 1. フィードバック記録
    await ctx.cli.learn('feedback', 'GEN-001', '--result', 'accept');
    
    // 2. パターン一覧
    const patterns = await ctx.cli.learn('patterns');
    expect(patterns.stdout).toContainPattern('acceptance');
    
    // 3. エクスポート・インポート
    await ctx.cli.learn('export', '--output', 'patterns.json');
    expect(ctx.project.fileExists('patterns.json')).toBe(true);
    
    await ctx.cli.learn('import', 'patterns.json');
  });
});
```

### 3.3 Performance E2E (REQ-E2E-005)

```typescript
// e2e/performance.e2e.test.ts

describe('Performance E2E', () => {
  it('should meet startup time budget', async () => {
    const result = await ctx.cli.run(['--version']);
    expect(result).toBeWithinPerformanceBudget({
      maxDuration: 500, // ms
    });
  });

  it('should meet memory budget', async () => {
    const result = await ctx.cli.perf('memory');
    expect(result.stdout).toMatch(/Used: (\d+)MB/);
    const used = parseInt(result.stdout.match(/Used: (\d+)MB/)?.[1] || '0');
    expect(used).toBeLessThan(512);
  });
});
```

---

## 4. File Structure

```
packages/core/
├── src/
│   └── testing/              # NEW: テストユーティリティ
│       ├── index.ts
│       ├── test-project.ts   # TestProject Factory
│       ├── test-fixtures.ts  # TestFixtures Repository
│       ├── cli-runner.ts     # CliRunner Facade
│       ├── test-context.ts   # TestContext Builder
│       ├── assertions.ts     # Custom Assertions
│       └── mock-mcp.ts       # MockMcpServer
│
└── __tests__/
    └── e2e/                  # E2Eテスト
        ├── helpers/          # 既存ヘルパー移行
        ├── sdd-workflow.e2e.test.ts
        ├── learning.e2e.test.ts
        ├── mcp-server.e2e.test.ts
        ├── performance.e2e.test.ts
        ├── error-handling.e2e.test.ts
        └── repl.e2e.test.ts
```

---

## 5. Dependencies

```json
{
  "devDependencies": {
    "@vitest/coverage-v8": "^2.0.0"
  }
}
```

---

## 6. Traceability Matrix

| 要件 | コンポーネント | テストファイル |
|-----|---------------|--------------|
| REQ-E2E-001 | TestProject, TestFixtures, CliRunner | helpers/*.ts |
| REQ-E2E-002 | TestContext | sdd-workflow.e2e.test.ts |
| REQ-E2E-003 | TestContext | learning.e2e.test.ts |
| REQ-E2E-004 | MockMcpServer | mcp-server.e2e.test.ts |
| REQ-E2E-005 | CliRunner | performance.e2e.test.ts |
| REQ-E2E-006 | Assertions | error-handling.e2e.test.ts |
| REQ-E2E-007 | TestContext | repl.e2e.test.ts |

---

**作成日**: 2026-01-06
**設計者**: GitHub Copilot
**ステータス**: Draft
