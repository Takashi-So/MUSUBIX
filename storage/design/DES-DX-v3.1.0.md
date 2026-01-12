# 設計書: MUSUBIX v3.1.0 開発者体験強化

**Document ID**: DES-DX-v3.1.0  
**Version**: 1.0.0  
**Created**: 2026-01-13  
**Author**: AI Agent  
**Status**: Draft  
**Traces To**: REQ-DX-v3.1.0

---

## 1. 概要

### 1.1 設計スコープ

| 機能ID | 機能名 | パッケージ |
|--------|--------|-----------|
| DES-WATCH | 自動Lint/Test実行 | `@nahisaho/musubix-core` |
| DES-SPACES | Copilot Spaces統合 | `@musubix/knowledge` |
| DES-CODEQL | CodeQL連携 | `@nahisaho/musubix-security` |
| DES-TEAM | チーム共有機能 | `@musubix/knowledge` |

### 1.2 アーキテクチャ概要（C4 Context）

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           Developer                                      │
└─────────────────────────┬───────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                      VS Code + GitHub Copilot                            │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                    MCP Server Connection                          │   │
│  └──────────────────────────────────────────────────────────────────┘   │
└─────────────────────────┬───────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                      MUSUBIX MCP Server                                  │
│  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐           │
│  │   Watch    │ │   Spaces   │ │   CodeQL   │ │    Team    │           │
│  │   Module   │ │   Module   │ │   Module   │ │   Module   │           │
│  └──────┬─────┘ └──────┬─────┘ └──────┬─────┘ └──────┬─────┘           │
│         │              │              │              │                  │
│         ▼              ▼              ▼              ▼                  │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                    Knowledge Store                               │   │
│  └─────────────────────────────────────────────────────────────────┘   │
└─────────────────────────┬───────────────────────────────────────────────┘
                          │
          ┌───────────────┼───────────────┐
          ▼               ▼               ▼
┌─────────────────┐ ┌───────────┐ ┌────────────────┐
│ GitHub Copilot  │ │  GitHub   │ │   Local Git    │
│    Spaces API   │ │ CodeQL    │ │   Repository   │
└─────────────────┘ └───────────┘ └────────────────┘
```

---

## 2. Watch Module設計（DES-WATCH）

### 2.1 コンポーネント図（C4 Component）

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Watch Module                                  │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐  │
│  │  FileWatcher    │───▶│  TaskScheduler  │───▶│  ResultReporter │  │
│  │  (chokidar)     │    │  (debounce)     │    │  (JSON/Terminal)│  │
│  └─────────────────┘    └────────┬────────┘    └─────────────────┘  │
│                                  │                                   │
│                    ┌─────────────┼─────────────┐                    │
│                    ▼             ▼             ▼                    │
│           ┌──────────────┐ ┌──────────┐ ┌──────────────┐           │
│           │  LintRunner  │ │TestRunner│ │SecurityRunner│           │
│           │  (ESLint)    │ │ (Vitest) │ │ (Extractor)  │           │
│           └──────────────┘ └──────────┘ └──────────────┘           │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 クラス設計

#### 2.2.1 FileWatcher

```typescript
// packages/core/src/watch/file-watcher.ts

interface WatchConfig {
  paths: string[];
  ignore: string[];
  debounceMs: number;
  extensions: string[];
}

interface FileChangeEvent {
  type: 'add' | 'change' | 'unlink';
  path: string;
  timestamp: Date;
}

class FileWatcher {
  private watcher: chokidar.FSWatcher;
  private config: WatchConfig;
  
  constructor(config: WatchConfig);
  
  start(): Promise<void>;
  stop(): Promise<void>;
  
  on(event: 'change', handler: (event: FileChangeEvent) => void): void;
  on(event: 'error', handler: (error: Error) => void): void;
}
```

#### 2.2.2 TaskScheduler

```typescript
// packages/core/src/watch/task-scheduler.ts

type TaskType = 'lint' | 'test' | 'security' | 'ears';

interface ScheduledTask {
  id: string;
  type: TaskType;
  files: string[];
  scheduledAt: Date;
  status: 'pending' | 'running' | 'completed' | 'failed';
}

interface TaskResult {
  taskId: string;
  type: TaskType;
  success: boolean;
  duration: number;
  issues: Issue[];
}

class TaskScheduler {
  private queue: Map<string, ScheduledTask>;
  private debounceTimers: Map<string, NodeJS.Timeout>;
  private runners: Map<TaskType, TaskRunner>;
  
  constructor(debounceMs: number);
  
  schedule(type: TaskType, files: string[]): void;
  cancel(taskId: string): void;
  
  onTaskComplete(handler: (result: TaskResult) => void): void;
}
```

#### 2.2.3 ResultReporter

```typescript
// packages/core/src/watch/result-reporter.ts

interface ReportConfig {
  outputDir: string;
  format: 'json' | 'terminal' | 'both';
  verbose: boolean;
}

interface WatchReport {
  timestamp: Date;
  tasks: TaskResult[];
  summary: {
    total: number;
    passed: number;
    failed: number;
    issues: number;
  };
}

class ResultReporter {
  constructor(config: ReportConfig);
  
  report(result: TaskResult): void;
  getLatestReport(): WatchReport;
  exportJSON(path: string): Promise<void>;
}
```

### 2.3 CLI設計

```bash
# 基本コマンド
musubix watch [path]                    # 監視開始
musubix watch --lint                    # Lintのみ
musubix watch --test                    # Testのみ
musubix watch --security                # セキュリティのみ
musubix watch --all                     # すべて有効（デフォルト）

# オプション
--debounce <ms>                         # デバウンス時間（デフォルト: 300）
--ignore <pattern>                      # 除外パターン追加
--output <dir>                          # 結果出力ディレクトリ
--verbose                               # 詳細出力
```

### 2.4 MCPツール設計

| ツール名 | 説明 | パラメータ |
|---------|------|-----------|
| `watch_start` | 監視開始 | `path`, `options` |
| `watch_stop` | 監視停止 | - |
| `watch_status` | 監視状態取得 | - |
| `watch_results` | 最新結果取得 | `type?` |

### 2.5 トレーサビリティ

| 設計ID | 要件ID | 説明 |
|--------|--------|------|
| DES-WATCH-001 | REQ-WATCH-001 | FileWatcher実装 |
| DES-WATCH-002 | REQ-WATCH-002 | LintRunner実装 |
| DES-WATCH-003 | REQ-WATCH-003 | TestRunner実装 |
| DES-WATCH-004 | REQ-WATCH-004 | EARSRunner実装 |
| DES-WATCH-005 | REQ-WATCH-005 | SecurityRunner実装 |
| DES-WATCH-006 | REQ-WATCH-006 | ResultReporter実装 |
| DES-WATCH-007 | REQ-WATCH-007 | TaskScheduler debounce |
| DES-WATCH-008 | REQ-WATCH-008 | ignore pattern handling |

---

## 3. Spaces Module設計（DES-SPACES）

### 3.1 コンポーネント図

```
┌─────────────────────────────────────────────────────────────────────┐
│                       Spaces Module                                  │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐  │
│  │  SpacesClient   │───▶│  SyncManager    │───▶│ ConflictResolver│  │
│  │  (GitHub API)   │    │  (push/pull)    │    │  (3-way merge)  │  │
│  └─────────────────┘    └────────┬────────┘    └─────────────────┘  │
│                                  │                                   │
│                                  ▼                                   │
│                    ┌─────────────────────────┐                      │
│                    │    EntityMapper         │                      │
│                    │ (Knowledge ↔ Spaces)    │                      │
│                    └─────────────────────────┘                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 3.2 クラス設計

#### 3.2.1 SpacesClient

```typescript
// packages/knowledge/src/spaces/spaces-client.ts

interface SpacesConfig {
  token: string;
  spaceId: string;
  baseUrl?: string;
}

interface SpacesEntity {
  id: string;
  type: string;
  content: string;
  metadata: Record<string, unknown>;
  updatedAt: Date;
}

class SpacesClient {
  constructor(config: SpacesConfig);
  
  connect(): Promise<void>;
  disconnect(): Promise<void>;
  
  list(filter?: { type?: string }): Promise<SpacesEntity[]>;
  get(id: string): Promise<SpacesEntity | null>;
  put(entity: SpacesEntity): Promise<void>;
  delete(id: string): Promise<void>;
  
  getLastSyncTime(): Promise<Date | null>;
}
```

#### 3.2.2 SyncManager

```typescript
// packages/knowledge/src/spaces/sync-manager.ts

type SyncDirection = 'push' | 'pull' | 'bidirectional';

interface SyncOptions {
  direction: SyncDirection;
  entityTypes?: string[];
  dryRun?: boolean;
  force?: boolean;
}

interface SyncResult {
  direction: SyncDirection;
  pushed: number;
  pulled: number;
  conflicts: ConflictInfo[];
  timestamp: Date;
}

interface ConflictInfo {
  entityId: string;
  localVersion: Entity;
  remoteVersion: SpacesEntity;
  resolution?: 'local' | 'remote' | 'merged';
}

class SyncManager {
  constructor(
    private store: KnowledgeStore,
    private client: SpacesClient,
    private mapper: EntityMapper
  );
  
  push(options?: Partial<SyncOptions>): Promise<SyncResult>;
  pull(options?: Partial<SyncOptions>): Promise<SyncResult>;
  sync(options?: Partial<SyncOptions>): Promise<SyncResult>;
  
  getConflicts(): ConflictInfo[];
  resolveConflict(entityId: string, resolution: 'local' | 'remote' | 'merged', mergedEntity?: Entity): Promise<void>;
}
```

#### 3.2.3 EntityMapper

```typescript
// packages/knowledge/src/spaces/entity-mapper.ts

class EntityMapper {
  toSpacesEntity(entity: Entity): SpacesEntity;
  fromSpacesEntity(spacesEntity: SpacesEntity): Entity;
  
  toSpacesRelation(relation: Relation): SpacesEntity;
  fromSpacesRelation(spacesEntity: SpacesEntity): Relation;
}
```

### 3.3 CLI設計

```bash
# 接続管理
musubix spaces connect                  # GitHub認証・Space選択
musubix spaces disconnect               # 接続解除
musubix spaces status                   # 接続状態表示

# 同期操作
musubix spaces push                     # ローカル → Spaces
musubix spaces pull                     # Spaces → ローカル
musubix spaces sync                     # 双方向同期

# オプション
--types <types>                         # 同期対象タイプ（requirement,design,task,pattern,adr）
--dry-run                               # プレビューのみ
--force                                 # 競合時に強制上書き
```

### 3.4 MCPツール設計

| ツール名 | 説明 | パラメータ |
|---------|------|-----------|
| `spaces_connect` | Spaces接続 | `token`, `spaceId` |
| `spaces_push` | プッシュ | `types?`, `dryRun?` |
| `spaces_pull` | プル | `types?`, `dryRun?` |
| `spaces_status` | 状態取得 | - |
| `spaces_conflicts` | 競合一覧 | - |
| `spaces_resolve` | 競合解決 | `entityId`, `resolution` |

### 3.5 トレーサビリティ

| 設計ID | 要件ID | 説明 |
|--------|--------|------|
| DES-SPACES-001 | REQ-SPACES-001 | SpacesClient.connect() |
| DES-SPACES-002 | REQ-SPACES-002 | SyncManager.push() |
| DES-SPACES-003 | REQ-SPACES-003 | SyncManager.pull() |
| DES-SPACES-004 | REQ-SPACES-004 | 自動同期（将来実装） |
| DES-SPACES-005 | REQ-SPACES-005 | SyncOptions.entityTypes |
| DES-SPACES-006 | REQ-SPACES-006 | ConflictResolver |

---

## 4. CodeQL Module設計（DES-CODEQL）

### 4.1 コンポーネント図

```
┌─────────────────────────────────────────────────────────────────────┐
│                       CodeQL Module                                  │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐  │
│  │  SARIFParser    │───▶│ FindingsMerger  │───▶│ CWEMapper       │  │
│  │  (SARIF 2.1.0)  │    │ (deduplication) │    │ (CWE/CVE DB)    │  │
│  └─────────────────┘    └────────┬────────┘    └─────────────────┘  │
│                                  │                                   │
│                                  ▼                                   │
│                    ┌─────────────────────────┐                      │
│                    │   FindingsStore         │                      │
│                    │  (Knowledge Store)      │                      │
│                    └─────────────────────────┘                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 4.2 クラス設計

#### 4.2.1 SARIFParser

```typescript
// packages/security/src/codeql/sarif-parser.ts

interface SARIFResult {
  ruleId: string;
  level: 'error' | 'warning' | 'note';
  message: string;
  locations: SARIFLocation[];
  fingerprints?: Record<string, string>;
}

interface SARIFLocation {
  physicalLocation: {
    artifactLocation: { uri: string };
    region: { startLine: number; endLine?: number; startColumn?: number };
  };
}

interface ParsedSARIF {
  tool: { name: string; version: string };
  results: SARIFResult[];
  rules: Map<string, SARIFRule>;
}

class SARIFParser {
  parse(content: string): ParsedSARIF;
  parseFile(path: string): Promise<ParsedSARIF>;
  
  validate(content: string): { valid: boolean; errors: string[] };
}
```

#### 4.2.2 FindingsMerger

```typescript
// packages/security/src/codeql/findings-merger.ts

interface SecurityFinding {
  id: string;
  source: 'codeql' | 'musubix' | 'both';
  severity: 'critical' | 'high' | 'medium' | 'low';
  cweId?: string;
  cveId?: string;
  location: {
    file: string;
    line: number;
    column?: number;
  };
  message: string;
  rule: string;
  fingerprint: string;
}

class FindingsMerger {
  constructor(private cweMapper: CWEMapper);
  
  merge(
    codeqlFindings: ParsedSARIF,
    musubixFindings: SecurityIssue[]
  ): SecurityFinding[];
  
  deduplicate(findings: SecurityFinding[]): SecurityFinding[];
  
  private generateFingerprint(finding: SecurityFinding): string;
}
```

#### 4.2.3 CWEMapper

```typescript
// packages/security/src/codeql/cwe-mapper.ts

interface CWEEntry {
  id: string;
  name: string;
  description: string;
  severity: 'critical' | 'high' | 'medium' | 'low';
  relatedCVEs?: string[];
}

class CWEMapper {
  constructor();
  
  mapRuleIdToCWE(ruleId: string): CWEEntry | null;
  getCWE(cweId: string): CWEEntry | null;
  getSeverity(cweId: string): 'critical' | 'high' | 'medium' | 'low';
  
  searchByKeyword(keyword: string): CWEEntry[];
}
```

### 4.3 CLI設計

```bash
# インポート
musubix codeql import <sarif-file>      # SARIFファイルインポート
musubix codeql import --dir <dir>       # ディレクトリ内全SARIFインポート

# 表示
musubix codeql list                     # 検出結果一覧
musubix codeql show <finding-id>        # 詳細表示

# 統合
musubix codeql merge                    # MUSUBIX結果と統合
musubix codeql export <output>          # 統合結果エクスポート

# GitHub Actions
musubix codeql workflow                 # ワークフロー生成
```

### 4.4 MCPツール設計

| ツール名 | 説明 | パラメータ |
|---------|------|-----------|
| `codeql_import` | SARIFインポート | `path` |
| `codeql_findings` | 検出結果取得 | `severity?`, `cweId?` |
| `codeql_status` | 統合状態 | - |
| `codeql_merge` | 結果統合 | - |

### 4.5 トレーサビリティ

| 設計ID | 要件ID | 説明 |
|--------|--------|------|
| DES-CODEQL-001 | REQ-CODEQL-001 | SARIFParser |
| DES-CODEQL-002 | REQ-CODEQL-002 | FindingsMerger |
| DES-CODEQL-003 | REQ-CODEQL-003 | CWEMapper |
| DES-CODEQL-004 | REQ-CODEQL-004 | FindingsStore |
| DES-CODEQL-005 | REQ-CODEQL-005 | workflow生成 |
| DES-CODEQL-006 | REQ-CODEQL-006 | MCPツール |

---

## 5. Team Module設計（DES-TEAM）

### 5.1 コンポーネント図

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Team Module                                   │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐  │
│  │   GitClient     │───▶│  TeamSyncManager│───▶│ MergeResolver   │  │
│  │ (simple-git)    │    │   (push/pull)   │    │  (3-way merge)  │  │
│  └─────────────────┘    └────────┬────────┘    └─────────────────┘  │
│                                  │                                   │
│                                  ▼                                   │
│                    ┌─────────────────────────┐                      │
│                    │    HistoryManager       │                      │
│                    │   (commit log/diff)     │                      │
│                    └─────────────────────────┘                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 5.2 クラス設計

#### 5.2.1 GitClient

```typescript
// packages/knowledge/src/team/git-client.ts

interface GitConfig {
  knowledgePath: string;
  remoteName?: string;
  branch?: string;
}

interface CommitInfo {
  hash: string;
  message: string;
  author: string;
  date: Date;
  files: string[];
}

class GitClient {
  constructor(config: GitConfig);
  
  init(): Promise<void>;
  addRemote(name: string, url: string): Promise<void>;
  
  status(): Promise<{ staged: string[]; modified: string[]; untracked: string[] }>;
  add(files: string[]): Promise<void>;
  commit(message: string): Promise<string>;
  
  push(remote?: string, branch?: string): Promise<void>;
  pull(remote?: string, branch?: string): Promise<void>;
  fetch(remote?: string): Promise<void>;
  
  log(limit?: number): Promise<CommitInfo[]>;
  diff(ref1?: string, ref2?: string): Promise<string>;
  
  hasConflicts(): Promise<boolean>;
  getConflictFiles(): Promise<string[]>;
}
```

#### 5.2.2 TeamSyncManager

```typescript
// packages/knowledge/src/team/team-sync-manager.ts

interface TeamSyncConfig {
  autoCommit: boolean;
  commitPrefix: string;
  remoteName: string;
  branch: string;
}

interface TeamSyncResult {
  operation: 'push' | 'pull';
  success: boolean;
  commits: CommitInfo[];
  conflicts?: string[];
  error?: string;
}

class TeamSyncManager {
  constructor(
    private gitClient: GitClient,
    private store: KnowledgeStore,
    private config: TeamSyncConfig
  );
  
  init(remoteUrl: string): Promise<void>;
  
  push(message?: string): Promise<TeamSyncResult>;
  pull(): Promise<TeamSyncResult>;
  
  status(): Promise<{
    ahead: number;
    behind: number;
    modified: string[];
    conflicts: string[];
  }>;
  
  diff(): Promise<string>;
  
  resolveConflict(file: string, resolution: 'ours' | 'theirs'): Promise<void>;
}
```

#### 5.2.3 HistoryManager

```typescript
// packages/knowledge/src/team/history-manager.ts

interface VersionInfo {
  version: string;
  commitHash: string;
  date: Date;
  author: string;
  changes: {
    added: string[];
    modified: string[];
    deleted: string[];
  };
}

class HistoryManager {
  constructor(private gitClient: GitClient);
  
  getHistory(limit?: number): Promise<VersionInfo[]>;
  getEntityHistory(entityId: string, limit?: number): Promise<VersionInfo[]>;
  
  rollback(commitHash: string): Promise<void>;
  restore(entityId: string, commitHash: string): Promise<void>;
  
  compare(hash1: string, hash2: string): Promise<{
    added: Entity[];
    modified: Array<{ before: Entity; after: Entity }>;
    deleted: Entity[];
  }>;
}
```

### 5.3 CLI設計

```bash
# 初期化
musubix team init <remote-url>          # Git同期初期化
musubix team status                     # 同期状態表示

# 同期操作
musubix team push                       # プッシュ
musubix team push -m "message"          # コミットメッセージ付き
musubix team pull                       # プル

# 差分・履歴
musubix team diff                       # ローカル vs リモート差分
musubix team log                        # コミット履歴
musubix team log --entity <id>          # エンティティ履歴

# 競合解決
musubix team conflicts                  # 競合一覧
musubix team resolve <file> --ours      # ローカル優先
musubix team resolve <file> --theirs    # リモート優先

# ロールバック
musubix team rollback <commit>          # 特定コミットに戻す
```

### 5.4 MCPツール設計

| ツール名 | 説明 | パラメータ |
|---------|------|-----------|
| `team_init` | 初期化 | `remoteUrl` |
| `team_push` | プッシュ | `message?` |
| `team_pull` | プル | - |
| `team_status` | 状態取得 | - |
| `team_diff` | 差分表示 | - |
| `team_log` | 履歴取得 | `limit?`, `entityId?` |
| `team_conflicts` | 競合一覧 | - |
| `team_resolve` | 競合解決 | `file`, `resolution` |

### 5.5 トレーサビリティ

| 設計ID | 要件ID | 説明 |
|--------|--------|------|
| DES-TEAM-001 | REQ-TEAM-001 | GitClient.init() |
| DES-TEAM-002 | REQ-TEAM-002 | TeamSyncManager.push() |
| DES-TEAM-003 | REQ-TEAM-003 | TeamSyncManager.pull() |
| DES-TEAM-004 | REQ-TEAM-004 | MergeResolver |
| DES-TEAM-005 | REQ-TEAM-005 | HistoryManager |
| DES-TEAM-006 | REQ-TEAM-006 | Git権限活用 |
| DES-TEAM-007 | REQ-TEAM-007 | diff表示 |
| DES-TEAM-008 | REQ-TEAM-008 | MCPツール |

---

## 6. パッケージ構成

### 6.1 新規ファイル一覧

```
packages/
├── core/src/
│   └── watch/
│       ├── index.ts
│       ├── file-watcher.ts
│       ├── task-scheduler.ts
│       ├── result-reporter.ts
│       ├── runners/
│       │   ├── lint-runner.ts
│       │   ├── test-runner.ts
│       │   ├── security-runner.ts
│       │   └── ears-runner.ts
│       └── types.ts
├── knowledge/src/
│   ├── spaces/
│   │   ├── index.ts
│   │   ├── spaces-client.ts
│   │   ├── sync-manager.ts
│   │   ├── entity-mapper.ts
│   │   └── conflict-resolver.ts
│   └── team/
│       ├── index.ts
│       ├── git-client.ts
│       ├── team-sync-manager.ts
│       ├── merge-resolver.ts
│       └── history-manager.ts
├── security/src/
│   └── codeql/
│       ├── index.ts
│       ├── sarif-parser.ts
│       ├── findings-merger.ts
│       ├── cwe-mapper.ts
│       ├── cwe-database.ts
│       └── types.ts
└── mcp-server/src/
    └── tools/
        ├── watch-tools.ts
        ├── spaces-tools.ts
        ├── codeql-tools.ts
        └── team-tools.ts
```

### 6.2 依存関係

| パッケージ | 新規依存 | 用途 |
|-----------|---------|------|
| `@nahisaho/musubix-core` | `chokidar` | ファイル監視 |
| `@musubix/knowledge` | `simple-git` | Git操作 |
| `@nahisaho/musubix-security` | - | SARIF標準対応 |

---

## 7. 設計パターン適用

| パターン | 適用箇所 | 理由 |
|---------|---------|------|
| **Observer** | FileWatcher → TaskScheduler | ファイル変更イベントの通知 |
| **Strategy** | TaskRunner (Lint/Test/Security) | 実行戦略の切り替え |
| **Adapter** | EntityMapper | Knowledge Store ↔ Spaces変換 |
| **Facade** | SyncManager, TeamSyncManager | 複雑な操作の単純化 |
| **Repository** | FindingsStore | セキュリティ検出結果の永続化 |

---

## 8. 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-13 | ✓ |
| レビュアー | | | |
| 承認者 | | | |

---

## 9. 変更履歴

| バージョン | 日付 | 変更者 | 変更内容 |
|-----------|------|--------|---------|
| 1.0.0 | 2026-01-13 | AI Agent | 初版作成 |
