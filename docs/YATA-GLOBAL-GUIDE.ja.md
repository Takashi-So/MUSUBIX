# YATA Global ユーザーガイド

> **YATA Global** - 分散型知識グラフプラットフォーム

## 📖 概要

YATA Global (`@nahisaho/yata-global`) は、コミュニティベースの知識共有プラットフォームです。フレームワーク知識、設計パターン、ベストプラクティスをグローバルに共有・検索できます。

### 主な特徴

| 機能 | 説明 |
|------|------|
| **フレームワーク知識** | 各種フレームワークのナレッジベース |
| **パターン共有** | 設計パターン・コードパターンの共有 |
| **KGPR** | Knowledge Graph Pull Request によるコントリビューション |
| **オフラインモード** | ローカルキャッシュによるオフライン動作 |
| **同期エンジン** | 自動/手動のデータ同期 |
| **認証・認可** | ユーザー認証とアクセス制御 |

---

## 🚀 インストール

```bash
npm install @nahisaho/yata-global
```

### 前提条件

- Node.js >= 20.0.0
- npm >= 10.0.0

---

## 📘 基本的な使い方

### クライアントの初期化

```typescript
import { createYataGlobal } from '@nahisaho/yata-global';

const yataGlobal = createYataGlobal({
  serverUrl: 'https://api.yata.example.com',  // APIサーバーURL
  offlineMode: false,      // オフラインモード
  cacheSize: 100,          // キャッシュサイズ（MB）
  autoSync: true,          // 自動同期
  syncInterval: 300000,    // 同期間隔（5分）
});

// イベントリスナー登録
yataGlobal.on('sync:start', () => console.log('Sync started'));
yataGlobal.on('sync:complete', (result) => console.log('Sync complete:', result));
yataGlobal.on('sync:error', (error) => console.error('Sync error:', error));

// 終了時
yataGlobal.close();
```

### 設定オプション

```typescript
interface SyncConfig {
  serverUrl: string;        // APIサーバーURL
  offlineMode: boolean;     // オフラインモード（デフォルト: false）
  cacheSize: number;        // ローカルキャッシュサイズ（デフォルト: 100MB）
  autoSync: boolean;        // 自動同期（デフォルト: true）
  syncInterval: number;     // 同期間隔（ミリ秒、デフォルト: 300000）
  retryAttempts: number;    // リトライ回数（デフォルト: 3）
  timeout: number;          // タイムアウト（ミリ秒）
}
```

---

## 🔐 認証

### ログイン

```typescript
// ユーザー名・パスワードでログイン
const token = await yataGlobal.login({
  username: 'developer',
  password: 'secure-password',
});

console.log('Logged in, token expires:', token.expiresAt);
```

### トークン認証

```typescript
// 既存トークンでログイン
const token = await yataGlobal.loginWithToken('your-access-token');
```

### ログアウト

```typescript
await yataGlobal.logout();
```

### 認証状態の確認

```typescript
if (yataGlobal.isAuthenticated()) {
  const user = await yataGlobal.getCurrentUser();
  console.log('Current user:', user?.username);
}
```

---

## 📚 フレームワーク知識

### フレームワークの検索

```typescript
const result = await yataGlobal.searchFrameworks({
  query: 'react',
  category: 'web-frontend',
  language: 'typescript',
  tags: ['ui', 'component'],
  minQuality: 70,
  sortBy: 'popularity',  // 'popularity' | 'quality' | 'updated' | 'relevance'
  limit: 20,
  offset: 0,
});

console.log(`Found ${result.total} frameworks`);
for (const fw of result.items) {
  console.log(`- ${fw.name} v${fw.version} (${fw.popularity}★)`);
}
```

### カテゴリ別フレームワーク

```typescript
const frontendFrameworks = await yataGlobal.getFrameworksByCategory('web-frontend');
```

### フレームワークカテゴリ

```typescript
type FrameworkCategory =
  | 'web-frontend'     // Webフロントエンド
  | 'web-backend'      // Webバックエンド
  | 'mobile'           // モバイル
  | 'desktop'          // デスクトップ
  | 'database'         // データベース
  | 'orm'              // ORM
  | 'testing'          // テスト
  | 'build-tool'       // ビルドツール
  | 'cli'              // CLI
  | 'ai-ml'            // AI/ML
  | 'devops'           // DevOps
  | 'cloud'            // クラウド
  | 'security'         // セキュリティ
  | 'networking'       // ネットワーク
  | 'data-processing'  // データ処理
  | 'logging'          // ロギング
  | 'monitoring'       // モニタリング
  | 'documentation'    // ドキュメント
  | 'other';           // その他
```

### 個別フレームワークの取得

```typescript
const framework = await yataGlobal.getFramework('react-18');
if (framework) {
  console.log('Name:', framework.name);
  console.log('Version:', framework.version);
  console.log('Description:', framework.description);
  console.log('Docs:', framework.documentationUrl);
  console.log('Quality:', framework.quality);
  console.log('Tags:', framework.tags.join(', '));
}
```

---

## 🧩 パターン

### パターンの検索

```typescript
const patterns = await yataGlobal.searchPatterns({
  query: 'repository pattern',
  category: 'data-access',
  language: 'typescript',
  sortBy: 'quality',
  limit: 20,
});

for (const pattern of patterns.items) {
  console.log(`- ${pattern.name}: ${pattern.description}`);
  console.log(`  Rating: ${pattern.rating.average}/5 (${pattern.downloads} downloads)`);
}
```

### パターンカテゴリ

```typescript
type PatternCategory =
  | 'architecture'      // アーキテクチャ
  | 'design-pattern'    // 設計パターン
  | 'testing'           // テスト
  | 'error-handling'    // エラー処理
  | 'authentication'    // 認証
  | 'authorization'     // 認可
  | 'api-design'        // API設計
  | 'data-access'       // データアクセス
  | 'validation'        // バリデーション
  | 'logging'           // ロギング
  | 'caching'           // キャッシュ
  | 'async'             // 非同期
  | 'configuration'     // 設定
  | 'other';            // その他
```

### 個別パターンの取得

```typescript
const pattern = await yataGlobal.getPattern('repository-pattern-ts');
if (pattern) {
  console.log('Name:', pattern.name);
  console.log('Description:', pattern.description);
  console.log('Template:', pattern.template);
  console.log('Example:', pattern.example);
}
```

### パターンの共有

```typescript
// 認証が必要
if (!yataGlobal.isAuthenticated()) {
  await yataGlobal.login({ username, password });
}

const patternId = await yataGlobal.sharePattern({
  name: 'Service Layer Pattern',
  description: 'ビジネスロジックをカプセル化するサービス層パターン',
  category: 'architecture',
  language: 'typescript',
  frameworks: ['nestjs', 'express'],
  template: `
export class {{ServiceName}} {
  constructor(private readonly repository: I{{EntityName}}Repository) {}
  
  async create(dto: Create{{EntityName}}Dto): Promise<{{EntityName}}> {
    // ビジネスロジック
    return this.repository.save(dto);
  }
}`,
  example: `
export class UserService {
  constructor(private readonly repository: IUserRepository) {}
  
  async createUser(dto: CreateUserDto): Promise<User> {
    const exists = await this.repository.findByEmail(dto.email);
    if (exists) throw new ConflictError('User already exists');
    return this.repository.save(dto);
  }
}`,
  tags: ['service', 'layer', 'architecture', 'clean-architecture'],
  visibility: 'public',  // 'public' | 'private' | 'unlisted'
  official: false,
});

console.log('Pattern shared:', patternId);
```

### パターンの評価

```typescript
await yataGlobal.ratePattern('pattern-id', 5);  // 1-5の評価
```

### パターンの削除

```typescript
await yataGlobal.deletePattern('pattern-id');
```

---

## 🔄 同期

### 手動同期

```typescript
const syncResult = await yataGlobal.sync();

console.log('Sync result:');
console.log(`  Frameworks synced: ${syncResult.frameworksSynced}`);
console.log(`  Patterns synced: ${syncResult.patternsSynced}`);
console.log(`  Duration: ${syncResult.duration}ms`);
```

### 同期状態の確認

```typescript
const status = yataGlobal.getSyncStatus();

console.log('Sync status:');
console.log(`  Last sync: ${status.lastSyncAt}`);
console.log(`  Pending changes: ${status.pendingChanges}`);
console.log(`  Is syncing: ${status.isSyncing}`);
```

### オフラインモード

```typescript
// オフラインモードを有効化
yataGlobal.enableOfflineMode();

// オフラインモードを無効化（オンライン復帰）
yataGlobal.disableOfflineMode();
```

オフラインモードでは:
- ローカルキャッシュからデータを取得
- 変更操作は同期キューに保存
- オンライン復帰時に自動同期

---

## 📊 アナリティクス

```typescript
const analytics = await yataGlobal.getAnalytics();

console.log('Platform Statistics:');
console.log(`  Total frameworks: ${analytics.totalFrameworks}`);
console.log(`  Total patterns: ${analytics.totalPatterns}`);
console.log(`  Total users: ${analytics.totalUsers}`);
console.log('');
console.log('Top Frameworks:');
for (const fw of analytics.topFrameworks) {
  console.log(`  - ${fw.name}: ${fw.popularity}★`);
}
console.log('');
console.log('Top Patterns:');
for (const p of analytics.topPatterns) {
  console.log(`  - ${p.name}: ${p.downloads} downloads`);
}
```

---

## 👤 ユーザー管理

### プロフィール取得

```typescript
const user = await yataGlobal.getCurrentUser();
if (user) {
  console.log('Username:', user.username);
  console.log('Email:', user.email);
  console.log('Joined:', user.joinedAt);
}
```

### プロフィール更新

```typescript
await yataGlobal.updateProfile({
  displayName: 'New Display Name',
  bio: 'TypeScript developer',
});
```

---

## 📤 KGPR (Knowledge Graph Pull Request)

KGPRは、ローカル知識グラフの変更をYATA Globalにコントリビュートするためのワークフローです。

### KGPR モジュールのインポート

```typescript
import {
  KGPRManager,
  createKGPRManager,
  MergeEngine,
  createMergeEngine,
  PrivacyFilter,
  NotificationService,
} from '@nahisaho/yata-global';
```

### KGPRワークフロー

```
┌─────────────────────────────────────────────────────────────┐
│                    KGPR ワークフロー                        │
│                                                             │
│  [YATA Local]              [YATA Global]                   │
│       │                         │                          │
│  1. KGPR作成                    │                          │
│  (プライバシーフィルタ適用)      │                          │
│       │                         │                          │
│       ▼                         │                          │
│  2. 差分計算                    │                          │
│  (エンティティ・関係性)          │                          │
│       │                         │                          │
│       └─── 3. KGPR送信 ────────►│                          │
│                                 │                          │
│                            4. レビュー                      │
│                            (approve/reject)                │
│                                 │                          │
│                            5. マージ                        │
│                            (コンフリクト解決)               │
│                                 │                          │
│       ◄───── 6. 結果通知 ───────┘                          │
└─────────────────────────────────────────────────────────────┘
```

### KGPR REST API (HTTPサーバー)

YATA Global HTTPサーバーが提供するKGPR APIエンドポイント:

| メソッド | エンドポイント | 説明 |
|---------|---------------|------|
| GET | `/api/v1/kgprs` | KGPR一覧取得 |
| POST | `/api/v1/kgprs` | KGPR作成 |
| GET | `/api/v1/kgprs/:id` | KGPR詳細取得 |
| POST | `/api/v1/kgprs/:id/review` | KGPRレビュー |
| POST | `/api/v1/kgprs/:id/merge` | KGPRマージ |

### KGPR作成（REST API）

```bash
curl -X POST http://localhost:3000/api/v1/kgprs \
  -H "Content-Type: application/json" \
  -d '{
    "title": "UserService パターンの追加",
    "description": "ユーザー認証フローから学習したパターン",
    "sourceNamespace": "app.services",
    "labels": ["pattern", "authentication"],
    "diff": {
      "entities": {
        "added": [
          {
            "changeType": "add",
            "localId": "entity-1",
            "name": "UserService",
            "entityType": "class",
            "namespace": "app.services",
            "description": "ユーザー管理サービス"
          }
        ],
        "updated": [],
        "deleted": []
      },
      "relationships": {
        "added": [],
        "updated": [],
        "deleted": []
      },
      "stats": {
        "entitiesAdded": 1,
        "entitiesUpdated": 0,
        "entitiesDeleted": 0,
        "relationshipsAdded": 0,
        "relationshipsUpdated": 0,
        "relationshipsDeleted": 0,
        "totalChanges": 1
      }
    }
  }'
```

レスポンス:
```json
{
  "success": true,
  "kgpr": {
    "id": "KGPR-abc123",
    "title": "UserService パターンの追加",
    "status": "pending_review"
  }
}
```

### KGPRレビュー（REST API）

```bash
# 承認
curl -X POST http://localhost:3000/api/v1/kgprs/KGPR-abc123/review \
  -H "Content-Type: application/json" \
  -d '{
    "decision": "approve",
    "comment": "LGTM! Great pattern."
  }'

# 変更要求
curl -X POST http://localhost:3000/api/v1/kgprs/KGPR-abc123/review \
  -H "Content-Type: application/json" \
  -d '{
    "decision": "changes_requested",
    "comment": "Please add more documentation."
  }'
```

### KGPRマージ（REST API）

```bash
curl -X POST http://localhost:3000/api/v1/kgprs/KGPR-abc123/merge \
  -H "Content-Type: application/json" \
  -d '{
    "conflictStrategy": "skip_conflicts"
  }'
```

レスポンス:
```json
{
  "success": true,
  "mergeResult": {
    "merged": true,
    "entitiesMerged": 1,
    "relationshipsMerged": 0,
    "conflicts": [],
    "message": "KGPR merged successfully"
  }
}
```

### マージエンジン

```typescript
import { createMergeEngine } from '@nahisaho/yata-global';

const mergeEngine = createMergeEngine();

// コンフリクト検出
const conflicts = await mergeEngine.detectConflicts(kgpr, globalState);

for (const conflict of conflicts) {
  console.log(`Conflict: ${conflict.type}`);
  console.log(`  Item: ${conflict.name} in ${conflict.namespace}`);
  console.log(`  Severity: ${conflict.severity}`);
  console.log(`  Suggestion: ${conflict.suggestedResolution}`);
}

// マージ実行
const mergeResult = await mergeEngine.merge(kgpr, {
  conflictStrategy: 'skip_conflicts',  // 'fail' | 'skip_conflicts' | 'force'
  dryRun: false,
  mergerId: 'user-123',
  mergerName: 'Developer',
});

console.log(`Merged: ${mergeResult.merged}`);
console.log(`Entities merged: ${mergeResult.entitiesMerged}`);
console.log(`Relationships merged: ${mergeResult.relationshipsMerged}`);
```

### コンフリクトタイプ

```typescript
type ConflictType =
  | 'entity_exists'        // 同名エンティティが既に存在
  | 'entity_modified'      // KGPR作成後にエンティティが変更された
  | 'entity_deleted'       // KGPR作成後にエンティティが削除された
  | 'relationship_exists'  // 関係性が既に存在
  | 'relationship_broken'  // ソース/ターゲットエンティティが存在しない
  | 'circular_dependency'  // 循環依存が発生する
  | 'schema_violation';    // グローバルKGスキーマ違反

type ConflictSeverity = 'error' | 'warning' | 'info';

type ConflictResolution =
  | 'use_local'   // ローカル（KGPR）の値を使用
  | 'use_global'  // グローバルの値を保持
  | 'merge'       // 両方の値をマージ
  | 'skip'        // この変更をスキップ
  | 'rename';     // リネームしてコンフリクト回避
```

---

## 🐳 Docker環境

### Docker Compose での起動

```bash
cd docker
docker compose up -d
```

### 構成

```
┌─────────────────────────────────────────────────────────────┐
│                    Docker Network                           │
│  ┌──────────────────┐    ┌──────────────────────────────┐  │
│  │  yata-global     │    │      musubix-dev             │  │
│  │  (Port 3000)     │◄───│  (Development Environment)   │  │
│  │                  │    │                              │  │
│  │  - HTTP API      │    │  - MUSUBIX CLI               │  │
│  │  - KGPR Server   │    │  - YATA Local                │  │
│  │  - Pattern Store │    │  - Project Workspace         │  │
│  └──────────────────┘    └──────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### ヘルスチェック

```bash
curl http://localhost:3000/health
# {"status":"healthy","timestamp":"...","version":"1.0.0"}
```

### E2Eテスト

```bash
cd docker
./test-kgpr-flow.sh
```

---

## 🔧 HTTPサーバー

YATA Global HTTPサーバーはスタンドアロンで起動できます。

### サーバーの起動

```bash
# npm経由
npx yata-global-server

# または直接
node packages/yata-global/dist/bin/yata-global-server.js
```

### 環境変数

| 変数 | デフォルト | 説明 |
|------|-----------|------|
| `PORT` | 3000 | リッスンポート |
| `HOST` | 0.0.0.0 | リッスンホスト |

### APIエンドポイント一覧

| メソッド | パス | 説明 |
|---------|------|------|
| GET | `/health` | ヘルスチェック |
| POST | `/auth/login` | ログイン |
| POST | `/auth/logout` | ログアウト |
| GET | `/api/v1/kgprs` | KGPR一覧 |
| POST | `/api/v1/kgprs` | KGPR作成 |
| GET | `/api/v1/kgprs/:id` | KGPR詳細 |
| POST | `/api/v1/kgprs/:id/review` | レビュー |
| POST | `/api/v1/kgprs/:id/merge` | マージ |
| GET | `/api/v1/patterns` | パターン一覧 |
| POST | `/api/v1/patterns` | パターン作成 |
| GET | `/api/v1/patterns/:id` | パターン詳細 |
| GET | `/api/v1/frameworks` | フレームワーク一覧 |
| GET | `/api/v1/frameworks/:id` | フレームワーク詳細 |

---

## 📱 イベント

YataGlobalは以下のイベントを発行します:

```typescript
// 認証イベント
yataGlobal.on('auth:login', (user) => {
  console.log('User logged in:', user.username);
});

yataGlobal.on('auth:logout', () => {
  console.log('User logged out');
});

// 同期イベント
yataGlobal.on('sync:start', () => {
  console.log('Sync started');
});

yataGlobal.on('sync:complete', (result) => {
  console.log('Sync completed:', result);
});

yataGlobal.on('sync:error', (error) => {
  console.error('Sync error:', error);
});

// 接続イベント
yataGlobal.on('connection:online', () => {
  console.log('Online');
});

yataGlobal.on('connection:offline', () => {
  console.log('Offline');
});
```

---

## 🔒 プライバシーフィルター

KGPRを作成する際、プライバシーフィルターが適用されます。

### プライバシーレベル

| レベル | 説明 |
|--------|------|
| `strict` | ファイルパス、行番号、機密メタデータを完全除去 |
| `moderate` | ファイルパスを相対化、行番号保持、機密メタデータ除去 |
| `none` | フィルタリングなし |

### 機密情報の検出

自動的にフィルタリングされる情報:
- API キー
- パスワード
- トークン
- 個人情報（メールアドレス等）
- 内部パス情報

---

## 📚 関連ドキュメント

- [YATA Local ユーザーガイド](./YATA-LOCAL-GUIDE.ja.md)
- [Docker環境 README](../docker/README.md)
- [API リファレンス](./API-REFERENCE.md)
- [MUSUBIX ユーザーガイド](./USER-GUIDE.ja.md)

---

## 📝 バージョン履歴

| バージョン | 主な変更 |
|-----------|---------|
| v2.4.1 | HTTPサーバー追加、Docker対応 |
| v1.7.0 | MergeEngine強化、コンフリクト解決 |
| v1.6.5 | KGPR、プライバシーフィルター追加 |
| v1.0.0 | 初期リリース |

---

**最終更新**: 2026-01-11
**パッケージ**: `@nahisaho/yata-global`
