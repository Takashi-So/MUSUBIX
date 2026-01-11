# MUSUBIX Docker Environment

Docker環境でMUSUBIXとYATA Globalを実行するための設定です。

## 構成

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

## クイックスタート

### 1. ビルド & 起動

```bash
cd docker
docker compose up -d
```

### 2. コンテナに接続

```bash
# musubix開発環境に入る
docker compose exec musubix bash

# yata-globalのログを確認
docker compose logs -f yata-global
```

### 3. 動作確認

```bash
# ヘルスチェック
curl http://localhost:3000/health

# E2Eテスト
./test-kgpr-flow.sh
```

## KGPR フロー

### 1. KGPR作成

```bash
curl -X POST http://localhost:3000/api/v1/kgprs \
  -H "Content-Type: application/json" \
  -d '{
    "title": "My Pattern",
    "description": "Learned pattern from my project",
    "sourceNamespace": "my.namespace",
    "labels": ["pattern"],
    "diff": {
      "entities": {
        "added": [{"changeType": "add", "localId": "e1", "name": "MyClass", "entityType": "class", "namespace": "my.namespace"}],
        "updated": [],
        "deleted": []
      },
      "relationships": {"added": [], "updated": [], "deleted": []},
      "stats": {"entitiesAdded": 1, "entitiesUpdated": 0, "entitiesDeleted": 0, "relationshipsAdded": 0, "relationshipsUpdated": 0, "relationshipsDeleted": 0, "totalChanges": 1}
    }
  }'
```

### 2. レビュー & 承認

```bash
curl -X POST http://localhost:3000/api/v1/kgprs/{KGPR_ID}/review \
  -H "Content-Type: application/json" \
  -d '{"decision": "approve", "comment": "LGTM!"}'
```

### 3. マージ

```bash
curl -X POST http://localhost:3000/api/v1/kgprs/{KGPR_ID}/merge \
  -H "Content-Type: application/json"
```

## API エンドポイント

| メソッド | パス | 説明 |
|---------|------|------|
| GET | `/health` | ヘルスチェック |
| POST | `/auth/login` | ログイン |
| GET | `/api/v1/kgprs` | KGPR一覧 |
| POST | `/api/v1/kgprs` | KGPR作成 |
| GET | `/api/v1/kgprs/{id}` | KGPR詳細 |
| POST | `/api/v1/kgprs/{id}/review` | KGPRレビュー |
| POST | `/api/v1/kgprs/{id}/merge` | KGPRマージ |
| GET | `/api/v1/patterns` | パターン一覧 |
| POST | `/api/v1/patterns` | パターン作成 |
| GET | `/api/v1/frameworks` | フレームワーク一覧 |

## 環境変数

### yata-global

| 変数 | デフォルト | 説明 |
|-----|----------|------|
| `PORT` | `3000` | サーバーポート |
| `HOST` | `0.0.0.0` | リッスンアドレス |
| `NODE_ENV` | `production` | 環境 |

### musubix-dev

| 変数 | デフォルト | 説明 |
|-----|----------|------|
| `YATA_LOCAL_DB` | `/root/.yata/local/knowledge.db` | YATAローカルDBパス |
| `YATA_GLOBAL_ENDPOINT` | `http://yata-global:3000` | YATA Globalエンドポイント |
| `NODE_ENV` | `development` | 環境 |

## ボリューム

| ボリューム | マウント先 | 説明 |
|-----------|-----------|------|
| `yata-global-data` | `/data` | YATA Globalデータ |
| `musubix-yata-local` | `/root/.yata` | YATAローカルDB |
| `musubix-projects` | `/workspace/projects` | プロジェクトワークスペース |

## トラブルシューティング

### ヘルスチェックが失敗する

IPv6の問題の可能性があります。docker-compose.ymlで`127.0.0.1`を明示的に使用しています。

```yaml
healthcheck:
  test: ["CMD", "wget", "-q", "--spider", "http://127.0.0.1:3000/health"]
```

### コンテナが起動しない

ログを確認してください：

```bash
docker compose logs yata-global
docker compose logs musubix
```

### ポートが使用中

```bash
# 3000ポートを使用しているプロセスを確認
lsof -i :3000
```

## クリーンアップ

```bash
# コンテナを停止
docker compose down

# ボリュームも削除
docker compose down -v

# イメージも削除
docker compose down --rmi all
```
