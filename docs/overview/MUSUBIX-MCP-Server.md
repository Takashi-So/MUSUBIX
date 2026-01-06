# MUSUBIX MCP Server パッケージ

**パッケージ名**: `@nahisaho/musubix-mcp-server`  
**バージョン**: 1.7.5  
**最終更新**: 2026-01-06

---

## 1. 概要

`@nahisaho/musubix-mcp-server` は、Model Context Protocol（MCP）を実装したサーバーです。AIコーディングエージェント（Claude Code、GitHub Copilot、Cursor等）とMUSUBIXシステムを連携します。

### 1.1 主要機能

| 機能 | 説明 |
|------|------|
| **MCPプロトコル** | Model Context Protocol 完全実装 |
| **マルチプラットフォーム** | 主要AIエージェント対応 |
| **ツール提供** | 24+ MCPツール |
| **プロンプト提供** | SDD方法論プロンプト |
| **リソース提供** | 憲法、パターン等のリソース |

### 1.2 対応プラットフォーム

| プラットフォーム | 対応状況 |
|----------------|---------|
| Claude Code | ✅ 完全対応 |
| GitHub Copilot | ✅ 完全対応 |
| Cursor | ✅ 完全対応 |
| Gemini CLI | ✅ 完全対応 |
| Codex CLI | ✅ 対応 |
| Qwen Code | ✅ 対応 |
| Windsurf | ✅ 対応 |

---

## 2. アーキテクチャ

### 2.1 モジュール構成

```
packages/mcp-server/src/
├── server.ts            # MCPサーバー実装
├── types.ts             # 型定義
├── index.ts             # エントリポイント
├── tools/               # MCPツール
│   ├── sdd-tools.ts         # SDDツール
│   ├── symbolic-tools.ts    # シンボリックツール
│   ├── pattern-tools.ts     # パターンツール
│   ├── ontology-tools.ts    # オントロジーツール
│   ├── kgpr-tools.ts        # KGPRツール
│   ├── yata-tools.ts        # YATAツール
│   └── formal-verify-tools.ts # 形式検証ツール
├── prompts/             # MCPプロンプト
│   └── sdd-prompts.ts
├── resources/           # MCPリソース
│   └── sdd-resources.ts
└── platform/            # プラットフォームアダプタ
    └── adapter.ts
```

### 2.2 サーバーアーキテクチャ

```
┌─────────────────────────────────────────────────────────────┐
│                    AI Agent (Claude, Copilot, etc.)          │
└──────────────────────┬──────────────────────────────────────┘
                       │ MCP Protocol (JSON-RPC)
                       │
┌──────────────────────▼──────────────────────────────────────┐
│                    MUSUBIX MCP Server                        │
│  ┌─────────────────────────────────────────────────────┐    │
│  │                   Router                             │    │
│  └──────┬────────────┬────────────┬────────────────────┘    │
│         │            │            │                          │
│  ┌──────▼────┐ ┌─────▼─────┐ ┌───▼────┐                    │
│  │   Tools   │ │  Prompts  │ │Resources│                    │
│  └──────┬────┘ └─────┬─────┘ └───┬────┘                    │
│         │            │           │                           │
└─────────┼────────────┼───────────┼───────────────────────────┘
          │            │           │
┌─────────▼────────────▼───────────▼───────────────────────────┐
│                    MUSUBIX Core                               │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────────────┐    │
│  │Symbolic │ │ CodeGen │ │ Design  │ │   Learning      │    │
│  └─────────┘ └─────────┘ └─────────┘ └─────────────────┘    │
└──────────────────────────────────────────────────────────────┘
```

---

## 3. 起動方法

### 3.1 コマンドライン

```bash
# 標準入出力（stdio）トランスポート
npx @nahisaho/musubix-mcp-server
npx musubix-mcp --transport stdio

# HTTPトランスポート
npx musubix-mcp --transport http --port 3000
```

### 3.2 プログラマティック

```typescript
import { MuSubixMCPServer } from '@nahisaho/musubix-mcp-server';

const server = new MuSubixMCPServer({
  name: 'musubix',
  version: '1.7.5',
});

await server.start();
```

### 3.3 Claude Code設定

`claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "musubix": {
      "command": "npx",
      "args": ["@nahisaho/musubix-mcp-server"],
      "env": {}
    }
  }
}
```

### 3.4 VS Code設定（GitHub Copilot）

`.vscode/settings.json`:

```json
{
  "mcp.servers": {
    "musubix": {
      "command": "npx",
      "args": ["@nahisaho/musubix-mcp-server"]
    }
  }
}
```

---

## 4. MCPツール一覧

### 4.1 SDD基本ツール（9ツール）

| ツール名 | 説明 |
|---------|------|
| `sdd_create_requirements` | EARS形式の要件ドキュメント作成 |
| `sdd_validate_requirements` | 要件のEARS検証・憲法準拠チェック |
| `sdd_create_design` | C4モデル設計ドキュメント作成 |
| `sdd_validate_design` | 設計の要件トレーサビリティ検証 |
| `sdd_create_tasks` | 設計から実装タスク生成 |
| `sdd_query_knowledge` | YATA知識グラフへのクエリ |
| `sdd_update_knowledge` | 知識グラフの更新 |
| `sdd_validate_constitution` | 9憲法条項への準拠検証 |
| `sdd_validate_traceability` | 要件↔設計↔タスクのトレーサビリティ検証 |

### 4.2 シンボリックツール（5ツール）

| ツール名 | 説明 |
|---------|------|
| `symbolic_filter_code` | LLM出力のセマンティック検証 |
| `symbolic_detect_hallucination` | ハルシネーション検出 |
| `symbolic_check_constitution` | 憲法ルールチェック |
| `symbolic_estimate_confidence` | 信頼度推定 |
| `symbolic_route_decision` | 信頼度ルーティング |

### 4.3 パターン統合ツール（7ツール）

| ツール名 | 説明 |
|---------|------|
| `pattern_extract` | コードからパターンを抽出 |
| `pattern_compress` | パターンの抽象化・圧縮 |
| `pattern_store` | パターンライブラリへの保存 |
| `pattern_query` | パターンの検索・取得 |
| `pattern_consolidate` | 類似パターンの統合 |
| `ontology_query` | オントロジーグラフへのクエリ |
| `ontology_infer` | オントロジーによる推論実行 |

### 4.4 オントロジー検証ツール（3ツール）

| ツール名 | 説明 |
|---------|------|
| `consistency_validate` | 知識グラフの整合性検証 |
| `validate_triple` | 単一トリプルの事前検証 |
| `check_circular` | 循環依存の検出 |

### 4.5 KGPRツール（5ツール）

| ツール名 | 説明 |
|---------|------|
| `kgpr_create` | KGPR作成（ローカルKGからドラフト作成） |
| `kgpr_diff` | 差分プレビュー |
| `kgpr_list` | KGPR一覧表示 |
| `kgpr_submit` | KGPR送信（レビュー用） |
| `kgpr_review` | KGPRレビュー |

### 4.6 形式検証ツール（6ツール）

| ツール名 | 説明 |
|---------|------|
| `verify_precondition` | 事前条件検証（Z3） |
| `verify_postcondition` | 事後条件検証（Hoare） |
| `ears_to_smt` | EARS→SMT-LIB2変換 |
| `trace_add_link` | トレースリンク追加 |
| `trace_query` | トレースクエリ |
| `trace_impact` | 影響分析 |

---

## 5. ツール詳細

### 5.1 sdd_create_requirements

EARS形式の要件ドキュメントを作成します。

**入力スキーマ:**

```json
{
  "type": "object",
  "properties": {
    "description": {
      "type": "string",
      "description": "機能の自然言語説明"
    },
    "domain": {
      "type": "string",
      "description": "ドメイン（ecommerce, healthcare等）"
    },
    "priority": {
      "type": "string",
      "enum": ["P0", "P1", "P2"],
      "description": "優先度"
    }
  },
  "required": ["description"]
}
```

**出力例:**

```json
{
  "requirements": [
    {
      "id": "REQ-001",
      "pattern": "event-driven",
      "text": "WHEN a user submits login form, THE system SHALL validate credentials within 2 seconds.",
      "priority": "P0"
    }
  ],
  "traceability": {
    "domain": "authentication",
    "relatedRequirements": ["REQ-SEC-001"]
  }
}
```

### 5.2 sdd_validate_constitution

9条憲法への準拠を検証します。

**入力スキーマ:**

```json
{
  "type": "object",
  "properties": {
    "code": {
      "type": "string",
      "description": "検証対象コード"
    },
    "design": {
      "type": "string",
      "description": "設計ドキュメント"
    },
    "requirements": {
      "type": "string",
      "description": "要件ドキュメント"
    }
  }
}
```

**出力例:**

```json
{
  "compliant": false,
  "violations": [
    {
      "article": "III",
      "name": "Test-First",
      "message": "No tests found for UserService",
      "severity": "error"
    }
  ],
  "suggestions": [
    "Add unit tests for UserService before implementing"
  ]
}
```

### 5.3 verify_precondition

Z3を使用して事前条件を検証します。

**入力スキーマ:**

```json
{
  "type": "object",
  "properties": {
    "condition": {
      "type": "object",
      "properties": {
        "expression": { "type": "string" },
        "format": { "type": "string", "enum": ["javascript", "smt", "natural"] }
      }
    },
    "variables": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "name": { "type": "string" },
          "type": { "type": "string", "enum": ["Int", "Real", "Bool", "String"] }
        }
      }
    }
  }
}
```

**出力例:**

```json
{
  "status": "valid",
  "duration": 45,
  "details": {
    "smtLib2": "(declare-const amount Int)...",
    "z3Result": "unsat"
  }
}
```

---

## 6. MCPプロンプト

### 6.1 利用可能なプロンプト

| プロンプト名 | 説明 |
|-------------|------|
| `sdd_requirements_analysis` | 機能説明からEARS形式要件を生成 |
| `sdd_requirements_review` | 要件の完全性・憲法準拠レビュー |
| `sdd_design_generation` | 要件からC4モデル設計を生成 |

### 6.2 sdd_requirements_analysis

**引数:**

```json
{
  "feature_description": "ユーザーログイン機能",
  "domain": "authentication",
  "constraints": ["2秒以内のレスポンス", "MFA対応"]
}
```

**生成されるプロンプト:**

```
あなたはSDD方法論に基づく要件アナリストです。
以下の機能説明をEARS形式の要件に変換してください。

## 機能説明
ユーザーログイン機能

## ドメイン
authentication

## 制約
- 2秒以内のレスポンス
- MFA対応

## EARS パターン
- Ubiquitous: THE [system] SHALL [requirement]
- Event-driven: WHEN [event], THE [system] SHALL [response]
...
```

---

## 7. MCPリソース

### 7.1 利用可能なリソース

| リソースURI | 説明 |
|------------|------|
| `musubix://constitution` | 9条憲法の全文 |
| `musubix://ears-patterns` | EARSパターンガイド |
| `musubix://c4-patterns` | C4モデルパターン |
| `musubix://design-patterns` | 設計パターンカタログ |
| `musubix://best-practices` | ベストプラクティス |

### 7.2 リソースアクセス例

```typescript
// MCPクライアントから
const constitution = await client.readResource('musubix://constitution');
console.log(constitution.contents);
```

---

## 8. プラットフォームアダプタ

### 8.1 概要

各AIプラットフォームの固有機能に対応するアダプタを提供します。

### 8.2 対応機能

| 機能 | Claude | Copilot | Cursor |
|------|--------|---------|--------|
| ツール呼び出し | ✅ | ✅ | ✅ |
| プロンプト | ✅ | ✅ | ✅ |
| リソース | ✅ | ✅ | ✅ |
| ストリーミング | ✅ | ✅ | ✅ |
| 画像入力 | ✅ | ❌ | ❌ |

### 8.3 アダプタ使用例

```typescript
import { PlatformAdapter } from '@nahisaho/musubix-mcp-server';

const adapter = new PlatformAdapter('claude');
const capabilities = adapter.getCapabilities();

if (capabilities.supportsStreaming) {
  // ストリーミング対応処理
}
```

---

## 9. 設定

### 9.1 環境変数

| 変数名 | 説明 | デフォルト |
|--------|------|-----------|
| `MUSUBIX_LOG_LEVEL` | ログレベル | `info` |
| `MUSUBIX_YATA_PATH` | YATAデータパス | `~/.musubix/yata` |
| `MUSUBIX_CACHE_SIZE` | キャッシュサイズ | `1000` |

### 9.2 設定ファイル

`musubix.config.json`:

```json
{
  "server": {
    "transport": "stdio",
    "port": 3000
  },
  "tools": {
    "enabled": ["sdd", "symbolic", "pattern", "formal-verify"],
    "disabled": []
  },
  "logging": {
    "level": "info",
    "file": "./musubix.log"
  }
}
```

---

## 10. エラーハンドリング

### 10.1 エラーコード

| コード | 説明 |
|--------|------|
| `-32700` | パースエラー |
| `-32600` | 無効なリクエスト |
| `-32601` | メソッド未発見 |
| `-32602` | 無効なパラメータ |
| `-32603` | 内部エラー |
| `-32000` | サーバーエラー |

### 10.2 エラーレスポンス例

```json
{
  "jsonrpc": "2.0",
  "error": {
    "code": -32602,
    "message": "Invalid params: 'condition' is required",
    "data": {
      "param": "condition",
      "expected": "object"
    }
  },
  "id": 1
}
```

---

## 11. 関連ドキュメント

| ドキュメント | 説明 |
|-------------|------|
| [MUSUBIX-Overview.md](MUSUBIX-Overview.md) | 全体概要 |
| [MUSUBIX-Core.md](MUSUBIX-Core.md) | Coreパッケージ |
| [MUSUBIX-FormalVerify.md](MUSUBIX-FormalVerify.md) | 形式検証 |
| [API-REFERENCE.md](API-REFERENCE.md) | APIリファレンス |

---

**© 2026 MUSUBIX Project**
