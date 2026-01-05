# MUSUBIX Pattern Library Learning MCP 要件定義書

**文書ID**: REQ-PATTERN-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-05  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**ロードマップ参照**: Phase 3 - 学習・推論拡張

---

## 1. 概要

### 1.1 目的

DreamCoder型のWake-Sleep学習アーキテクチャを採用したPattern Library Learning MCPサーバーを開発し、コードベースから再利用可能な抽象パターンを自動抽出・管理する機能を実現する。

### 1.2 スコープ

- パターン抽出（E-graph/Tree-sitter）
- 類似度計算（Code2Vec埋め込み）
- クラスタリング（HDBSCAN）
- パターンライブラリ管理
- Wake-Sleep学習サイクル統合

### 1.3 技術スタック

| 技術 | 用途 | 備考 |
|------|------|------|
| Tree-sitter (tree-sitter-typescript) | AST生成・パターン抽出 | Node.jsバインディング使用 |
| カスタム抽象化エンジン | パターン抽象化 | Anti-unification実装 |
| ml-distance | 類似度計算 | コサイン類似度 |
| density-clustering | クラスタリング | DBSCAN/HDBSCAN |
| MCP Server SDK | サーバー実装 | @modelcontextprotocol/sdk |

---

## 2. 機能要件

### REQ-PATTERN-001-F001: パターン抽出

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーがコードベースのパターン抽出を要求した時,  
THE システム SHALL コードベースをパースしてAST（抽象構文木）を生成し,  
AND THE システム SHALL 繰り返し出現するコード構造を識別し,  
AND THE システム SHALL 最小出現回数（デフォルト3回）以上のパターンを抽出し,  
AND THE システム SHALL 各パターンに一意のIDと出現頻度を付与する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] Tree-sitterによるAST生成が動作する
- [ ] 繰り返しパターンが正しく識別される
- [ ] パターンIDと頻度が付与される
- [ ] 最小出現回数のフィルタリングが機能する

**トレーサビリティ**: DES-PATTERN-001, TSK-PATTERN-001

---

### REQ-PATTERN-001-F002: パターン抽象化

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 類似コードスニペットの集合が与えられた時,  
THE システム SHALL 共通構造を抽出して抽象化を生成し,  
AND THE システム SHALL 可変部分をパラメータとして識別し,  
AND THE システム SHALL 抽象化の信頼度スコアを計算し,  
AND THE システム SHALL 抽象化テンプレートを生成する。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] 共通構造が正しく抽出される
- [ ] パラメータが適切に識別される
- [ ] 信頼度スコアが0.0〜1.0の範囲で計算される
- [ ] テンプレートが再利用可能な形式で生成される

**トレーサビリティ**: DES-PATTERN-002, TSK-PATTERN-002

---

### REQ-PATTERN-001-F003: 類似度計算

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 2つ以上のコードスニペットが比較対象として与えられた時,  
THE システム SHALL Code2Vec埋め込みを生成し,  
AND THE システム SHALL コサイン類似度を計算し,  
AND THE システム SHALL 類似度スコア（0.0〜1.0）を返却する。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] Code2Vec埋め込みが生成される
- [ ] コサイン類似度が正しく計算される
- [ ] 同一コードの類似度が1.0に近い
- [ ] 無関係なコードの類似度が0.0に近い

**トレーサビリティ**: DES-PATTERN-003, TSK-PATTERN-003

---

### REQ-PATTERN-001-F004: パターンクラスタリング

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN パターン抽出が完了した時,  
THE システム SHALL HDBSCANアルゴリズムでパターンをクラスタリングし,  
AND THE システム SHALL 各クラスタに代表パターンを選定し,  
AND THE システム SHALL クラスタ間の関係を識別する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] HDBSCANクラスタリングが動作する
- [ ] 代表パターンが選定される
- [ ] クラスタ階層が生成される

**トレーサビリティ**: DES-PATTERN-004, TSK-PATTERN-004

---

### REQ-PATTERN-001-F005: パターンライブラリ管理

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL パターンライブラリをJSON形式で永続化し,  
AND THE システム SHALL パターンの追加・更新・削除をサポートし,  
AND THE システム SHALL パターンのバージョン管理を行い,  
AND THE システム SHALL パターンライブラリのインポート・エクスポートをサポートする。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] パターンがJSON形式で保存される
- [ ] CRUD操作が正しく動作する
- [ ] バージョン履歴が記録される
- [ ] インポート・エクスポートが機能する

**トレーサビリティ**: DES-PATTERN-005, TSK-PATTERN-005

---

### REQ-PATTERN-001-F006: パターンライブラリ圧縮

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN パターンライブラリの最適化が要求された時,  
THE システム SHALL 冗長なパターンを検出し,  
AND THE システム SHALL 類似パターンをマージし,  
AND THE システム SHALL 圧縮結果のサマリーを生成する。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] 冗長パターンが検出される
- [ ] パターンマージが正しく動作する
- [ ] 圧縮率が計算される

**トレーサビリティ**: DES-PATTERN-006, TSK-PATTERN-006

---

### REQ-PATTERN-001-F007: プライバシー保護

**種別**: UNWANTED  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL NOT 抽出したパターンを外部サーバーに送信し,  
AND THE システム SHALL NOT 機密コード（APIキー、パスワード等）をパターンライブラリに含め,  
AND THE システム SHALL NOT ユーザーの同意なくパターンを共有する。

**検証方法**: セキュリティレビュー、コードレビュー  
**受入基準**:
- [ ] パターンがローカルストレージのみに保存される
- [ ] 機密情報フィルタリングが実装されている
- [ ] 外部通信がない

**トレーサビリティ**: DES-PATTERN-007, TSK-PATTERN-007

---

## 3. MCPツール仕様

### 3.1 extract_patterns

```typescript
{
  "name": "extract_patterns",
  "description": "コードベースから再利用可能なパターンを抽出",
  "inputSchema": {
    "type": "object",
    "properties": {
      "codebase_path": { "type": "string", "description": "コードベースのパス" },
      "min_occurrences": { "type": "number", "default": 3, "description": "最小出現回数" },
      "language": { "type": "string", "description": "プログラミング言語" }
    },
    "required": ["codebase_path"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "patterns": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "id": { "type": "string" },
            "abstraction": { "type": "string" },
            "instances": { "type": "array" },
            "frequency": { "type": "number" }
          }
        }
      }
    }
  }
}
```

### 3.2 suggest_abstraction

```typescript
{
  "name": "suggest_abstraction",
  "description": "類似コードから抽象化を提案",
  "inputSchema": {
    "type": "object",
    "properties": {
      "code_snippets": { "type": "array", "items": { "type": "string" } }
    },
    "required": ["code_snippets"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "abstraction": { "type": "string" },
      "parameters": { "type": "array" },
      "confidence": { "type": "number" }
    }
  }
}
```

### 3.3 compress_library

```typescript
{
  "name": "compress_library",
  "description": "パターンライブラリを圧縮・最適化",
  "inputSchema": {
    "type": "object",
    "properties": {
      "library_path": { "type": "string" }
    },
    "required": ["library_path"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "optimized_path": { "type": "string" },
      "removed_redundant": { "type": "number" },
      "merged_count": { "type": "number" },
      "compression_ratio": { "type": "number" }
    }
  }
}
```

---

## 4. 非機能要件

### REQ-PATTERN-001-NF001: パフォーマンス

**要件**:  
THE システム SHALL 10,000行のコードベースを60秒以内にパターン抽出し,  
AND THE システム SHALL 類似度計算を100ms以内に完了する。

### REQ-PATTERN-001-NF002: スケーラビリティ

**要件**:  
THE システム SHALL 100,000行以上のコードベースに対応し,  
AND THE システム SHALL 10,000パターン以上のライブラリを管理可能にする。

### REQ-PATTERN-001-NF003: 拡張性

**要件**:  
THE システム SHALL 新しいプログラミング言語のサポートを追加可能にし,  
AND THE システム SHALL カスタムパターンマッチャーの登録をサポートする。

---

## 5. 制約事項

- Tree-sitter対応言語のみサポート（TypeScript, JavaScript, Python, Go, Rust等）
- Code2Vec埋め込みはオフラインモデルを使用
- パターンライブラリはローカルストレージのみ（クラウド同期なし）

---

## 6. 依存関係

| 依存先 | 種別 | 説明 |
|-------|------|------|
| REQ-LEARN-001 | 機能依存 | 既存の自己学習機能との連携 |
| REQ-WAKE-001 | 機能依存 | Wake-Sleep学習サイクルとの統合 |
| tree-sitter | 外部ライブラリ | AST生成 |
| hdbscan | 外部ライブラリ | クラスタリング |

---

## 7. 用語定義

| 用語 | 定義 |
|------|------|
| パターン | 繰り返し出現する再利用可能なコード構造 |
| 抽象化 | 具体的なコードから共通構造を抽出したテンプレート |
| E-graph | 等価クラスを表現するデータ構造 |
| Code2Vec | コードの分散表現を生成するモデル |
| HDBSCAN | 階層的密度ベースクラスタリングアルゴリズム |

---

**文書履歴**:
| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-05 | 初版作成 | Claude |
