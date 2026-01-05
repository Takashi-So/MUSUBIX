# Requirements: E2E Test Enhancement v1.5.2

> **EARS形式** に準拠した要件定義

## Overview

| 項目 | 内容 |
|-----|------|
| バージョン | 1.5.2 |
| 優先度 | P1 |
| 関連要件 | REQ-TEST-001, REQ-CLI-001 |
| 目標 | E2Eテストカバレッジ80%以上、シナリオテスト完備 |

---

## Requirements

### REQ-E2E-001: Test Helpers & Fixtures

**EARS Pattern**: Ubiquitous

**要件**:
THE E2E test framework SHALL provide reusable test helpers and fixtures for common testing scenarios.

**詳細**:
| 機能 | 説明 |
|-----|------|
| `TestProject` | テストプロジェクトのセットアップ・クリーンアップ |
| `TestFixtures` | 共通テストデータの提供 |
| `TestAssertions` | カスタムアサーション関数 |
| `CliRunner` | CLIコマンド実行ヘルパー |
| `MockServer` | MCPサーバーモック |

**受入基準**:
- [ ] TestProjectでプロジェクト作成・削除が可能
- [ ] TestFixturesで要件・設計・コードのサンプル提供
- [ ] CliRunnerで標準出力・エラー・終了コードの取得
- [ ] MockServerでMCPプロトコルをシミュレート

---

### REQ-E2E-002: SDD Workflow Scenario Tests

**EARS Pattern**: Event-driven

**要件**:
WHEN a user executes the complete SDD workflow (requirements → design → codegen → test), THE system SHALL produce traceable and valid outputs at each phase.

**シナリオ**:
```
1. musubix requirements analyze <input>
   → EARS形式の要件が生成される
2. musubix design generate <requirements>
   → C4モデルの設計が生成される
3. musubix codegen generate <design>
   → TypeScriptコードが生成される
4. musubix test generate <code>
   → Vitestテストが生成される
5. musubix trace matrix
   → 全アーティファクトがトレース可能
```

**受入基準**:
- [ ] 完全なSDDワークフローが自動実行可能
- [ ] 各フェーズの出力が検証可能
- [ ] トレーサビリティマトリクスが生成される

---

### REQ-E2E-003: Learning System E2E Tests

**EARS Pattern**: State-driven

**要件**:
WHILE the learning system is active, THE system SHALL correctly process feedback, extract patterns, and provide recommendations.

**シナリオ**:
```
1. musubix learn feedback <id> --result accept
   → フィードバックが記録される
2. musubix learn patterns
   → 学習済みパターンが表示される
3. musubix learn recommend
   → コンテキストベースの推奨が提供される
4. musubix learn export --output patterns.json
   → パターンがエクスポートされる
5. musubix learn import patterns.json
   → パターンがインポートされる
```

**受入基準**:
- [ ] フィードバック→パターン抽出のフローが動作
- [ ] エクスポート/インポートの往復が可能
- [ ] 推奨機能が適切な結果を返す

---

### REQ-E2E-004: MCP Server Integration Tests

**EARS Pattern**: Event-driven

**要件**:
WHEN MCP tools are invoked through the server, THE system SHALL return correctly formatted responses conforming to the MCP protocol.

**テスト対象ツール**:
| ツール | テスト内容 |
|-------|----------|
| `sdd_create_requirements` | 要件作成の成功・失敗 |
| `sdd_validate_requirements` | 検証結果のフォーマット |
| `pattern_extract` | パターン抽出結果 |
| `ontology_query` | クエリ結果 |
| `consistency_validate` | 整合性検証結果 |

**受入基準**:
- [ ] 全19ツールの正常系テストが存在
- [ ] エラーハンドリングのテストが存在
- [ ] MCPプロトコル準拠の検証

---

### REQ-E2E-005: Performance E2E Tests

**EARS Pattern**: Ubiquitous

**要件**:
THE performance test suite SHALL verify that CLI startup time is under 500ms and memory usage is under 512MB.

**テスト内容**:
| メトリクス | 閾値 |
|----------|------|
| CLI起動時間 | < 500ms |
| メモリ使用量 | < 512MB |
| 要件分析時間 | < 2s (100要件) |
| パターン検索時間 | < 100ms |

**受入基準**:
- [ ] パフォーマンステストが自動実行される
- [ ] 閾値超過時にテスト失敗
- [ ] CI/CDでの計測が可能

---

### REQ-E2E-006: Error Handling & Recovery Tests

**EARS Pattern**: Unwanted

**要件**:
THE system SHALL NOT crash or produce corrupted state when encountering invalid inputs, missing files, or network failures.

**テストケース**:
| シナリオ | 期待動作 |
|---------|---------|
| 存在しないファイル指定 | 適切なエラーメッセージ |
| 不正なEARS構文 | 検証エラーの詳細表示 |
| 破損したJSONファイル | パースエラーとリカバリ |
| MCPサーバー接続失敗 | タイムアウトと再試行 |

**受入基準**:
- [ ] 全エラーシナリオでクラッシュしない
- [ ] ユーザーフレンドリーなエラーメッセージ
- [ ] リカバリ可能な状態を維持

---

### REQ-E2E-007: REPL Interactive Tests

**EARS Pattern**: Event-driven

**要件**:
WHEN a user interacts with the REPL shell, THE system SHALL provide command completion, history navigation, and session variable support.

**テスト内容**:
| 機能 | テスト |
|-----|-------|
| TAB補完 | コマンド/オプション補完 |
| 履歴 | ↑/↓ナビゲーション |
| 変数 | set/get/expand |
| 出力フォーマット | JSON/Table/YAML |

**受入基準**:
- [ ] REPL機能の自動テストが可能
- [ ] インタラクティブ入力のシミュレーション
- [ ] 出力フォーマットの検証

---

## Traceability

| 要件ID | 関連コンポーネント | テストファイル |
|--------|------------------|--------------|
| REQ-E2E-001 | TestHelpers | e2e/helpers/ |
| REQ-E2E-002 | SDD Workflow | e2e/sdd-workflow.e2e.test.ts |
| REQ-E2E-003 | Learning System | e2e/learning.e2e.test.ts |
| REQ-E2E-004 | MCP Server | e2e/mcp-server.e2e.test.ts |
| REQ-E2E-005 | Performance | e2e/performance.e2e.test.ts |
| REQ-E2E-006 | Error Handling | e2e/error-handling.e2e.test.ts |
| REQ-E2E-007 | REPL | e2e/repl.e2e.test.ts |

---

## Test Coverage Goals

| カテゴリ | 現在 | 目標 |
|---------|------|------|
| Lines | 25% | 80% |
| Branches | 20% | 75% |
| Functions | 30% | 85% |
| E2Eシナリオ | 2 | 10+ |

---

**作成日**: 2026-01-06
**最終更新**: 2026-01-06
**ステータス**: Draft
