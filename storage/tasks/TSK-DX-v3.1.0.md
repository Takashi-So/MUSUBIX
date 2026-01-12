# タスク分解書: MUSUBIX v3.1.0 開発者体験強化

**Document ID**: TSK-DX-v3.1.0  
**Version**: 1.0.0  
**Created**: 2026-01-13  
**Author**: AI Agent  
**Status**: Draft  
**Traces To**: DES-DX-v3.1.0

---

## 1. 概要

### 1.1 タスク構成

| モジュール | タスク数 | 見積もり工数 |
|-----------|---------|-------------|
| Watch Module | 8 | 16h |
| Spaces Module | 6 | 12h |
| CodeQL Module | 6 | 10h |
| Team Module | 8 | 14h |
| 統合・テスト | 4 | 8h |
| **合計** | **32** | **60h** |

### 1.2 優先度・依存関係

```
Phase A: 基盤実装（並行可能）
├── TSK-WATCH-001〜004 (Watch基盤)
├── TSK-CODEQL-001〜003 (CodeQL基盤)
└── TSK-TEAM-001〜004 (Team基盤)

Phase B: 機能実装（Phase A完了後）
├── TSK-WATCH-005〜008 (Watch Runner/MCP)
├── TSK-SPACES-001〜006 (Spaces全体) ← Knowledge Store依存
├── TSK-CODEQL-004〜006 (CodeQL統合/MCP)
└── TSK-TEAM-005〜008 (Team履歴/MCP)

Phase C: 統合・リリース
└── TSK-INT-001〜004 (統合テスト/リリース)
```

---

## 2. Watch Moduleタスク

### TSK-WATCH-001: FileWatcher実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-001 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | なし |

**実装内容**:
1. `packages/core/src/watch/file-watcher.ts` 作成
2. chokidarを使用したファイル監視
3. WatchConfig, FileChangeEvent型定義
4. start(), stop(), on()メソッド実装
5. .gitignore/.musubixignore読み込み

**受け入れ条件**:
- [ ] ファイル変更検出が動作する
- [ ] 除外パターンが適用される
- [ ] エラーハンドリングが実装されている

---

### TSK-WATCH-002: TaskScheduler実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-007 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-WATCH-001 |

**実装内容**:
1. `packages/core/src/watch/task-scheduler.ts` 作成
2. デバウンス機能（300msデフォルト）
3. タスクキュー管理
4. TaskRunner抽象インターフェース

**受け入れ条件**:
- [ ] 連続変更がデバウンスされる
- [ ] タスクが順次実行される
- [ ] キャンセル機能が動作する

---

### TSK-WATCH-003: ResultReporter実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-006 |
| 優先度 | P0 |
| 見積もり | 1.5h |
| 担当 | - |
| 依存 | TSK-WATCH-002 |

**実装内容**:
1. `packages/core/src/watch/result-reporter.ts` 作成
2. ターミナル出力（カラー対応）
3. JSON形式エクスポート
4. WatchReportサマリー生成

**受け入れ条件**:
- [ ] 結果がターミナルに表示される
- [ ] JSONファイルが出力される
- [ ] サマリー情報が正確

---

### TSK-WATCH-004: LintRunner実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-002 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-WATCH-002 |

**実装内容**:
1. `packages/core/src/watch/runners/lint-runner.ts` 作成
2. ESLint API統合
3. Pylint統合（Python検出時）
4. 結果をTaskResult形式に変換

**受け入れ条件**:
- [ ] ESLintが実行される
- [ ] エラー/警告が正しく分類される
- [ ] 増分Lint（変更ファイルのみ）が動作する

---

### TSK-WATCH-005: TestRunner実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-003 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-WATCH-002 |

**実装内容**:
1. `packages/core/src/watch/runners/test-runner.ts` 作成
2. Vitest API統合
3. 関連テスト検出ロジック
4. テスト結果パース

**受け入れ条件**:
- [ ] 変更ファイルに関連するテストが実行される
- [ ] pass/fail/skip数が正確
- [ ] エラー詳細が含まれる

---

### TSK-WATCH-006: SecurityRunner実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-005 |
| 優先度 | P1 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-WATCH-002 |

**実装内容**:
1. `packages/core/src/watch/runners/security-runner.ts` 作成
2. Security Extractor統合
3. 変更ファイルのみスキャン
4. 脆弱性結果をTaskResult形式に変換

**受け入れ条件**:
- [ ] セキュリティスキャンが実行される
- [ ] 7言語対応が維持される
- [ ] 検出結果にCWE情報が含まれる

---

### TSK-WATCH-007: Watch CLI実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-001〜008 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-WATCH-001〜006 |

**実装内容**:
1. `packages/core/src/cli/commands/watch.ts` 作成
2. `musubix watch`コマンド実装
3. オプション（--lint, --test, --security, --debounce）
4. Ctrl+Cでの graceful shutdown

**受け入れ条件**:
- [ ] `musubix watch`が動作する
- [ ] オプションが正しく適用される
- [ ] 停止時にリソースが解放される

---

### TSK-WATCH-008: Watch MCPツール実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-WATCH-001〜008 |
| 優先度 | P0 |
| 見積もり | 2.5h |
| 担当 | - |
| 依存 | TSK-WATCH-007 |

**実装内容**:
1. `packages/mcp-server/src/tools/watch-tools.ts` 作成
2. watch_start, watch_stop, watch_status, watch_results実装
3. MCPサーバー登録

**受け入れ条件**:
- [ ] 4つのMCPツールが動作する
- [ ] Copilot Chatから操作可能
- [ ] エラーが適切にハンドリングされる

---

## 3. Spaces Moduleタスク

### TSK-SPACES-001: SpacesClient実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-SPACES-001 |
| 優先度 | P0 |
| 見積もり | 3h |
| 担当 | - |
| 依存 | なし |

**実装内容**:
1. `packages/knowledge/src/spaces/spaces-client.ts` 作成
2. GitHub Copilot Spaces API統合
3. OAuth認証フロー
4. CRUD操作実装

**受け入れ条件**:
- [ ] Spacesとの接続が確立できる
- [ ] エンティティのCRUDが動作する
- [ ] 認証トークンが安全に保存される

---

### TSK-SPACES-002: EntityMapper実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-SPACES-005 |
| 優先度 | P0 |
| 見積もり | 1.5h |
| 担当 | - |
| 依存 | TSK-SPACES-001 |

**実装内容**:
1. `packages/knowledge/src/spaces/entity-mapper.ts` 作成
2. Knowledge Store Entity → Spaces Entity変換
3. Relation変換
4. メタデータマッピング

**受け入れ条件**:
- [ ] 双方向変換が正確
- [ ] 全エンティティタイプ対応
- [ ] メタデータが保持される

---

### TSK-SPACES-003: SyncManager実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-SPACES-002, DES-SPACES-003 |
| 優先度 | P0 |
| 見積もり | 2.5h |
| 担当 | - |
| 依存 | TSK-SPACES-002 |

**実装内容**:
1. `packages/knowledge/src/spaces/sync-manager.ts` 作成
2. push(), pull(), sync()実装
3. 差分検出ロジック
4. SyncResult生成

**受け入れ条件**:
- [ ] push/pullが動作する
- [ ] 差分のみ同期される
- [ ] 同期結果が正確

---

### TSK-SPACES-004: ConflictResolver実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-SPACES-006 |
| 優先度 | P1 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-SPACES-003 |

**実装内容**:
1. `packages/knowledge/src/spaces/conflict-resolver.ts` 作成
2. 競合検出ロジック
3. 3-way merge戦略
4. 手動解決サポート

**受け入れ条件**:
- [ ] 競合が検出される
- [ ] local/remote/merged選択が可能
- [ ] マージ結果が正確

---

### TSK-SPACES-005: Spaces CLI実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-SPACES-001〜006 |
| 優先度 | P0 |
| 見積もり | 1.5h |
| 担当 | - |
| 依存 | TSK-SPACES-004 |

**実装内容**:
1. `packages/core/src/cli/commands/spaces.ts` 作成
2. connect, push, pull, status, syncサブコマンド
3. --types, --dry-run, --forceオプション

**受け入れ条件**:
- [ ] 全サブコマンドが動作する
- [ ] オプションが正しく適用される
- [ ] ヘルプが表示される

---

### TSK-SPACES-006: Spaces MCPツール実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-SPACES-001〜006 |
| 優先度 | P0 |
| 見積もり | 1.5h |
| 担当 | - |
| 依存 | TSK-SPACES-005 |

**実装内容**:
1. `packages/mcp-server/src/tools/spaces-tools.ts` 作成
2. 6つのMCPツール実装
3. MCPサーバー登録

**受け入れ条件**:
- [ ] 6つのMCPツールが動作する
- [ ] Copilot Chatから操作可能

---

## 4. CodeQL Moduleタスク

### TSK-CODEQL-001: SARIFParser実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-CODEQL-001 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | なし |

**実装内容**:
1. `packages/security/src/codeql/sarif-parser.ts` 作成
2. SARIF 2.1.0スキーマ対応
3. パース・バリデーション
4. ParsedSARIF生成

**受け入れ条件**:
- [ ] 有効なSARIFがパースできる
- [ ] 無効なSARIFでエラーが返る
- [ ] 全必須フィールドが抽出される

---

### TSK-CODEQL-002: CWEMapper実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-CODEQL-003 |
| 優先度 | P1 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | なし |

**実装内容**:
1. `packages/security/src/codeql/cwe-mapper.ts` 作成
2. `packages/security/src/codeql/cwe-database.ts` 作成
3. CWE Top 25マッピング
4. 重大度マッピング

**受け入れ条件**:
- [ ] CodeQLルールIDからCWEが取得できる
- [ ] 重大度が正しく判定される
- [ ] 検索機能が動作する

---

### TSK-CODEQL-003: FindingsMerger実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-CODEQL-002 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-CODEQL-001, TSK-CODEQL-002 |

**実装内容**:
1. `packages/security/src/codeql/findings-merger.ts` 作成
2. CodeQL + MUSUBIX結果統合
3. フィンガープリントベース重複排除
4. SecurityFinding統一形式

**受け入れ条件**:
- [ ] 両ソースの結果が統合される
- [ ] 重複が排除される
- [ ] ソース（codeql/musubix/both）が識別される

---

### TSK-CODEQL-004: FindingsStore実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-CODEQL-004 |
| 優先度 | P1 |
| 見積もり | 1.5h |
| 担当 | - |
| 依存 | TSK-CODEQL-003 |

**実装内容**:
1. Knowledge Storeへの検出結果保存
2. エンティティタイプ `security-finding` 定義
3. トレーサビリティリンク生成

**受け入れ条件**:
- [ ] 検出結果がKnowledge Storeに保存される
- [ ] 要件/設計へのリンクが作成できる
- [ ] クエリで検索できる

---

### TSK-CODEQL-005: CodeQL CLI実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-CODEQL-001〜006 |
| 優先度 | P0 |
| 見積もり | 1.5h |
| 担当 | - |
| 依存 | TSK-CODEQL-004 |

**実装内容**:
1. `packages/core/src/cli/commands/codeql.ts` 作成
2. import, list, show, merge, exportサブコマンド
3. workflowサブコマンド（GitHub Actions生成）

**受け入れ条件**:
- [ ] 全サブコマンドが動作する
- [ ] GitHub Actionsワークフローが生成される

---

### TSK-CODEQL-006: CodeQL MCPツール実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-CODEQL-006 |
| 優先度 | P0 |
| 見積もり | 1h |
| 担当 | - |
| 依存 | TSK-CODEQL-005 |

**実装内容**:
1. `packages/mcp-server/src/tools/codeql-tools.ts` 作成
2. 4つのMCPツール実装
3. MCPサーバー登録

**受け入れ条件**:
- [ ] 4つのMCPツールが動作する
- [ ] Copilot Chatから操作可能

---

## 5. Team Moduleタスク

### TSK-TEAM-001: GitClient実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-TEAM-001 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | なし |

**実装内容**:
1. `packages/knowledge/src/team/git-client.ts` 作成
2. simple-git統合
3. init, add, commit, push, pull, fetch実装
4. status, log, diff実装

**受け入れ条件**:
- [ ] Git操作が動作する
- [ ] エラーが適切にハンドリングされる
- [ ] 非Git環境でエラーが返る

---

### TSK-TEAM-002: TeamSyncManager実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-TEAM-002, DES-TEAM-003 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-TEAM-001 |

**実装内容**:
1. `packages/knowledge/src/team/team-sync-manager.ts` 作成
2. init(), push(), pull()実装
3. status()実装（ahead/behind計算）
4. autoCommit機能

**受け入れ条件**:
- [ ] 初期化が動作する
- [ ] push/pullが動作する
- [ ] 状態が正確に取得できる

---

### TSK-TEAM-003: MergeResolver実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-TEAM-004 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-TEAM-002 |

**実装内容**:
1. `packages/knowledge/src/team/merge-resolver.ts` 作成
2. 競合検出
3. ours/theirs解決
4. JSON形式の3-way merge

**受け入れ条件**:
- [ ] 競合が検出される
- [ ] ours/theirs解決が動作する
- [ ] Knowledge Store JSONが正しくマージされる

---

### TSK-TEAM-004: HistoryManager実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-TEAM-005 |
| 優先度 | P1 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-TEAM-001 |

**実装内容**:
1. `packages/knowledge/src/team/history-manager.ts` 作成
2. getHistory(), getEntityHistory()実装
3. rollback(), restore()実装
4. compare()実装

**受け入れ条件**:
- [ ] コミット履歴が取得できる
- [ ] エンティティ単位の履歴が取得できる
- [ ] ロールバックが動作する

---

### TSK-TEAM-005: Team CLI実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-TEAM-001〜007 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-TEAM-004 |

**実装内容**:
1. `packages/core/src/cli/commands/team.ts` 作成
2. init, push, pull, status, diff, log, conflicts, resolve, rollbackサブコマンド
3. オプション実装

**受け入れ条件**:
- [ ] 全サブコマンドが動作する
- [ ] ヘルプが表示される

---

### TSK-TEAM-006: Team MCPツール実装

| 属性 | 値 |
|------|-----|
| 設計ID | DES-TEAM-008 |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-TEAM-005 |

**実装内容**:
1. `packages/mcp-server/src/tools/team-tools.ts` 作成
2. 8つのMCPツール実装
3. MCPサーバー登録

**受け入れ条件**:
- [ ] 8つのMCPツールが動作する
- [ ] Copilot Chatから操作可能

---

### TSK-TEAM-007: index.ts・エクスポート整備

| 属性 | 値 |
|------|-----|
| 設計ID | DES-TEAM-* |
| 優先度 | P1 |
| 見積もり | 1h |
| 担当 | - |
| 依存 | TSK-TEAM-006 |

**実装内容**:
1. `packages/knowledge/src/team/index.ts` 作成
2. `packages/knowledge/src/index.ts` 更新
3. 公開API定義

**受け入れ条件**:
- [ ] Team機能がパッケージからエクスポートされる
- [ ] 型定義が公開される

---

### TSK-TEAM-008: ドキュメント更新

| 属性 | 値 |
|------|-----|
| 設計ID | - |
| 優先度 | P2 |
| 見積もり | 1h |
| 担当 | - |
| 依存 | TSK-TEAM-007 |

**実装内容**:
1. README.md更新
2. AGENTS.md更新（MCPツール一覧）
3. CLI --help更新

**受け入れ条件**:
- [ ] ドキュメントが最新化される
- [ ] 使用例が含まれる

---

## 6. 統合・リリースタスク

### TSK-INT-001: 統合テスト作成

| 属性 | 値 |
|------|-----|
| 設計ID | - |
| 優先度 | P0 |
| 見積もり | 3h |
| 担当 | - |
| 依存 | 全モジュール完了後 |

**実装内容**:
1. Watch統合テスト
2. Spaces統合テスト（モック）
3. CodeQL統合テスト
4. Team統合テスト

**受け入れ条件**:
- [ ] 統合テストが全パス
- [ ] カバレッジ80%以上

---

### TSK-INT-002: MCPサーバー統合

| 属性 | 値 |
|------|-----|
| 設計ID | - |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-INT-001 |

**実装内容**:
1. 新規22 MCPツールの登録
2. MCP Server index.ts更新
3. ツール一覧テスト

**受け入れ条件**:
- [ ] 全83ツール（61+22）が登録される
- [ ] Copilotから全ツールアクセス可能

---

### TSK-INT-003: バージョン更新・CHANGELOG

| 属性 | 値 |
|------|-----|
| 設計ID | - |
| 優先度 | P0 |
| 見積もり | 1h |
| 担当 | - |
| 依存 | TSK-INT-002 |

**実装内容**:
1. package.json → 3.1.0
2. CHANGELOG.md更新
3. AGENTS.md MCPツール数更新

**受け入れ条件**:
- [ ] バージョンが3.1.0
- [ ] CHANGELOGに全機能記載

---

### TSK-INT-004: npm公開

| 属性 | 値 |
|------|-----|
| 設計ID | - |
| 優先度 | P0 |
| 見積もり | 2h |
| 担当 | - |
| 依存 | TSK-INT-003 |

**実装内容**:
1. 全パッケージビルド確認
2. テスト全パス確認
3. npm publish（security, core, mcp-server, knowledge）
4. Git tag v3.1.0

**受け入れ条件**:
- [ ] npm公開完了
- [ ] インストール確認

---

## 7. タスクサマリー

| タスクID | タイトル | 見積もり | 優先度 | 依存 |
|---------|---------|---------|--------|------|
| TSK-WATCH-001 | FileWatcher実装 | 2h | P0 | - |
| TSK-WATCH-002 | TaskScheduler実装 | 2h | P0 | 001 |
| TSK-WATCH-003 | ResultReporter実装 | 1.5h | P0 | 002 |
| TSK-WATCH-004 | LintRunner実装 | 2h | P0 | 002 |
| TSK-WATCH-005 | TestRunner実装 | 2h | P0 | 002 |
| TSK-WATCH-006 | SecurityRunner実装 | 2h | P1 | 002 |
| TSK-WATCH-007 | Watch CLI実装 | 2h | P0 | 001-006 |
| TSK-WATCH-008 | Watch MCPツール実装 | 2.5h | P0 | 007 |
| TSK-SPACES-001 | SpacesClient実装 | 3h | P0 | - |
| TSK-SPACES-002 | EntityMapper実装 | 1.5h | P0 | 001 |
| TSK-SPACES-003 | SyncManager実装 | 2.5h | P0 | 002 |
| TSK-SPACES-004 | ConflictResolver実装 | 2h | P1 | 003 |
| TSK-SPACES-005 | Spaces CLI実装 | 1.5h | P0 | 004 |
| TSK-SPACES-006 | Spaces MCPツール実装 | 1.5h | P0 | 005 |
| TSK-CODEQL-001 | SARIFParser実装 | 2h | P0 | - |
| TSK-CODEQL-002 | CWEMapper実装 | 2h | P1 | - |
| TSK-CODEQL-003 | FindingsMerger実装 | 2h | P0 | 001,002 |
| TSK-CODEQL-004 | FindingsStore実装 | 1.5h | P1 | 003 |
| TSK-CODEQL-005 | CodeQL CLI実装 | 1.5h | P0 | 004 |
| TSK-CODEQL-006 | CodeQL MCPツール実装 | 1h | P0 | 005 |
| TSK-TEAM-001 | GitClient実装 | 2h | P0 | - |
| TSK-TEAM-002 | TeamSyncManager実装 | 2h | P0 | 001 |
| TSK-TEAM-003 | MergeResolver実装 | 2h | P0 | 002 |
| TSK-TEAM-004 | HistoryManager実装 | 2h | P1 | 001 |
| TSK-TEAM-005 | Team CLI実装 | 2h | P0 | 004 |
| TSK-TEAM-006 | Team MCPツール実装 | 2h | P0 | 005 |
| TSK-TEAM-007 | index.ts・エクスポート整備 | 1h | P1 | 006 |
| TSK-TEAM-008 | ドキュメント更新 | 1h | P2 | 007 |
| TSK-INT-001 | 統合テスト作成 | 3h | P0 | 全モジュール |
| TSK-INT-002 | MCPサーバー統合 | 2h | P0 | INT-001 |
| TSK-INT-003 | バージョン更新・CHANGELOG | 1h | P0 | INT-002 |
| TSK-INT-004 | npm公開 | 2h | P0 | INT-003 |

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
