# REQ-BUGFIX-v3.3.10: ニューロシンボリック統合テストで発見された不具合修正

## 概要

v3.3.9のニューロシンボリック開発検証テストにおいて、以下の不具合・改善点が発見されました。
本要件定義書はこれらの問題を解決するための要件を定義します。

## 発見された問題

| ID | カテゴリ | 問題概要 | 重要度 |
|----|----------|----------|--------|
| BUG-001 | CLI | scaffoldコマンドの出力不足 | P0 |
| BUG-002 | API | getMissingQuestions関数の引数エラーハンドリング不足 | P1 |
| BUG-003 | CLI | codegenコマンドのスケルトン生成不完全 | P1 |
| BUG-004 | Doc | QualityGateValidator APIドキュメント不足 | P2 |
| BUG-005 | CLI | npxグローバルキャッシュによる古いバージョン実行 | P1 |
| BUG-006 | CLI | codegen generateにテスト生成機能が未統合 | P1 |

---

## 要件定義（EARS形式）

### REQ-BUGFIX-001: scaffoldコマンドの出力改善

#### REQ-BUGFIX-001-01: 生成ファイル一覧の表示
WHEN the user executes `musubix scaffold domain-model <name>`, THE system SHALL display a complete list of all generated files with their paths.

#### REQ-BUGFIX-001-02: 生成内容の詳細表示
WHEN the scaffold command completes successfully, THE system SHALL display the number of files created, total lines of code, and directory structure.

#### REQ-BUGFIX-001-03: エラー時のガイダンス
IF the scaffold command fails, THEN THE system SHALL provide a clear error message with suggested remediation steps.

#### REQ-BUGFIX-001-04: 出力ディレクトリの確認
WHEN generating files, THE system SHALL verify the target directory exists and is writable before attempting to create files.

---

### REQ-BUGFIX-002: getMissingQuestions関数の堅牢性向上

#### REQ-BUGFIX-002-01: 引数型の柔軟な受け入れ
WHEN `getMissingQuestions` receives a `ClarificationContext` object instead of `missingIds` array, THE system SHALL automatically extract missing question IDs by calling `analyzeContextCompleteness` internally.

#### REQ-BUGFIX-002-02: 引数バリデーション
THE system SHALL validate input arguments and provide a clear TypeError message when invalid types are passed to `getMissingQuestions`.

#### REQ-BUGFIX-002-03: オーバーロード対応
THE system SHALL support both calling patterns:
- `getMissingQuestions(missingIds: string[])`
- `getMissingQuestions(context: ClarificationContext)`

#### REQ-BUGFIX-002-04: 空配列のハンドリング
WHEN an empty array or undefined is passed to `getMissingQuestions`, THE system SHALL return all 5 core questions.

---

### REQ-BUGFIX-003: codegenコマンドの完全実装

#### REQ-BUGFIX-003-01: C4設計からのコード生成
WHEN the user executes `musubix codegen generate <design.md>`, THE system SHALL generate TypeScript skeleton code for all components defined in the C4 design document.

#### REQ-BUGFIX-003-02: 設計パターン自動適用
THE system SHALL automatically detect and apply appropriate design patterns (Repository, Service, Factory) based on component descriptions.

#### REQ-BUGFIX-003-03: トレーサビリティコメント
THE system SHALL include traceability comments linking generated code back to design document sections (DES-* references).

#### REQ-BUGFIX-003-04: 生成ファイルの構造
WHEN generating code, THE system SHALL create:
- Interface definitions (*.interface.ts)
- Implementation skeletons (*.ts)
- Unit test templates (*.test.ts)
- Index exports (index.ts)

---

### REQ-BUGFIX-004: APIドキュメント改善

#### REQ-BUGFIX-004-01: QualityGateValidator使用例
THE system SHALL provide clear usage examples for `QualityGateValidator` in API documentation including:
- Constructor parameters
- Method signatures
- Return types
- Error handling patterns

#### REQ-BUGFIX-004-02: ニューロシンボリック統合API
THE system SHALL document the neuro-symbolic integration APIs with examples showing:
- Neural result input format
- Symbolic validation process
- Confidence routing rules
- Result blending behavior

#### REQ-BUGFIX-004-03: JSDocコメント
THE system SHALL include comprehensive JSDoc comments for all public APIs in the symbolic module.

---

### REQ-BUGFIX-005: CLIバージョン管理改善

#### REQ-BUGFIX-005-01: バージョン表示の正確性
WHEN the user executes `musubix --version` or `musubix -v`, THE system SHALL display the currently installed package version accurately.

#### REQ-BUGFIX-005-02: キャッシュバイパスオプション
IF the user suspects version mismatch, THEN THE system SHALL provide guidance to clear npx cache (`npx clear-npx-cache` or `npx --yes musubix@latest`).

#### REQ-BUGFIX-005-03: バージョン不一致警告
WHEN the CLI detects a mismatch between the installed version and the expected version in musubix.config.json, THE system SHALL display a warning message.

#### REQ-BUGFIX-005-04: 依存パッケージバージョン表示
WHEN `musubix --version --verbose` is executed, THE system SHALL display versions of all 5 core dependent packages: @nahisaho/musubix-core, @nahisaho/musubix-mcp-server, @musubix/knowledge, @musubix/policy, and @musubix/decisions.

#### REQ-BUGFIX-005-05: --verboseオプションの実装
THE system SHALL support a `--verbose` flag for the version command that enables detailed output mode.

---

### REQ-BUGFIX-006: テスト生成機能の統合

#### REQ-BUGFIX-006-01: codegen generateへのテスト生成統合
WHEN the user executes `musubix codegen generate <design.md> --with-tests`, THE system SHALL generate unit test files alongside the implementation skeleton files.

#### REQ-BUGFIX-006-02: 既存unit-test-generatorとの統合
THE system SHALL utilize the existing `unit-test-generator.ts` module for generating test files during code generation.

#### REQ-BUGFIX-006-03: テストファイル命名規則
WHEN generating test files, THE system SHALL follow the naming convention `<component-name>.test.ts` and place them in the same directory as the implementation file or in a `__tests__` subdirectory.

#### REQ-BUGFIX-006-04: テストカバレッジ対象
THE system SHALL generate tests that cover:
- Constructor and initialization
- Public method signatures
- Error handling scenarios
- Edge cases based on EARS requirements

---

## 優先度と実装順序

### P0（必須 - v3.3.10でリリース）
- REQ-BUGFIX-001-01, REQ-BUGFIX-001-02
- REQ-BUGFIX-002-01, REQ-BUGFIX-002-02

### P1（重要 - v3.3.10でリリース）
- REQ-BUGFIX-001-03, REQ-BUGFIX-001-04
- REQ-BUGFIX-002-03, REQ-BUGFIX-002-04
- REQ-BUGFIX-003-01, REQ-BUGFIX-003-02, REQ-BUGFIX-003-03, REQ-BUGFIX-003-04
- REQ-BUGFIX-005-01, REQ-BUGFIX-005-02, REQ-BUGFIX-005-03, REQ-BUGFIX-005-05
- REQ-BUGFIX-006-01, REQ-BUGFIX-006-02, REQ-BUGFIX-006-03, REQ-BUGFIX-006-04

### P2（任意 - v3.4.0で対応可）
- REQ-BUGFIX-004-01, REQ-BUGFIX-004-02, REQ-BUGFIX-004-03
- REQ-BUGFIX-005-04

---

## テスト要件

### テストケース一覧

| 要件ID | テストケース | 期待結果 |
|--------|-------------|----------|
| REQ-BUGFIX-001-01 | `npx musubix scaffold domain-model TestApp` | ファイル一覧が表示される |
| REQ-BUGFIX-002-01 | `getMissingQuestions({purpose: 'test'})` | 不足質問が返却される（エラーにならない） |
| REQ-BUGFIX-002-02 | `getMissingQuestions(123)` | TypeErrorが発生し、明確なメッセージが表示される |
| REQ-BUGFIX-003-01 | `npx musubix codegen generate design.md` | TypeScriptスケルトンが生成される |
| REQ-BUGFIX-005-05 | `npx musubix -v --verbose` | 詳細バージョン情報が表示される |
| REQ-BUGFIX-006-01 | `npx musubix codegen generate design.md --with-tests` | 実装ファイルとテストファイルが生成される |
| REQ-BUGFIX-005-01 | `npx musubix -v` | 正確なバージョン番号が表示される |

---

## トレーサビリティ

| 要件ID | 関連設計 | 関連タスク | 関連テスト |
|--------|----------|-----------|-----------|
| REQ-BUGFIX-001 | DES-BUGFIX-001 | TSK-BUGFIX-001 | TEST-BUGFIX-001 |
| REQ-BUGFIX-002 | DES-BUGFIX-002 | TSK-BUGFIX-002 | TEST-BUGFIX-002 |
| REQ-BUGFIX-003 | DES-BUGFIX-003 | TSK-BUGFIX-003 | TEST-BUGFIX-003 |
| REQ-BUGFIX-004 | DES-BUGFIX-004 | TSK-BUGFIX-004 | TEST-BUGFIX-004 |
| REQ-BUGFIX-005 | DES-BUGFIX-005 | TSK-BUGFIX-005 | TEST-BUGFIX-005 |
| REQ-BUGFIX-006 | DES-BUGFIX-006 | TSK-BUGFIX-006 | TEST-BUGFIX-006 |

---

## 承認

| 役割 | 名前 | 日付 | 署名 |
|------|------|------|------|
| 作成者 | AI Agent | 2026-01-14 | ✅ |
| レビュアー | | | |
| 承認者 | | | |

---

## 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-14 | 初版作成 | AI Agent |
| 1.1 | 2026-01-14 | REQ-BUGFIX-005-05, REQ-BUGFIX-006追加 | AI Agent |
