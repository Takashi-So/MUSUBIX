# 要件定義書: Go言語セキュリティエクストラクター

**Document ID**: REQ-SEC-GO-001  
**Version**: 1.0.0  
**Created**: 2026-01-12  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft (レビュー待ち)  
**Priority**: P0 (必須)  
**Target Release**: v3.0.14

---

## 1. 概要

`@nahisaho/musubix-security`パッケージにGo言語向けセキュリティエクストラクター（GoExtractor）を追加し、Goプロジェクトの脆弱性検出機能を実現する。

---

## 2. 背景・動機

### 2.1 現状分析

| 言語 | Extractor | Scanner | 状態 |
|------|-----------|---------|------|
| TypeScript | ✅ | ✅ | Production |
| JavaScript | ✅ | ✅ | Production |
| Python | ✅ | ✅ | Production |
| PHP | ✅ | ✅ | Production |
| Ruby | ✅ | ⏳ | v3.0.13追加 |
| Rust | ✅ | ⏳ | v3.0.13追加 |
| **Go** | ❌ | ❌ | 未対応 |
| Java | ❌ | ❌ | 未対応 |

### 2.2 Go言語の重要性

- **Kubernetes/Cloud Native**: Docker, Kubernetes, Terraform等のインフラツールはGoで記述
- **バックエンドサービス**: 高性能APIサーバーでの採用増加
- **セキュリティツール**: 多くのセキュリティツールがGoで実装
- **競合対応**: CodeQL, Semgrep, Snyk Code全てがGo対応済み

### 2.3 Go言語固有のセキュリティ課題

| カテゴリ | 脆弱性パターン | CWE |
|---------|----------------|-----|
| SQL Injection | `database/sql`での文字列連結 | CWE-89 |
| Command Injection | `os/exec`でのシェル展開 | CWE-78 |
| Path Traversal | `os.Open`等へのユーザー入力 | CWE-22 |
| SSRF | `http.Get`等へのユーザー入力 | CWE-918 |
| Race Condition | Goroutine間のデータ競合 | CWE-362 |
| Unsafe Pointer | `unsafe`パッケージの誤用 | CWE-119 |
| XXE | XMLパーサーの設定不備 | CWE-611 |
| Hardcoded Secrets | 埋め込みクレデンシャル | CWE-798 |

---

## 3. 要件一覧

### 3.1 機能要件

#### REQ-SEC-GO-001: GoExtractorの実装

> **WHEN** ユーザーが`.go`ファイルを解析対象に指定した場合,  
> **THE** GoExtractorモジュール **SHALL** BaseExtractorインターフェースを実装し、以下の抽出機能を提供する:
> - AST (Abstract Syntax Tree) の構築
> - DFG (Data Flow Graph) の構築
> - CFG (Control Flow Graph) の構築
> - Symbol Table の構築

**受入基準**:
- `extract(source, filePath)` メソッドが`ExtractionResult`を返す
- `getFrameworkModels()` メソッドがGoフレームワークモデルを返す
- `supports(filePath)` メソッドが`.go`ファイルを正しく判定

#### REQ-SEC-GO-002: tree-sitter-go統合

> **WHEN** GoExtractorがソースコードを解析する場合,  
> **THE** GoExtractor **SHALL** tree-sitter-goを使用してASTを構築する。
> **IF** tree-sitter-goが利用不可の場合,  
> **THEN THE** GoExtractor **SHALL** フォールバックASTを生成し、基本的な解析を継続する。

**受入基準**:
- tree-sitter-goがoptional依存として定義
- パーサー初期化失敗時にエラーをスローせずフォールバック

#### REQ-SEC-GO-003: Go固有ソースパターン検出

> **WHILE** GoExtractorがDFGを構築している状態,  
> **THE** GoExtractor **SHALL** 以下のソースパターンを検出しtaintラベルを付与する:

| パターン | ソースタイプ | taintラベル |
|---------|-------------|------------|
| `r.URL.Query()` | HTTP Query | `user_input` |
| `r.FormValue()` | HTTP Form | `user_input` |
| `r.PostFormValue()` | HTTP Form | `user_input` |
| `r.Header.Get()` | HTTP Header | `user_input` |
| `r.Body` | HTTP Body | `user_input` |
| `r.Cookie()` | Cookie | `user_input` |
| `os.Args` | CLI Args | `user_input` |
| `os.Getenv()` | Environment | `env_input` |
| `bufio.NewReader(os.Stdin)` | Stdin | `user_input` |

**受入基準**:
- 各パターンに対応するテストケースが存在
- taintラベルがDFGノードに正しく設定

#### REQ-SEC-GO-004: Go固有シンクパターン検出

> **WHILE** GoExtractorがDFGを構築している状態,  
> **THE** GoExtractor **SHALL** 以下のシンクパターンを検出し脆弱性タイプを記録する:

| パターン | シンクタイプ | 脆弱性タイプ | 深刻度 |
|---------|-------------|-------------|--------|
| `db.Query()` (文字列連結) | SQL | sql_injection | critical |
| `db.Exec()` (文字列連結) | SQL | sql_injection | critical |
| `db.QueryRow()` (文字列連結) | SQL | sql_injection | critical |
| `exec.Command()` | Command | command_injection | critical |
| `exec.CommandContext()` | Command | command_injection | critical |
| `os.Open()` | File | path_traversal | high |
| `os.OpenFile()` | File | path_traversal | high |
| `os.ReadFile()` | File | path_traversal | high |
| `os.WriteFile()` | File | path_traversal | high |
| `http.Get()` | HTTP | ssrf | high |
| `http.Post()` | HTTP | ssrf | high |
| `http.NewRequest()` | HTTP | ssrf | high |
| `template.HTML()` | Template | xss | high |
| `w.Write()` (HTMLレスポンス) | Response | xss | high |
| `http.Redirect()` | Redirect | open_redirect | medium |
| `xml.Unmarshal()` | XML | xxe | high |

**受入基準**:
- 各パターンに対応するテストケースが存在
- vulnerabilityTypeとseverityがDFGノードに正しく設定

#### REQ-SEC-GO-005: Go固有サニタイザーパターン検出

> **WHILE** GoExtractorがDFGを構築している状態,  
> **THE** GoExtractor **SHALL** 以下のサニタイザーパターンを検出する:

| パターン | サニタイズ対象 |
|---------|---------------|
| `db.Prepare()` | sql_injection |
| `filepath.Clean()` | path_traversal |
| `filepath.Abs()` | path_traversal |
| `html.EscapeString()` | xss |
| `template.HTMLEscapeString()` | xss |
| `url.PathEscape()` | path_traversal |
| `url.QueryEscape()` | ssrf |
| `strconv.Atoi()` | sql_injection, command_injection |

**受入基準**:
- サニタイザー検出後、対応するtaintラベルが除去される

#### REQ-SEC-GO-006: Goフレームワークモデル

> **THE** GoExtractor **SHALL** 以下のフレームワークモデルを提供する:

| フレームワーク | 説明 |
|---------------|------|
| `net/http` | 標準HTTPライブラリ |
| `database/sql` | 標準データベースライブラリ |
| `os/exec` | コマンド実行 |
| `os` | ファイルシステム操作 |
| `encoding/xml` | XML処理 |
| `html/template` | HTMLテンプレート |
| `Gin` | Ginフレームワーク |
| `Echo` | Echoフレームワーク |
| `Fiber` | Fiberフレームワーク |
| `GORM` | GORM ORM |

**受入基準**:
- `getFrameworkModels()` が10個以上のモデルを返す
- 各モデルに sources, sinks, sanitizers が定義

#### REQ-SEC-GO-007: CFG構築

> **WHEN** GoExtractorがCFGを構築する場合,  
> **THE** GoExtractor **SHALL** 以下の制御構造を正しく処理する:
> - `if` / `else if` / `else` 文
> - `for` 文 (通常、range、条件なし)
> - `switch` / `select` 文
> - `defer` 文
> - `go` 文 (goroutine)
> - `return` / `break` / `continue` / `goto` 文
> - `panic` / `recover`

**受入基準**:
- 各制御構造に対応するBasicBlockが生成される
- エントリブロックとエグジットブロックが正しく設定

#### REQ-SEC-GO-008: Symbol Table構築

> **WHEN** GoExtractorがSymbol Tableを構築する場合,  
> **THE** GoExtractor **SHALL** 以下のシンボルを抽出する:
> - パッケージ宣言
> - import文
> - 関数宣言 (func)
> - メソッド宣言 (receiver付きfunc)
> - 型宣言 (type)
> - 構造体 (struct)
> - インターフェース (interface)
> - 定数 (const)
> - 変数 (var)

**受入基準**:
- 各シンボルタイプが正しく分類される
- エクスポート状態（大文字始まり）が正しく判定される

### 3.2 非機能要件

#### REQ-SEC-GO-PERF-001: 解析性能

> **THE** GoExtractor **SHALL** 1ファイルあたり500ms以内で解析を完了する。

**受入基準**:
- 1000行のGoファイルが500ms以内に解析完了

#### REQ-SEC-GO-COMPAT-001: 後方互換性

> **THE** GoExtractor実装 **SHALL NOT** 既存のRuby/Rust/その他エクストラクターの動作を変更する。

**受入基準**:
- 既存テスト（1102件）が全て合格

#### REQ-SEC-GO-TREE-001: tree-sitter依存

> **THE** GoExtractor **SHALL** tree-sitter-goをoptional peerDependencyとして使用する。

**受入基準**:
- tree-sitter-goが未インストールでもビルド・テストが成功

---

## 4. 成果物一覧

| 成果物 | パス | 説明 |
|--------|------|------|
| GoExtractor | `packages/security/src/extractors/go-extractor.ts` | Go言語エクストラクター |
| テスト | `packages/security/tests/go-extractor.test.ts` | ユニットテスト |
| index更新 | `packages/security/src/extractors/index.ts` | エクスポート追加 |
| 設計書 | `storage/design/DES-SEC-GO-001.md` | 設計ドキュメント |
| タスク分解書 | `storage/tasks/TSK-SEC-GO-001.md` | 実装タスク |

---

## 5. トレーサビリティ

| 要件ID | 設計ID | タスクID |
|--------|--------|----------|
| REQ-SEC-GO-001 | DES-SEC-GO-001 | TSK-GO-001 |
| REQ-SEC-GO-002 | DES-SEC-GO-001 | TSK-GO-002 |
| REQ-SEC-GO-003 | DES-SEC-GO-001 | TSK-GO-003 |
| REQ-SEC-GO-004 | DES-SEC-GO-001 | TSK-GO-004 |
| REQ-SEC-GO-005 | DES-SEC-GO-001 | TSK-GO-005 |
| REQ-SEC-GO-006 | DES-SEC-GO-001 | TSK-GO-006 |
| REQ-SEC-GO-007 | DES-SEC-GO-001 | TSK-GO-007 |
| REQ-SEC-GO-008 | DES-SEC-GO-001 | TSK-GO-008 |

---

## 6. 受入基準（全体）

1. ✅ GoExtractorがBaseExtractor抽象クラスを正しく実装
2. ✅ `extract()` メソッドがExtractionResultを返す
3. ✅ 10個のフレームワークモデルが定義済み
4. ✅ ソース/シンク/サニタイザーパターンが正しく検出
5. ✅ CFGが制御構造を正しく表現
6. ✅ Symbol Tableがエクスポート状態を正しく判定
7. ✅ テストカバレッジ80%以上
8. ✅ 既存テスト全合格
9. ✅ CHANGELOG.md更新

---

## 7. リスク分析

| リスク | 影響 | 確率 | 軽減策 |
|--------|------|------|--------|
| tree-sitter-go互換性 | 高 | 低 | フォールバックAST実装 |
| Goの複雑な構文 | 中 | 中 | 段階的なパターン追加 |
| 型推論の複雑さ | 中 | 中 | 基本型のみ初期対応 |
| Goroutine解析 | 高 | 高 | 初期版では基本検出のみ |

---

## 8. 参考資料

- [Go Language Specification](https://go.dev/ref/spec)
- [tree-sitter-go](https://github.com/tree-sitter/tree-sitter-go)
- [OWASP Go Security Cheat Sheet](https://cheatsheetseries.owasp.org/cheatsheets/Go_Security_Cheat_Sheet.html)
- [CWE Top 25](https://cwe.mitre.org/top25/)
- [RubyExtractor実装](packages/security/src/extractors/ruby-extractor.ts)
- [RustExtractor実装](packages/security/src/extractors/rust-extractor.ts)

---

**Document End**
