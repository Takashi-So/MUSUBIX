# タスク分解書: @nahisaho/musubix-security CodeQL同等機能強化

**Document ID**: TSK-SEC-CODEQL-001  
**Version**: 1.1.0  
**Created**: 2026-01-12  
**Updated**: 2026-01-12  
**Author**: AI Agent (GitHub Copilot)  
**Status**: ✅ Completed (v3.0.13)

---

## 実装完了サマリー

| 項目 | 状態 | リリース |
|------|------|----------|
| Ruby Extractor (TSK-023, TSK-024) | ✅ 完了 | v3.0.13 |
| Rust Extractor (TSK-025, TSK-026) | ✅ 完了 | v3.0.13 |
| テスト | ✅ 1102 passed | v3.0.13 |

---

## 1. トレーサビリティ

| 要件ID | 設計ID | タスクID |
|--------|--------|----------|
| REQ-SEC-LANG-001 | DES-SEC-CODEQL-001 | TSK-001〜TSK-004 |
| REQ-SEC-LANG-002 | DES-SEC-CODEQL-001 | TSK-005〜TSK-008 |
| REQ-SEC-DB-001〜007 | DES-SEC-CODEQL-001 | TSK-009〜TSK-015 |
| REQ-SEC-CFG-001〜006 | DES-SEC-CODEQL-001 | TSK-016〜TSK-019 |
| REQ-SEC-DFG-001〜006 | DES-SEC-CODEQL-001 | TSK-020〜TSK-023 |
| REQ-SEC-LANG-003 | DES-SEC-CODEQL-001 | TSK-024〜TSK-027 |
| REQ-SEC-LANG-004 | DES-SEC-CODEQL-001 | TSK-028〜TSK-031 |
| REQ-SEC-FW-001〜008 | DES-SEC-CODEQL-001 | TSK-032〜TSK-035 |

---

## 2. タスク一覧

### 2.1 Phase 1-A: 基盤構築（優先度 P0）

#### TSK-001: BaseExtractor 抽象クラス作成

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-001 |
| **タイトル** | BaseExtractor 抽象クラスの実装 |
| **説明** | 全言語エクストラクターの基底となる抽象クラスを作成。共通インターフェースと基本実装を提供 |
| **成果物** | `packages/security/src/extractors/base-extractor.ts` |
| **依存タスク** | なし |
| **見積もり** | 2時間 |
| **完了条件** | - BaseExtractor クラスが定義されている<br>- extract(), buildAST(), buildDFG(), buildCFG() メソッドが抽象定義<br>- ExtractionResult 型が定義されている<br>- テストが通過 |

#### TSK-002: 型定義ファイル追加（CodeDB, MQL, Variant）

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-002 |
| **タイトル** | 新規型定義ファイルの作成 |
| **説明** | CodeDB、MQL、Variant 解析に必要な型定義を追加 |
| **成果物** | `packages/security/src/types/codedb.ts`<br>`packages/security/src/types/mql.ts`<br>`packages/security/src/types/variant.ts` |
| **依存タスク** | なし |
| **見積もり** | 3時間 |
| **完了条件** | - CodeDatabase, ASTStore, DFGStore, CFGStore 型が定義<br>- MQLAst, QueryPlan, QueryResult 型が定義<br>- Pattern, VariantMatch, VariantResult 型が定義<br>- types/index.ts から全てexport |

#### TSK-003: Tree-sitter 依存追加と設定

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-003 |
| **タイトル** | Tree-sitter パッケージの導入 |
| **説明** | tree-sitter と言語別パーサーの依存追加、ビルド設定 |
| **成果物** | `packages/security/package.json` 更新 |
| **依存タスク** | なし |
| **見積もり** | 1時間 |
| **完了条件** | - tree-sitter, tree-sitter-go, tree-sitter-java が dependencies に追加<br>- npm install が成功<br>- ネイティブモジュールのビルドが成功 |

#### TSK-004: extractors/index.ts エントリポイント作成

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-004 |
| **タイトル** | Extractors モジュールのエントリポイント |
| **説明** | 全エクストラクターをエクスポートするインデックスファイル |
| **成果物** | `packages/security/src/extractors/index.ts` |
| **依存タスク** | TSK-001 |
| **見積もり** | 30分 |
| **完了条件** | - BaseExtractor がエクスポートされている<br>- 将来の言語エクストラクター用のプレースホルダーコメント |

---

### 2.2 Phase 1-B: Go言語サポート（優先度 P0）

#### TSK-005: GoExtractor 基本実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-005 |
| **タイトル** | GoExtractor クラスの基本実装 |
| **説明** | Go言語のAST抽出機能を実装。tree-sitter-go を使用 |
| **成果物** | `packages/security/src/extractors/go-extractor.ts` |
| **依存タスク** | TSK-001, TSK-003 |
| **見積もり** | 4時間 |
| **完了条件** | - GoExtractor が BaseExtractor を継承<br>- .go ファイルのAST抽出が可能<br>- 関数、メソッド、構造体の検出<br>- 基本的なテストが通過 |

#### TSK-006: GoExtractor DFG構築

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-006 |
| **タイトル** | Go言語のデータフローグラフ構築 |
| **説明** | Go言語特有のデータフロー追跡（チャネル、ゴルーチン含む） |
| **成果物** | `packages/security/src/extractors/go-extractor.ts` 拡張 |
| **依存タスク** | TSK-005 |
| **見積もり** | 4時間 |
| **完了条件** | - 変数代入の追跡<br>- 関数パラメータのフロー追跡<br>- チャネル送受信のモデル化<br>- ゴルーチン間のデータフロー（基本） |

#### TSK-007: GoExtractor CFG構築

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-007 |
| **タイトル** | Go言語の制御フローグラフ構築 |
| **説明** | Go言語の制御フロー（defer, panic/recover 含む）を構築 |
| **成果物** | `packages/security/src/extractors/go-extractor.ts` 拡張 |
| **依存タスク** | TSK-005 |
| **見積もり** | 3時間 |
| **完了条件** | - if/else/switch の分岐<br>- for/range ループ<br>- defer 文の遅延実行モデル<br>- panic/recover のフロー |

#### TSK-008: GoExtractor テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-008 |
| **タイトル** | GoExtractor ユニットテスト |
| **説明** | Go言語エクストラクターの包括的テスト |
| **成果物** | `packages/security/tests/extractors/go-extractor.test.ts` |
| **依存タスク** | TSK-005, TSK-006, TSK-007 |
| **見積もり** | 2時間 |
| **完了条件** | - AST抽出テスト (≥5ケース)<br>- DFG構築テスト (≥5ケース)<br>- CFG構築テスト (≥5ケース)<br>- エッジケーステスト<br>- カバレッジ ≥80% |

---

### 2.3 Phase 1-C: Java言語サポート（優先度 P0）

#### TSK-009: JavaExtractor 基本実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-009 |
| **タイトル** | JavaExtractor クラスの基本実装 |
| **説明** | Java言語のAST抽出機能を実装。tree-sitter-java を使用 |
| **成果物** | `packages/security/src/extractors/java-extractor.ts` |
| **依存タスク** | TSK-001, TSK-003 |
| **見積もり** | 4時間 |
| **完了条件** | - JavaExtractor が BaseExtractor を継承<br>- .java ファイルのAST抽出が可能<br>- クラス、メソッド、フィールドの検出<br>- 基本的なテストが通過 |

#### TSK-010: JavaExtractor DFG構築

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-010 |
| **タイトル** | Java言語のデータフローグラフ構築 |
| **説明** | Java言語特有のデータフロー追跡（継承、インターフェース含む） |
| **成果物** | `packages/security/src/extractors/java-extractor.ts` 拡張 |
| **依存タスク** | TSK-009 |
| **見積もり** | 4時間 |
| **完了条件** | - フィールドアクセスの追跡<br>- メソッド呼び出しのフロー<br>- 継承関係の考慮<br>- static/instance の区別 |

#### TSK-011: JavaExtractor CFG構築

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-011 |
| **タイトル** | Java言語の制御フローグラフ構築 |
| **説明** | Java言語の制御フロー（例外処理含む）を構築 |
| **成果物** | `packages/security/src/extractors/java-extractor.ts` 拡張 |
| **依存タスク** | TSK-009 |
| **見積もり** | 3時間 |
| **完了条件** | - if/else/switch の分岐<br>- for/while/do-while ループ<br>- try-catch-finally の例外フロー<br>- synchronized ブロック |

#### TSK-012: JavaExtractor テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-012 |
| **タイトル** | JavaExtractor ユニットテスト |
| **説明** | Java言語エクストラクターの包括的テスト |
| **成果物** | `packages/security/tests/extractors/java-extractor.test.ts` |
| **依存タスク** | TSK-009, TSK-010, TSK-011 |
| **見積もり** | 2時間 |
| **完了条件** | - AST抽出テスト (≥5ケース)<br>- DFG構築テスト (≥5ケース)<br>- CFG構築テスト (≥5ケース)<br>- カバレッジ ≥80% |

---

### 2.4 Phase 1-D: CodeDB実装（優先度 P0）

#### TSK-013: CodeDatabase 基本構造

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-013 |
| **タイトル** | CodeDatabase クラスの実装 |
| **説明** | AST/DFG/CFG/Symbol情報を格納するデータベースクラス |
| **成果物** | `packages/security/src/codedb/database.ts` |
| **依存タスク** | TSK-002 |
| **見積もり** | 3時間 |
| **完了条件** | - CodeDatabase クラスが実装<br>- ASTStore, DFGStore, CFGStore が内包<br>- SymbolTable, CallGraph が内包<br>- メモリ効率の良いMap構造 |

#### TSK-014: CodeDBBuilder 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-014 |
| **タイトル** | CodeDBBuilder クラスの実装 |
| **説明** | ソースコードからCodeDatabaseを構築するビルダー |
| **成果物** | `packages/security/src/codedb/builder.ts` |
| **依存タスク** | TSK-013, TSK-004 |
| **見積もり** | 4時間 |
| **完了条件** | - createDatabase() でプロジェクト全体を解析<br>- 複数言語の同時解析<br>- 並列処理オプション<br>- 進捗コールバック |

#### TSK-015: CodeDBQuery 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-015 |
| **タイトル** | CodeDBQuery クラスの実装 |
| **説明** | CodeDatabaseに対するクエリ機能 |
| **成果物** | `packages/security/src/codedb/query.ts` |
| **依存タスク** | TSK-013 |
| **見積もり** | 3時間 |
| **完了条件** | - queryAST() でAST検索<br>- queryDataFlow() でパス検索<br>- queryControlFlow() でCFGパス検索<br>- querySymbols() でシンボル検索 |

#### TSK-016: CodeDB JSON シリアライズ

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-016 |
| **タイトル** | CodeDB JSON永続化機能 |
| **説明** | CodeDatabaseのJSON形式でのexport/import（Git-friendly） |
| **成果物** | `packages/security/src/codedb/serializer.ts` |
| **依存タスク** | TSK-013 |
| **見積もり** | 2時間 |
| **完了条件** | - exportToJSON() でJSON出力<br>- importFromJSON() でJSON読み込み<br>- 循環参照の適切な処理<br>- 大規模DBでもメモリ効率良好 |

#### TSK-017: CodeDB テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-017 |
| **タイトル** | CodeDB ユニットテスト |
| **説明** | CodeDatabase, Builder, Query の包括的テスト |
| **成果物** | `packages/security/tests/codedb/` |
| **依存タスク** | TSK-013, TSK-014, TSK-015, TSK-016 |
| **見積もり** | 3時間 |
| **完了条件** | - Database操作テスト (≥10ケース)<br>- Builder テスト (≥5ケース)<br>- Query テスト (≥10ケース)<br>- シリアライズテスト (≥5ケース)<br>- カバレッジ ≥85% |

---

### 2.5 Phase 1-E: CFG/DFG強化（優先度 P0）

#### TSK-018: CFGBuilder 強化

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-018 |
| **タイトル** | CFGBuilder の機能強化 |
| **説明** | 既存のCFG構築を強化。BasicBlock、ドミネーター、ループ検出 |
| **成果物** | `packages/security/src/analysis/cfg/builder.ts` |
| **依存タスク** | TSK-002 |
| **見積もり** | 4時間 |
| **完了条件** | - BasicBlock の正確な分割<br>- ドミネーター木の構築<br>- ループヘッダの検出<br>- 例外フローの統合 |

#### TSK-019: CFGAnalyzer パスセンシティブ解析

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-019 |
| **タイトル** | パスセンシティブCFG解析 |
| **説明** | 条件分岐を考慮したパスセンシティブな解析 |
| **成果物** | `packages/security/src/analysis/cfg/path-sensitive.ts` |
| **依存タスク** | TSK-018 |
| **見積もり** | 4時間 |
| **完了条件** | - 条件式の評価<br>- 到達可能パスの列挙<br>- 不可能パスの除外<br>- パス条件の収集 |

#### TSK-020: DFGBuilder 強化

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-020 |
| **タイトル** | DFGBuilder の機能強化 |
| **説明** | コンテキストセンシティブなデータフロー構築 |
| **成果物** | `packages/security/src/analysis/dfg/builder.ts` |
| **依存タスク** | TSK-002 |
| **見積もり** | 4時間 |
| **完了条件** | - 呼び出しサイトごとのコンテキスト<br>- オブジェクトプロパティの追跡<br>- 配列要素の追跡<br>- クロージャのキャプチャ |

#### TSK-021: TaintTracker 強化

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-021 |
| **タイトル** | TaintTracker の機能強化 |
| **説明** | 既存のテイント解析を強化。サニタイザー認識の改善 |
| **成果物** | `packages/security/src/analysis/dfg/taint-tracker.ts` |
| **依存タスク** | TSK-020 |
| **見積もり** | 3時間 |
| **完了条件** | - 複数テイントラベルのサポート<br>- サニタイザーの適切な認識<br>- 部分サニタイズの追跡<br>- 暗黙的フローのオプション |

#### TSK-022: CFG/DFG テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-022 |
| **タイトル** | CFG/DFG強化のユニットテスト |
| **説明** | 強化したCFG/DFG機能の包括的テスト |
| **成果物** | `packages/security/tests/analysis/` |
| **依存タスク** | TSK-018, TSK-019, TSK-020, TSK-021 |
| **見積もり** | 3時間 |
| **完了条件** | - CFGBuilder テスト (≥10ケース)<br>- パスセンシティブテスト (≥5ケース)<br>- DFGBuilder テスト (≥10ケース)<br>- TaintTracker テスト (≥10ケース)<br>- カバレッジ ≥85% |

---

### 2.6 Phase 1-F: Ruby/Rustサポート（優先度 P1）

#### TSK-023: RubyExtractor 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-023 |
| **タイトル** | RubyExtractor クラスの実装 |
| **説明** | Ruby言語のAST/DFG/CFG抽出機能を実装 |
| **成果物** | `packages/security/src/extractors/ruby-extractor.ts` |
| **依存タスク** | TSK-001, TSK-003 |
| **見積もり** | 6時間 |
| **完了条件** | - .rb ファイルのAST抽出<br>- クラス、モジュール、メソッドの検出<br>- ブロック、Procの追跡<br>- 基本的なDFG/CFG構築 |

#### TSK-024: RubyExtractor テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-024 |
| **タイトル** | RubyExtractor ユニットテスト |
| **説明** | Ruby言語エクストラクターのテスト |
| **成果物** | `packages/security/tests/extractors/ruby-extractor.test.ts` |
| **依存タスク** | TSK-023 |
| **見積もり** | 2時間 |
| **完了条件** | - 各機能のテスト (≥15ケース)<br>- カバレッジ ≥80% |

#### TSK-025: RustExtractor 実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-025 |
| **タイトル** | RustExtractor クラスの実装 |
| **説明** | Rust言語のAST/DFG/CFG抽出機能を実装 |
| **成果物** | `packages/security/src/extractors/rust-extractor.ts` |
| **依存タスク** | TSK-001, TSK-003 |
| **見積もり** | 6時間 |
| **完了条件** | - .rs ファイルのAST抽出<br>- 所有権/借用の追跡<br>- unsafe ブロックの検出<br>- 基本的なDFG/CFG構築 |

#### TSK-026: RustExtractor テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-026 |
| **タイトル** | RustExtractor ユニットテスト |
| **説明** | Rust言語エクストラクターのテスト |
| **成果物** | `packages/security/tests/extractors/rust-extractor.test.ts` |
| **依存タスク** | TSK-025 |
| **見積もり** | 2時間 |
| **完了条件** | - 各機能のテスト (≥15ケース)<br>- カバレッジ ≥80% |

---

### 2.7 Phase 1-G: フレームワーク認識（優先度 P1）

#### TSK-027: Express/NestJS モデル

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-027 |
| **タイトル** | Express/NestJS フレームワークモデル |
| **説明** | Express.js と NestJS のソース/シンク/サニタイザー定義 |
| **成果物** | `packages/security/src/frameworks/express.ts`<br>`packages/security/src/frameworks/nestjs.ts` |
| **依存タスク** | TSK-002 |
| **見積もり** | 3時間 |
| **完了条件** | - req.body/query/params をソースとして認識<br>- res.send/json をシンクとして認識<br>- バリデーションライブラリをサニタイザーとして認識<br>- NestJS デコレーターの解析 |

#### TSK-028: Django/Flask モデル

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-028 |
| **タイトル** | Django/Flask フレームワークモデル |
| **説明** | Django と Flask のソース/シンク/サニタイザー定義 |
| **成果物** | `packages/security/src/frameworks/django.ts`<br>`packages/security/src/frameworks/flask.ts` |
| **依存タスク** | TSK-002 |
| **見積もり** | 3時間 |
| **完了条件** | - request.form/args をソースとして認識<br>- render_template をシンクとして認識<br>- escape/mark_safe をサニタイザーとして認識<br>- Django ORM の追跡 |

#### TSK-029: Gin (Go) モデル

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-029 |
| **タイトル** | Gin フレームワークモデル |
| **説明** | Go Gin フレームワークのソース/シンク/サニタイザー定義 |
| **成果物** | `packages/security/src/frameworks/gin.ts` |
| **依存タスク** | TSK-002, TSK-005 |
| **見積もり** | 2時間 |
| **完了条件** | - c.Param/Query/PostForm をソースとして認識<br>- c.JSON/String をシンクとして認識<br>- バリデーションの認識 |

#### TSK-030: フレームワーク統合テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-030 |
| **タイトル** | フレームワークモデル統合テスト |
| **説明** | フレームワークモデルの包括的テスト |
| **成果物** | `packages/security/tests/frameworks/` |
| **依存タスク** | TSK-027, TSK-028, TSK-029 |
| **見積もり** | 2時間 |
| **完了条件** | - 各フレームワークのテスト (≥5ケース/FW)<br>- 実際のコードサンプルでの検証<br>- 偽陽性/偽陰性の確認 |

---

### 2.8 Phase 1-H: 統合・リリース

#### TSK-031: MultiLanguageScanner 拡張

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-031 |
| **タイトル** | MultiLanguageScanner の拡張 |
| **説明** | 既存のMultiLanguageScannerにGo/Java/Ruby/Rustを追加 |
| **成果物** | `packages/security/src/analysis/multi-language-scanner.ts` 更新 |
| **依存タスク** | TSK-005, TSK-009, TSK-023, TSK-025 |
| **見積もり** | 2時間 |
| **完了条件** | - SupportedLanguage に4言語追加<br>- detectLanguage() の拡張子マッピング<br>- scanFile() のルーティング |

#### TSK-032: index.ts エクスポート更新

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-032 |
| **タイトル** | メインindex.ts のエクスポート更新 |
| **説明** | 新規追加した全モジュールをindex.tsからエクスポート |
| **成果物** | `packages/security/src/index.ts` 更新 |
| **依存タスク** | 全タスク |
| **見積もり** | 1時間 |
| **完了条件** | - Extractors エクスポート<br>- CodeDB エクスポート<br>- Frameworks エクスポート<br>- 型定義エクスポート |

#### TSK-033: 統合テスト

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-033 |
| **タイトル** | Phase 1 統合テスト |
| **説明** | 全コンポーネントの統合テスト |
| **成果物** | `packages/security/tests/integration/phase1.test.ts` |
| **依存タスク** | TSK-031, TSK-032 |
| **見積もり** | 3時間 |
| **完了条件** | - マルチ言語プロジェクトのスキャン<br>- CodeDB生成と永続化<br>- フレームワーク認識<br>- エンドツーエンドのテスト |

#### TSK-034: ドキュメント更新

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-034 |
| **タイトル** | ドキュメント更新 |
| **説明** | README、API Reference、CHANGELOG の更新 |
| **成果物** | `packages/security/README.md`<br>`docs/API-REFERENCE.md`<br>`CHANGELOG.md` |
| **依存タスク** | TSK-033 |
| **見積もり** | 2時間 |
| **完了条件** | - 新機能の説明<br>- APIドキュメント<br>- 使用例 |

#### TSK-035: バージョン更新・リリース準備

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-035 |
| **タイトル** | v3.1.0 リリース準備 |
| **説明** | package.json バージョン更新、ビルド確認、リリースノート |
| **成果物** | `packages/security/package.json`<br>Git tag: v3.1.0 |
| **依存タスク** | TSK-034 |
| **見積もり** | 1時間 |
| **完了条件** | - バージョン 3.1.0<br>- 全テスト通過<br>- ビルド成功<br>- リリースノート作成 |

---

## 3. 実行順序と依存関係

```
TSK-001 ─────────────────────────────┐
TSK-002 ─────────────────────────────┤
TSK-003 ─────────────────────────────┤
                                     ▼
TSK-004 ◄─── TSK-001                 │
                                     │
┌────────────────────────────────────┴────────────────────────────────────┐
│                          並列実行可能                                     │
│                                                                          │
│  ┌─ Go言語 ─────────────┐   ┌─ Java言語 ────────────┐                   │
│  │ TSK-005 (基本)        │   │ TSK-009 (基本)        │                   │
│  │    ↓                  │   │    ↓                  │                   │
│  │ TSK-006 (DFG)         │   │ TSK-010 (DFG)         │                   │
│  │ TSK-007 (CFG)         │   │ TSK-011 (CFG)         │                   │
│  │    ↓                  │   │    ↓                  │                   │
│  │ TSK-008 (テスト)      │   │ TSK-012 (テスト)      │                   │
│  └───────────────────────┘   └───────────────────────┘                   │
│                                                                          │
│  ┌─ CodeDB ─────────────────────────────────────┐                       │
│  │ TSK-013 (Database) ◄── TSK-002               │                       │
│  │    ↓                                         │                       │
│  │ TSK-014 (Builder) ◄── TSK-004                │                       │
│  │ TSK-015 (Query)                              │                       │
│  │ TSK-016 (Serializer)                         │                       │
│  │    ↓                                         │                       │
│  │ TSK-017 (テスト)                             │                       │
│  └──────────────────────────────────────────────┘                       │
│                                                                          │
│  ┌─ CFG/DFG強化 ─────────────────────────────────┐                      │
│  │ TSK-018 (CFGBuilder) ◄── TSK-002              │                      │
│  │    ↓                                          │                      │
│  │ TSK-019 (パスセンシティブ)                    │                      │
│  │ TSK-020 (DFGBuilder)                          │                      │
│  │    ↓                                          │                      │
│  │ TSK-021 (TaintTracker)                        │                      │
│  │    ↓                                          │                      │
│  │ TSK-022 (テスト)                              │                      │
│  └───────────────────────────────────────────────┘                      │
│                                                                          │
└──────────────────────────────────────────────────────────────────────────┘

┌─ Ruby/Rust (P1) ──────────────────┐   ┌─ フレームワーク (P1) ────────────┐
│ TSK-023 (Ruby)                     │   │ TSK-027 (Express/NestJS)         │
│    ↓                               │   │ TSK-028 (Django/Flask)           │
│ TSK-024 (テスト)                   │   │ TSK-029 (Gin)                    │
│ TSK-025 (Rust)                     │   │    ↓                             │
│    ↓                               │   │ TSK-030 (テスト)                 │
│ TSK-026 (テスト)                   │   └──────────────────────────────────┘
└────────────────────────────────────┘

                                     ▼
TSK-031 (MultiLanguageScanner) ◄── Go/Java/Ruby/Rust
                                     ▼
TSK-032 (index.ts) ◄── 全モジュール
                                     ▼
TSK-033 (統合テスト)
                                     ▼
TSK-034 (ドキュメント)
                                     ▼
TSK-035 (リリース)
```

---

## 4. サマリー

| カテゴリ | タスク数 | 合計見積もり |
|---------|---------|-------------|
| 基盤構築 (P0) | 4 | 6.5時間 |
| Go言語 (P0) | 4 | 13時間 |
| Java言語 (P0) | 4 | 13時間 |
| CodeDB (P0) | 5 | 15時間 |
| CFG/DFG強化 (P0) | 5 | 18時間 |
| Ruby/Rust (P1) | 4 | 16時間 |
| フレームワーク (P1) | 4 | 10時間 |
| 統合・リリース | 5 | 9時間 |
| **合計** | **35** | **100.5時間** |

**想定期間**: 約2.5週間（1人/日8時間想定）

---

## 5. セルフレビュー

| 観点 | 状態 | 詳細 |
|------|------|------|
| 設計との対応 | ✅ OK | DES-SEC-CODEQL-001 の全コンポーネントをカバー |
| タスクサイズ | ✅ OK | 各タスク 1〜6時間で適切 |
| 依存関係 | ✅ OK | 依存グラフが明確、並列実行可能箇所を明示 |
| 完了条件 | ✅ OK | 各タスクに具体的な完了条件を定義 |
| テストカバレッジ | ✅ OK | 各コンポーネントにテストタスクあり |
| 見積もり妥当性 | ✅ OK | 類似実装の経験に基づく見積もり |

---

👉 **次のアクションを選択してください:**
- **修正** / 具体的な修正指示 → 修正して再提示
- **承認** / **OK** / **進める** → Phase 4（実装）へ

**✅ Article X準拠**: 要件定義・設計・タスク分解が完了しました。承認後、実装を開始します。
