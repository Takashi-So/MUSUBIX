# MUSUBIX v2.3.2 タスク分解書

## 多言語AST解析拡張（CodeGraph Multi-Language Support）

**Document ID**: TSK-CG-MULTILANG
**Version**: 2.3.2
**Status**: Draft
**Created**: 2026-01-09
**Design Reference**: DES-CG-MULTILANG
**Requirements Reference**: REQ-CG-MULTILANG

---

## 1. タスク概要

| カテゴリ | タスク数 | 合計見積もり |
|----------|----------|-------------|
| 基盤（Foundation） | 3 | 4時間 |
| P0言語（Critical） | 3 | 6時間 |
| P1言語（High） | 5 | 7.5時間 |
| P2言語（Medium） | 5 | 5時間 |
| テスト | 3 | 4時間 |
| 統合・リリース | 3 | 2.5時間 |
| **合計** | **22** | **29時間** |

---

## 2. タスク一覧

### 2.1 基盤タスク（Foundation）

#### TSK-CG-001: BaseExtractor基底クラス実装
**Design**: DES-CG-BASE
**Priority**: P0 (Critical)
**Estimate**: 2時間
**Dependencies**: なし

**Description**:
全言語エクストラクターの基底クラスを実装する。

**Subtasks**:
- [ ] `packages/codegraph/src/parser/extractors/` ディレクトリ作成
- [ ] `LanguageConfig` インターフェース定義
- [ ] `BaseExtractor` 抽象クラス実装
  - [ ] `createEntity()` メソッド
  - [ ] `createRelation()` メソッド
  - [ ] `walkTree()` メソッド
  - [ ] `getNodeText()` メソッド
  - [ ] `getChildByField()` メソッド
- [ ] ユニットテスト作成

**Acceptance Criteria**:
- BaseExtractorを継承した具体クラスが作成可能
- createEntity/createRelationが正しいID形式で生成

---

#### TSK-CG-002: ExtractorRegistry実装
**Design**: DES-CG-REGISTRY
**Priority**: P0 (Critical)
**Estimate**: 1時間
**Dependencies**: TSK-CG-001

**Description**:
言語エクストラクターを登録・取得するレジストリを実装する。

**Subtasks**:
- [ ] `extractors/index.ts` 作成
- [ ] `registerExtractor()` 関数実装
- [ ] `getExtractor()` 関数実装
- [ ] `getRegisteredLanguages()` 関数実装
- [ ] エクスポート設定

**Acceptance Criteria**:
- 言語名でエクストラクターを取得可能
- 登録済み言語一覧を取得可能

---

#### TSK-CG-003: AST Parser統合
**Design**: DES-CG-PARSER
**Priority**: P0 (Critical)
**Estimate**: 1時間
**Dependencies**: TSK-CG-002

**Description**:
既存のAST Parserを拡張し、ExtractorRegistryと連携させる。

**Subtasks**:
- [ ] `loadGrammar()` メソッド追加（lazy loading）
- [ ] `parseWithTreeSitter()` をExtractor使用に変更
- [ ] エラーハンドリング（grammar未インストール時のフォールバック）
- [ ] 既存テストが通ることを確認

**Acceptance Criteria**:
- 既存のTypeScript/JavaScript/Python解析が動作
- grammar未インストール時にフォールバック動作

---

### 2.2 P0言語タスク（Critical）

#### TSK-CG-010: Rust言語エクストラクター実装
**Design**: DES-CG-RUST
**Requirement**: REQ-CG-MULTILANG-001
**Priority**: P0 (Critical)
**Estimate**: 2時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Description**:
Rust言語のAST解析エクストラクターを実装する。

**Subtasks**:
- [ ] `extractors/rust.ts` 作成
- [ ] `RustExtractor` クラス実装
- [ ] `extractFunction()` - fn宣言
- [ ] `extractStruct()` - struct宣言
- [ ] `extractEnum()` - enum宣言
- [ ] `extractTrait()` - trait宣言
- [ ] `extractImpl()` - implブロック
- [ ] `extractUse()` - use文
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

**Test Cases**:
```rust
// テスト対象コード例
fn hello() {}
struct Point { x: i32, y: i32 }
enum Color { Red, Green, Blue }
trait Drawable { fn draw(&self); }
impl Drawable for Point { fn draw(&self) {} }
use std::collections::HashMap;
```

**Acceptance Criteria**:
- 全Rust構文要素が正しくEntity/Relationに変換される
- テストカバレッジ80%以上

---

#### TSK-CG-011: Go言語エクストラクター実装
**Design**: DES-CG-GO
**Requirement**: REQ-CG-MULTILANG-002
**Priority**: P0 (Critical)
**Estimate**: 2時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Description**:
Go言語のAST解析エクストラクターを実装する。

**Subtasks**:
- [ ] `extractors/go.ts` 作成
- [ ] `GoExtractor` クラス実装
- [ ] `extractFunction()` - func宣言
- [ ] `extractMethod()` - メソッド（レシーバー付き）
- [ ] `extractStruct()` - type X struct
- [ ] `extractInterface()` - type X interface
- [ ] `extractPackage()` - package文
- [ ] `extractImport()` - import文
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

**Test Cases**:
```go
package main
import "fmt"
func main() {}
type Point struct { X, Y int }
type Reader interface { Read() }
func (p Point) String() string { return "" }
```

**Acceptance Criteria**:
- Go構文要素が正しくEntity/Relationに変換される
- メソッドのレシーバー情報が保持される

---

#### TSK-CG-012: Java言語エクストラクター実装
**Design**: DES-CG-JAVA
**Requirement**: REQ-CG-MULTILANG-003
**Priority**: P0 (Critical)
**Estimate**: 2時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Description**:
Java言語のAST解析エクストラクターを実装する。

**Subtasks**:
- [ ] `extractors/java.ts` 作成
- [ ] `JavaExtractor` クラス実装
- [ ] `extractClass()` - class宣言
- [ ] `extractInterface()` - interface宣言
- [ ] `extractEnum()` - enum宣言
- [ ] `extractMethod()` - メソッド宣言
- [ ] `extractConstructor()` - コンストラクタ
- [ ] `extractImport()` - import文
- [ ] `extractInheritance()` - extends/implements
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

**Test Cases**:
```java
package com.example;
import java.util.List;
public class MyClass extends Base implements Runnable {
    public MyClass() {}
    public void run() {}
}
interface Service { void execute(); }
enum Status { ACTIVE, INACTIVE }
```

**Acceptance Criteria**:
- Java構文要素が正しくEntity/Relationに変換される
- 継承関係が正しく抽出される

---

### 2.3 P1言語タスク（High）

#### TSK-CG-020: PHP言語エクストラクター実装
**Design**: DES-CG-PHP
**Requirement**: REQ-CG-MULTILANG-004
**Priority**: P1 (High)
**Estimate**: 1.5時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/php.ts` 作成
- [ ] `PHPExtractor` クラス実装
- [ ] class, interface, trait抽出
- [ ] function, method抽出
- [ ] namespace, use抽出
- [ ] extends/implements関係
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-021: C#言語エクストラクター実装
**Design**: DES-CG-CSHARP
**Requirement**: REQ-CG-MULTILANG-005
**Priority**: P1 (High)
**Estimate**: 1.5時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/csharp.ts` 作成
- [ ] `CSharpExtractor` クラス実装
- [ ] class, interface, struct, enum抽出
- [ ] method, property抽出
- [ ] namespace, using抽出
- [ ] 継承関係抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-022: C言語エクストラクター実装
**Design**: DES-CG-C
**Requirement**: REQ-CG-MULTILANG-006
**Priority**: P1 (High)
**Estimate**: 1.5時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/c.ts` 作成
- [ ] `CExtractor` クラス実装
- [ ] function抽出
- [ ] struct, enum, typedef抽出
- [ ] #include抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-023: C++言語エクストラクター実装
**Design**: DES-CG-CPP
**Requirement**: REQ-CG-MULTILANG-007
**Priority**: P1 (High)
**Estimate**: 1.5時間
**Dependencies**: TSK-CG-022

**Subtasks**:
- [ ] `extractors/cpp.ts` 作成
- [ ] `CppExtractor` クラス実装（CExtractor拡張）
- [ ] class, namespace抽出追加
- [ ] method抽出追加
- [ ] テンプレートクラス対応
- [ ] 継承関係抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-024: Ruby言語エクストラクター実装
**Design**: DES-CG-RUBY
**Requirement**: REQ-CG-MULTILANG-008
**Priority**: P1 (High)
**Estimate**: 1.5時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/ruby.ts` 作成
- [ ] `RubyExtractor` クラス実装
- [ ] class, module抽出
- [ ] method, singleton_method抽出
- [ ] require/require_relative抽出
- [ ] 継承関係抽出
- [ ] include/extend関係抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

### 2.4 P2言語タスク（Medium）

#### TSK-CG-030: HCL/Terraform言語エクストラクター実装
**Design**: DES-CG-HCL
**Requirement**: REQ-CG-MULTILANG-009
**Priority**: P2 (Medium)
**Estimate**: 1時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/hcl.ts` 作成
- [ ] `HCLExtractor` クラス実装
- [ ] resource, data抽出
- [ ] variable, output抽出
- [ ] module, provider, locals抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-031: Kotlin言語エクストラクター実装
**Design**: DES-CG-KOTLIN
**Requirement**: REQ-CG-MULTILANG-010
**Priority**: P2 (Medium)
**Estimate**: 1時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/kotlin.ts` 作成
- [ ] `KotlinExtractor` クラス実装
- [ ] class, interface, object抽出
- [ ] fun, property抽出
- [ ] import抽出
- [ ] 継承関係抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-032: Swift言語エクストラクター実装
**Design**: DES-CG-SWIFT
**Requirement**: REQ-CG-MULTILANG-011
**Priority**: P2 (Medium)
**Estimate**: 1時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/swift.ts` 作成
- [ ] `SwiftExtractor` クラス実装
- [ ] class, struct, protocol抽出
- [ ] func, extension抽出
- [ ] import抽出
- [ ] 継承関係抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-033: Scala言語エクストラクター実装
**Design**: DES-CG-SCALA
**Requirement**: REQ-CG-MULTILANG-012
**Priority**: P2 (Medium)
**Estimate**: 1時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/scala.ts` 作成
- [ ] `ScalaExtractor` クラス実装
- [ ] class, trait, object抽出
- [ ] def抽出
- [ ] import抽出
- [ ] extends/with関係抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

#### TSK-CG-034: Lua言語エクストラクター実装
**Design**: DES-CG-LUA
**Requirement**: REQ-CG-MULTILANG-013
**Priority**: P2 (Medium)
**Estimate**: 1時間
**Dependencies**: TSK-CG-001, TSK-CG-002

**Subtasks**:
- [ ] `extractors/lua.ts` 作成
- [ ] `LuaExtractor` クラス実装
- [ ] function, local function抽出
- [ ] テーブルメソッド抽出
- [ ] require抽出
- [ ] レジストリへの登録
- [ ] ユニットテスト作成

---

### 2.5 テストタスク

#### TSK-CG-040: ユニットテスト整備
**Priority**: P0 (Critical)
**Estimate**: 2時間
**Dependencies**: TSK-CG-010〜034

**Description**:
各言語エクストラクターのユニットテストを整備する。

**Subtasks**:
- [ ] `test/extractors/` ディレクトリ作成
- [ ] 各言語のテストファイル作成
  - [ ] rust.spec.ts
  - [ ] go.spec.ts
  - [ ] java.spec.ts
  - [ ] php.spec.ts
  - [ ] csharp.spec.ts
  - [ ] c.spec.ts
  - [ ] cpp.spec.ts
  - [ ] ruby.spec.ts
  - [ ] hcl.spec.ts
  - [ ] kotlin.spec.ts
  - [ ] swift.spec.ts
  - [ ] scala.spec.ts
  - [ ] lua.spec.ts
- [ ] フィクスチャファイル作成

**Acceptance Criteria**:
- 各言語で最低5テストケース
- カバレッジ80%以上

---

#### TSK-CG-041: 統合テスト作成
**Priority**: P1 (High)
**Estimate**: 1.5時間
**Dependencies**: TSK-CG-040

**Description**:
複数言語混在プロジェクトの統合テストを作成する。

**Subtasks**:
- [ ] マルチ言語プロジェクトフィクスチャ作成
- [ ] インデックス統合テスト
- [ ] クエリ統合テスト
- [ ] パフォーマンステスト（1000行/秒の確認）

**Acceptance Criteria**:
- 16言語混在プロジェクトが正常にインデックス可能
- パフォーマンス要件を満たす

---

#### TSK-CG-042: フォールバックテスト
**Priority**: P1 (High)
**Estimate**: 0.5時間
**Dependencies**: TSK-CG-003

**Description**:
tree-sitter grammar未インストール時のフォールバック動作をテストする。

**Subtasks**:
- [ ] grammar欠落時のテスト
- [ ] 警告メッセージの確認
- [ ] regex fallback動作確認

**Acceptance Criteria**:
- grammar未インストールでもエラーにならない
- フォールバックで基本的な抽出が動作

---

### 2.6 統合・リリースタスク

#### TSK-CG-050: package.json更新
**Priority**: P0 (Critical)
**Estimate**: 0.5時間
**Dependencies**: なし（並行可能）

**Description**:
optionalDependenciesにtree-sitter言語パッケージを追加する。

**Subtasks**:
- [ ] tree-sitter-rust追加
- [ ] tree-sitter-go追加
- [ ] tree-sitter-java追加
- [ ] tree-sitter-php追加
- [ ] tree-sitter-c-sharp追加
- [ ] tree-sitter-cpp追加
- [ ] tree-sitter-ruby追加
- [ ] tree-sitter-hcl追加
- [ ] tree-sitter-kotlin追加
- [ ] tree-sitter-swift追加
- [ ] tree-sitter-scala追加
- [ ] tree-sitter-lua追加

---

#### TSK-CG-051: バージョン更新
**Priority**: P0 (Critical)
**Estimate**: 1時間
**Dependencies**: TSK-CG-040, TSK-CG-041

**Description**:
v2.3.2としてバージョンを更新し、CHANGELOG作成。

**Subtasks**:
- [ ] 全package.jsonのバージョンを2.3.2に更新
- [ ] CHANGELOG.mdに変更内容追記
- [ ] README.md更新（対応言語一覧）
- [ ] docs/overview/MUSUBIX-CodeGraph.md更新

---

#### TSK-CG-052: リリース準備
**Priority**: P0 (Critical)
**Estimate**: 1時間
**Dependencies**: TSK-CG-051

**Description**:
npm publish前の最終確認とリリース。

**Subtasks**:
- [ ] 全テスト実行（npm test）
- [ ] ビルド確認（npm run build）
- [ ] lint確認（npm run lint）
- [ ] npm publish --dry-run
- [ ] git tag v2.3.2
- [ ] npm publish

---

## 3. 実行順序（依存関係グラフ）

```
TSK-CG-001 (BaseExtractor)
    │
    ▼
TSK-CG-002 (Registry)
    │
    ├──────────────────────────────────────────────────┐
    ▼                                                   │
TSK-CG-003 (AST Parser統合)                            │
    │                                                   │
    ├───────────────────────────────────────────────────┤
    │                                                   │
    ▼                                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│ P0言語（並行実行可能）                                               │
│ TSK-CG-010 (Rust) │ TSK-CG-011 (Go) │ TSK-CG-012 (Java)            │
└─────────────────────────────────────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────────────────────────────────────┐
│ P1言語（並行実行可能）                                               │
│ TSK-CG-020 (PHP) │ TSK-CG-021 (C#) │ TSK-CG-022 (C) │              │
│ TSK-CG-023 (C++) │ TSK-CG-024 (Ruby)                                │
└─────────────────────────────────────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────────────────────────────────────┐
│ P2言語（並行実行可能）                                               │
│ TSK-CG-030 (HCL) │ TSK-CG-031 (Kotlin) │ TSK-CG-032 (Swift) │      │
│ TSK-CG-033 (Scala) │ TSK-CG-034 (Lua)                               │
└─────────────────────────────────────────────────────────────────────┘
    │
    ▼
TSK-CG-040 (ユニットテスト)
    │
    ▼
TSK-CG-041 (統合テスト) ←── TSK-CG-042 (フォールバックテスト)
    │
    ▼
TSK-CG-051 (バージョン更新) ←── TSK-CG-050 (package.json)
    │
    ▼
TSK-CG-052 (リリース)
```

---

## 4. トレーサビリティマトリクス

| 要件ID | 設計ID | タスクID | 状態 |
|--------|--------|----------|------|
| REQ-CG-MULTILANG-001 | DES-CG-RUST | TSK-CG-010 | 待機 |
| REQ-CG-MULTILANG-002 | DES-CG-GO | TSK-CG-011 | 待機 |
| REQ-CG-MULTILANG-003 | DES-CG-JAVA | TSK-CG-012 | 待機 |
| REQ-CG-MULTILANG-004 | DES-CG-PHP | TSK-CG-020 | 待機 |
| REQ-CG-MULTILANG-005 | DES-CG-CSHARP | TSK-CG-021 | 待機 |
| REQ-CG-MULTILANG-006 | DES-CG-C | TSK-CG-022 | 待機 |
| REQ-CG-MULTILANG-007 | DES-CG-CPP | TSK-CG-023 | 待機 |
| REQ-CG-MULTILANG-008 | DES-CG-RUBY | TSK-CG-024 | 待機 |
| REQ-CG-MULTILANG-009 | DES-CG-HCL | TSK-CG-030 | 待機 |
| REQ-CG-MULTILANG-010 | DES-CG-KOTLIN | TSK-CG-031 | 待機 |
| REQ-CG-MULTILANG-011 | DES-CG-SWIFT | TSK-CG-032 | 待機 |
| REQ-CG-MULTILANG-012 | DES-CG-SCALA | TSK-CG-033 | 待機 |
| REQ-CG-MULTILANG-013 | DES-CG-LUA | TSK-CG-034 | 待機 |
| REQ-CG-MULTILANG-NFR-001 | DES-CG-PARSER | TSK-CG-041 | 待機 |
| REQ-CG-MULTILANG-NFR-002 | DES-CG-PARSER | TSK-CG-042 | 待機 |
| REQ-CG-MULTILANG-NFR-003 | DES-CG-REGISTRY | TSK-CG-002 | 待機 |

---

## 5. 変更履歴

| バージョン | 日付 | 変更内容 |
|-----------|------|----------|
| 1.0.0 | 2026-01-09 | 初版作成 |
