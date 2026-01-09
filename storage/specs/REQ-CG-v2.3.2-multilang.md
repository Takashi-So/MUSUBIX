# MUSUBIX v2.3.2 要件定義書

## 多言語AST解析拡張（CodeGraph Multi-Language Support）

**Document ID**: REQ-CG-MULTILANG
**Version**: 2.3.2
**Status**: Draft
**Created**: 2026-01-09
**Author**: AI Agent (Claude)
**Related**: CodeGraphMCPServer v0.8.0

---

## 1. 概要

### 1.1 背景

現在のMUSUBIX CodeGraphパッケージ（@nahisaho/musubix-codegraph）は、型定義（types.ts）では16言語を定義しているが、AST解析の実装はTypeScript/JavaScript/Pythonのみが機能している。

CodeGraphMCPServer（https://github.com/nahisaho/CodeGraphMCPServer）v0.8.0では、16言語のTree-sitterベースAST解析を実装済みであり、MUSUBIXにもこの機能を移植する。

### 1.2 目的

MUSUBIXのCodeGraphパッケージにCodeGraphMCPServerで対応している全16言語のAST解析機能を追加し、多言語コードベースの分析を可能にする。

---

## 2. 対象言語一覧

CodeGraphMCPServer v0.8.0で対応している16言語:

| No. | 言語 | 拡張子 | tree-sitter-* | 優先度 |
|-----|------|--------|---------------|--------|
| 1 | Python | .py, .pyi | tree-sitter-python | P0 (既存) |
| 2 | TypeScript | .ts, .tsx | tree-sitter-typescript | P0 (既存) |
| 3 | JavaScript | .js, .jsx, .mjs, .cjs | tree-sitter-javascript | P0 (既存) |
| 4 | Rust | .rs | tree-sitter-rust | P0 |
| 5 | Go | .go | tree-sitter-go | P0 |
| 6 | Java | .java | tree-sitter-java | P0 |
| 7 | PHP | .php | tree-sitter-php | P1 |
| 8 | C# | .cs | tree-sitter-c-sharp | P1 |
| 9 | C | .c, .h | tree-sitter-c (via cpp) | P1 |
| 10 | C++ | .cpp, .hpp, .cc, .cxx, .hxx | tree-sitter-cpp | P1 |
| 11 | Ruby | .rb, .rake, .gemspec | tree-sitter-ruby | P1 |
| 12 | HCL/Terraform | .tf, .hcl, .tfvars | tree-sitter-hcl | P2 |
| 13 | Kotlin | .kt, .kts | tree-sitter-kotlin | P2 |
| 14 | Swift | .swift | tree-sitter-swift | P2 |
| 15 | Scala | .scala, .sc | tree-sitter-scala | P2 |
| 16 | Lua | .lua | tree-sitter-lua | P2 |

---

## 3. 機能要件（EARS形式）

### 3.1 AST解析基盤

#### REQ-CG-MULTILANG-001: Rust言語サポート
**Type**: Functional
**Priority**: P0 (Critical)

> WHEN the system parses Rust source files (.rs), THE CodeGraph Parser SHALL extract functions, structs, enums, traits, impl blocks, and modules as entities.

**Acceptance Criteria**:
1. `fn` declarations → Function entity
2. `struct` declarations → Struct entity
3. `enum` declarations → Enum entity
4. `trait` declarations → Trait/Interface entity
5. `impl` blocks → Impl entity
6. `mod` declarations → Module entity
7. `use` statements → Import relations
8. Method calls → Call relations

---

#### REQ-CG-MULTILANG-002: Go言語サポート
**Type**: Functional
**Priority**: P0 (Critical)

> WHEN the system parses Go source files (.go), THE CodeGraph Parser SHALL extract functions, structs, interfaces, methods, and packages as entities.

**Acceptance Criteria**:
1. `func` declarations → Function entity
2. `type X struct` → Struct entity
3. `type X interface` → Interface entity
4. `func (r Receiver) Method()` → Method entity
5. `package` statement → Module entity
6. `import` statements → Import relations

---

#### REQ-CG-MULTILANG-003: Java言語サポート
**Type**: Functional
**Priority**: P0 (Critical)

> WHEN the system parses Java source files (.java), THE CodeGraph Parser SHALL extract classes, interfaces, methods, fields, and enums as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `interface X` → Interface entity
3. `enum X` → Enum entity
4. Method declarations → Method entity
5. Constructor declarations → Method entity
6. Field declarations → Variable entity (optional)
7. `import` statements → Import relations
8. `extends/implements` → Inheritance relations

---

#### REQ-CG-MULTILANG-004: PHP言語サポート
**Type**: Functional
**Priority**: P1 (High)

> WHEN the system parses PHP source files (.php), THE CodeGraph Parser SHALL extract classes, interfaces, traits, methods, and functions as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `interface X` → Interface entity
3. `trait X` → Trait entity
4. Method declarations → Method entity
5. Function declarations → Function entity
6. `namespace` declarations → Namespace entity
7. `use` statements → Import relations
8. `extends/implements` → Inheritance relations

---

#### REQ-CG-MULTILANG-005: C#言語サポート
**Type**: Functional
**Priority**: P1 (High)

> WHEN the system parses C# source files (.cs), THE CodeGraph Parser SHALL extract classes, interfaces, structs, enums, methods, and properties as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `interface X` → Interface entity
3. `struct X` → Struct entity
4. `enum X` → Enum entity
5. Method declarations → Method entity
6. Property declarations → Property entity
7. `namespace` declarations → Namespace entity
8. `using` directives → Import relations
9. `: BaseClass/Interface` → Inheritance relations

---

#### REQ-CG-MULTILANG-006: C言語サポート
**Type**: Functional
**Priority**: P1 (High)

> WHEN the system parses C source files (.c, .h), THE CodeGraph Parser SHALL extract functions, structs, enums, and typedefs as entities.

**Acceptance Criteria**:
1. Function declarations → Function entity
2. `struct` declarations → Struct entity
3. `enum` declarations → Enum entity
4. `typedef` → Type entity
5. `#include` directives → Import relations

---

#### REQ-CG-MULTILANG-007: C++言語サポート
**Type**: Functional
**Priority**: P1 (High)

> WHEN the system parses C++ source files (.cpp, .hpp, .cc, .cxx), THE CodeGraph Parser SHALL extract classes, structs, functions, methods, and namespaces as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `struct X` → Struct entity
3. Function declarations → Function entity
4. Method declarations → Method entity
5. `namespace` declarations → Namespace entity
6. `#include` directives → Import relations
7. `: public Base` → Inheritance relations
8. Template classes → Class entity with template annotation

---

#### REQ-CG-MULTILANG-008: Ruby言語サポート
**Type**: Functional
**Priority**: P1 (High)

> WHEN the system parses Ruby source files (.rb, .rake, .gemspec), THE CodeGraph Parser SHALL extract classes, modules, methods, and singleton methods as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `module X` → Module entity
3. `def method` → Method entity
4. `def self.method` → Method entity (static)
5. `require/require_relative` → Import relations
6. `< BaseClass` → Inheritance relations
7. `include/extend` → Module inclusion relations

---

#### REQ-CG-MULTILANG-009: HCL/Terraform言語サポート
**Type**: Functional
**Priority**: P2 (Medium)

> WHEN the system parses HCL/Terraform source files (.tf, .hcl), THE CodeGraph Parser SHALL extract resources, data sources, variables, outputs, and modules as entities.

**Acceptance Criteria**:
1. `resource "type" "name"` → Resource entity
2. `data "type" "name"` → Data entity
3. `variable "name"` → Variable entity
4. `output "name"` → Output entity
5. `module "name"` → Module entity
6. `provider "name"` → Provider entity
7. `locals` block → Local entity

---

#### REQ-CG-MULTILANG-010: Kotlin言語サポート
**Type**: Functional
**Priority**: P2 (Medium)

> WHEN the system parses Kotlin source files (.kt, .kts), THE CodeGraph Parser SHALL extract classes, interfaces, objects, functions, and properties as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `interface X` → Interface entity
3. `object X` → Object/Singleton entity
4. `fun name()` → Function entity
5. `val/var name` → Property entity
6. `import` statements → Import relations
7. `: BaseClass, Interface` → Inheritance relations

---

#### REQ-CG-MULTILANG-011: Swift言語サポート
**Type**: Functional
**Priority**: P2 (Medium)

> WHEN the system parses Swift source files (.swift), THE CodeGraph Parser SHALL extract classes, structs, protocols, functions, and extensions as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `struct X` → Struct entity
3. `protocol X` → Protocol/Interface entity
4. `func name()` → Function entity
5. `extension X` → Extension entity
6. `import` statements → Import relations
7. `: BaseClass, Protocol` → Inheritance relations

---

#### REQ-CG-MULTILANG-012: Scala言語サポート
**Type**: Functional
**Priority**: P2 (Medium)

> WHEN the system parses Scala source files (.scala, .sc), THE CodeGraph Parser SHALL extract classes, traits, objects, and functions as entities.

**Acceptance Criteria**:
1. `class X` → Class entity
2. `trait X` → Trait/Interface entity
3. `object X` → Object/Singleton entity
4. `def name` → Function/Method entity
5. `import` statements → Import relations
6. `extends/with` → Inheritance relations

---

#### REQ-CG-MULTILANG-013: Lua言語サポート
**Type**: Functional
**Priority**: P2 (Medium)

> WHEN the system parses Lua source files (.lua), THE CodeGraph Parser SHALL extract functions, local functions, and table assignments as entities.

**Acceptance Criteria**:
1. `function name()` → Function entity
2. `local function name()` → Function entity (local)
3. `X.method = function()` → Method entity
4. `require()` → Import relations

---

### 3.2 非機能要件

#### REQ-CG-MULTILANG-NFR-001: パース性能
**Type**: Non-Functional (Performance)
**Priority**: P0 (Critical)

> THE CodeGraph Parser SHALL parse files at a minimum rate of 1,000 lines per second for each supported language.

**Acceptance Criteria**:
1. 10,000行ファイル: 10秒以内
2. 100,000行プロジェクト: 100秒以内
3. メモリ使用量: 1GBプロジェクトで2GB未満

---

#### REQ-CG-MULTILANG-NFR-002: オプショナル依存関係
**Type**: Non-Functional (Installation)
**Priority**: P0 (Critical)

> WHILE a tree-sitter grammar is not installed, THE CodeGraph Parser SHALL gracefully degrade to regex-based fallback parsing for that language.

**Acceptance Criteria**:
1. tree-sitterが利用不可でもシステムは起動
2. 欠落した言語に対してフォールバックパーサーを使用
3. エラーではなく警告を出力

---

#### REQ-CG-MULTILANG-NFR-003: 拡張性
**Type**: Non-Functional (Maintainability)
**Priority**: P1 (High)

> THE CodeGraph Parser architecture SHALL allow adding new language support without modifying core parsing logic.

**Acceptance Criteria**:
1. プラグイン/エクストラクター形式での言語追加
2. 言語設定のみで新言語登録可能
3. 新言語追加時のテスト自動生成

---

### 3.3 統合要件

#### REQ-CG-MULTILANG-INT-001: CLI統合
**Type**: Functional (Integration)
**Priority**: P0 (Critical)

> WHEN the user runs `npx musubix cg index <path>`, THE CLI SHALL automatically detect and parse all 16 supported languages in the specified directory.

**Acceptance Criteria**:
1. 拡張子による自動言語検出
2. 複数言語プロジェクトの統合インデックス
3. 言語別統計の出力

---

#### REQ-CG-MULTILANG-INT-002: MCP Server統合
**Type**: Functional (Integration)
**Priority**: P0 (Critical)

> WHEN CodeGraph tools are invoked via MCP Server, THE tools SHALL support all 16 languages for indexing, querying, and analysis operations.

**Acceptance Criteria**:
1. `codegraph_index` ツールで16言語対応
2. `codegraph_query` ツールで言語フィルタ対応
3. `codegraph_stats` ツールで言語別統計

---

## 4. 技術仕様

### 4.1 依存関係（package.json）

```json
{
  "dependencies": {
    "tree-sitter": "^0.21.0"
  },
  "optionalDependencies": {
    "tree-sitter-python": "^0.21.0",
    "tree-sitter-typescript": "^0.21.0",
    "tree-sitter-javascript": "^0.21.0",
    "tree-sitter-rust": "^0.21.0",
    "tree-sitter-go": "^0.21.0",
    "tree-sitter-java": "^0.21.0",
    "tree-sitter-php": "^0.23.0",
    "tree-sitter-c-sharp": "^0.21.0",
    "tree-sitter-cpp": "^0.22.0",
    "tree-sitter-ruby": "^0.21.0",
    "tree-sitter-hcl": "^0.1.0",
    "tree-sitter-kotlin": "^1.0.0",
    "tree-sitter-swift": "^0.0.1",
    "tree-sitter-scala": "^0.20.0",
    "tree-sitter-lua": "^0.1.0"
  }
}
```

### 4.2 ファイル構造

```
packages/codegraph/src/
├── parser/
│   ├── ast-parser.ts          # メインパーサー（更新）
│   ├── index.ts               # エクスポート
│   └── extractors/            # 言語別エクストラクター（NEW）
│       ├── base-extractor.ts  # 基底クラス
│       ├── python.ts          # Python (既存)
│       ├── typescript.ts      # TypeScript (既存)
│       ├── javascript.ts      # JavaScript (既存)
│       ├── rust.ts            # Rust (NEW)
│       ├── go.ts              # Go (NEW)
│       ├── java.ts            # Java (NEW)
│       ├── php.ts             # PHP (NEW)
│       ├── csharp.ts          # C# (NEW)
│       ├── c.ts               # C (NEW)
│       ├── cpp.ts             # C++ (NEW)
│       ├── ruby.ts            # Ruby (NEW)
│       ├── hcl.ts             # HCL/Terraform (NEW)
│       ├── kotlin.ts          # Kotlin (NEW)
│       ├── swift.ts           # Swift (NEW)
│       ├── scala.ts           # Scala (NEW)
│       └── lua.ts             # Lua (NEW)
└── types.ts                   # 型定義（更新済み）
```

---

## 5. トレーサビリティ

### 5.1 要件→設計マッピング

| 要件ID | 設計ID | 説明 |
|--------|--------|------|
| REQ-CG-MULTILANG-001 | DES-CG-RUST | Rust言語エクストラクター |
| REQ-CG-MULTILANG-002 | DES-CG-GO | Go言語エクストラクター |
| REQ-CG-MULTILANG-003 | DES-CG-JAVA | Java言語エクストラクター |
| REQ-CG-MULTILANG-004 | DES-CG-PHP | PHP言語エクストラクター |
| REQ-CG-MULTILANG-005 | DES-CG-CSHARP | C#言語エクストラクター |
| REQ-CG-MULTILANG-006 | DES-CG-C | C言語エクストラクター |
| REQ-CG-MULTILANG-007 | DES-CG-CPP | C++言語エクストラクター |
| REQ-CG-MULTILANG-008 | DES-CG-RUBY | Ruby言語エクストラクター |
| REQ-CG-MULTILANG-009 | DES-CG-HCL | HCL言語エクストラクター |
| REQ-CG-MULTILANG-010 | DES-CG-KOTLIN | Kotlin言語エクストラクター |
| REQ-CG-MULTILANG-011 | DES-CG-SWIFT | Swift言語エクストラクター |
| REQ-CG-MULTILANG-012 | DES-CG-SCALA | Scala言語エクストラクター |
| REQ-CG-MULTILANG-013 | DES-CG-LUA | Lua言語エクストラクター |

---

## 6. リスク分析

| リスク | 影響 | 確率 | 対策 |
|--------|------|------|------|
| tree-sitter互換性 | High | Medium | Optional依存として実装、フォールバック用意 |
| パフォーマンス低下 | Medium | Low | 言語別ベンチマーク実施 |
| メモリ使用量増大 | Medium | Medium | 遅延初期化、使用言語のみロード |
| ネイティブモジュールビルド失敗 | High | Medium | プリビルドバイナリ利用、フォールバック |

---

## 7. 承認

| 役割 | 名前 | 日付 | 状態 |
|------|------|------|------|
| 作成者 | AI Agent (Claude) | 2026-01-09 | 完了 |
| レビュアー | - | - | 待機 |
| 承認者 | - | - | 待機 |

---

## 変更履歴

| バージョン | 日付 | 変更内容 |
|-----------|------|----------|
| 1.0.0 | 2026-01-09 | 初版作成 |
