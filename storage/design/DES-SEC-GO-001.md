# 設計書: Go言語セキュリティエクストラクター

**Document ID**: DES-SEC-GO-001  
**Version**: 1.0.0  
**Created**: 2026-01-12  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft (レビュー待ち)  
**Requirements**: REQ-SEC-GO-001

---

## 1. 概要

Go言語向けセキュリティエクストラクター（GoExtractor）の設計を定義する。BaseExtractor抽象クラスを継承し、Ruby/Rust Extractorと同一のインターフェースを提供する。

---

## 2. アーキテクチャ

### 2.1 クラス階層

```
BaseExtractor (abstract)
├── RubyExtractor (v3.0.13)
├── RustExtractor (v3.0.13)
└── GoExtractor (v3.0.14 NEW!)
```

### 2.2 コンポーネント図

```
┌─────────────────────────────────────────────────────────┐
│                     GoExtractor                          │
├─────────────────────────────────────────────────────────┤
│  + language: 'go'                                        │
│  + extensions: ['.go']                                   │
│  - parser: TreeSitterParser | null                       │
│  - nodeIdCounter: number                                 │
│  - blockIdCounter: number                                │
├─────────────────────────────────────────────────────────┤
│  + extract(source, filePath): Promise<ExtractionResult>  │
│  + supports(filePath): boolean                           │
│  + getFrameworkModels(): FrameworkModel[]                │
│  # buildAST(source, filePath): Promise<ASTBuildResult>   │
│  # buildDFG(astNodes, astEdges, models): Promise<DFG>    │
│  # buildCFG(astNodes, astEdges): Promise<CFG>            │
│  # extractSymbols(astNodes): Promise<SymbolTable>        │
│  - initParser(): Promise<void>                           │
│  - convertTreeSitterNode(...): ASTNode                   │
│  - extractNodeProperties(node): Record<string, unknown>  │
│  - createFallbackAST(...): ASTNode                       │
│  - isExported(name): boolean                             │
└─────────────────────────────────────────────────────────┘
```

### 2.3 依存関係

```
go-extractor.ts
├── base-extractor.ts (継承)
│   ├── ASTNode, ASTEdge
│   ├── DFGNode, DFGEdge, DataFlowGraph
│   ├── BasicBlock, CFGEdge, ControlFlowGraph
│   ├── Symbol, FunctionSymbol, ClassSymbol, SymbolTable
│   ├── FrameworkModel, FrameworkSource, FrameworkSink, FrameworkSanitizer
│   └── ExtractionResult
└── tree-sitter-go (optional peer dependency)
```

---

## 3. 詳細設計

### 3.1 GoExtractorクラス

```typescript
/**
 * Go Language Extractor
 * @trace REQ-SEC-GO-001
 */
export class GoExtractor extends BaseExtractor {
  readonly language: SupportedLanguage = 'go';
  readonly extensions: string[] = ['.go'];

  private parser: TreeSitterParser | null = null;
  private nodeIdCounter = 0;
  private blockIdCounter = 0;

  /**
   * Get framework models for Go
   * @trace REQ-SEC-GO-006
   */
  getFrameworkModels(): FrameworkModel[];

  /**
   * Build AST from source code
   * @trace REQ-SEC-GO-002
   */
  protected async buildAST(
    source: string,
    filePath: string
  ): Promise<{ ast: ASTNode; astNodes: Map<string, ASTNode>; astEdges: ASTEdge[] }>;

  /**
   * Build Data Flow Graph
   * @trace REQ-SEC-GO-003, REQ-SEC-GO-004, REQ-SEC-GO-005
   */
  protected async buildDFG(
    astNodes: Map<string, ASTNode>,
    astEdges: ASTEdge[],
    frameworkModels: FrameworkModel[]
  ): Promise<DataFlowGraph>;

  /**
   * Build Control Flow Graph
   * @trace REQ-SEC-GO-007
   */
  protected async buildCFG(
    astNodes: Map<string, ASTNode>,
    astEdges: ASTEdge[]
  ): Promise<ControlFlowGraph>;

  /**
   * Extract symbols from AST
   * @trace REQ-SEC-GO-008
   */
  protected async extractSymbols(
    astNodes: Map<string, ASTNode>
  ): Promise<SymbolTable>;
}
```

### 3.2 フレームワークモデル設計

#### 3.2.1 net/http モデル

```typescript
{
  name: 'net/http',
  languages: ['go'],
  sources: [
    { pattern: /r\.URL\.Query\(\)/, type: 'http_query', taintLabel: 'user_input' },
    { pattern: /r\.FormValue\(/, type: 'http_form', taintLabel: 'user_input' },
    { pattern: /r\.PostFormValue\(/, type: 'http_form', taintLabel: 'user_input' },
    { pattern: /r\.Header\.Get\(/, type: 'http_header', taintLabel: 'user_input' },
    { pattern: /r\.Body/, type: 'http_body', taintLabel: 'user_input' },
    { pattern: /r\.Cookie\(/, type: 'cookie', taintLabel: 'user_input' },
  ],
  sinks: [
    { pattern: /w\.Write\(/, type: 'response', vulnerabilityType: 'xss', severity: 'high' },
    { pattern: /fmt\.Fprintf\(w,/, type: 'response', vulnerabilityType: 'xss', severity: 'high' },
    { pattern: /http\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
  ],
  sanitizers: [
    { pattern: /html\.EscapeString\(/, sanitizes: ['xss'] },
    { pattern: /template\.HTMLEscapeString\(/, sanitizes: ['xss'] },
  ],
}
```

#### 3.2.2 database/sql モデル

```typescript
{
  name: 'database/sql',
  languages: ['go'],
  sources: [],
  sinks: [
    { pattern: /db\.Query\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    { pattern: /db\.Exec\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    { pattern: /db\.QueryRow\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    { pattern: /tx\.Query\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    { pattern: /tx\.Exec\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
  ],
  sanitizers: [
    { pattern: /db\.Prepare\(/, sanitizes: ['sql_injection'] },
    { pattern: /\?/, sanitizes: ['sql_injection'] }, // Placeholder
  ],
}
```

#### 3.2.3 os/exec モデル

```typescript
{
  name: 'os/exec',
  languages: ['go'],
  sources: [
    { pattern: /os\.Args/, type: 'cli_args', taintLabel: 'user_input' },
    { pattern: /os\.Getenv\(/, type: 'env', taintLabel: 'env_input' },
  ],
  sinks: [
    { pattern: /exec\.Command\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
    { pattern: /exec\.CommandContext\(/, type: 'command', vulnerabilityType: 'command_injection', severity: 'critical' },
  ],
  sanitizers: [],
}
```

#### 3.2.4 os (ファイル操作) モデル

```typescript
{
  name: 'os',
  languages: ['go'],
  sources: [],
  sinks: [
    { pattern: /os\.Open\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    { pattern: /os\.OpenFile\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    { pattern: /os\.ReadFile\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    { pattern: /os\.WriteFile\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    { pattern: /os\.Remove\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'high' },
    { pattern: /os\.Mkdir\(/, type: 'file', vulnerabilityType: 'path_traversal', severity: 'medium' },
  ],
  sanitizers: [
    { pattern: /filepath\.Clean\(/, sanitizes: ['path_traversal'] },
    { pattern: /filepath\.Abs\(/, sanitizes: ['path_traversal'] },
  ],
}
```

#### 3.2.5 encoding/xml モデル

```typescript
{
  name: 'encoding/xml',
  languages: ['go'],
  sources: [],
  sinks: [
    { pattern: /xml\.Unmarshal\(/, type: 'xml', vulnerabilityType: 'xxe', severity: 'high' },
    { pattern: /xml\.NewDecoder\(/, type: 'xml', vulnerabilityType: 'xxe', severity: 'high' },
  ],
  sanitizers: [],
}
```

#### 3.2.6 Gin フレームワークモデル

```typescript
{
  name: 'Gin',
  languages: ['go'],
  sources: [
    { pattern: /c\.Query\(/, type: 'http_query', taintLabel: 'user_input' },
    { pattern: /c\.Param\(/, type: 'http_param', taintLabel: 'user_input' },
    { pattern: /c\.PostForm\(/, type: 'http_form', taintLabel: 'user_input' },
    { pattern: /c\.GetHeader\(/, type: 'http_header', taintLabel: 'user_input' },
    { pattern: /c\.ShouldBind/, type: 'binding', taintLabel: 'user_input' },
    { pattern: /c\.BindJSON\(/, type: 'json_binding', taintLabel: 'user_input' },
  ],
  sinks: [
    { pattern: /c\.String\(/, type: 'response', vulnerabilityType: 'xss', severity: 'high' },
    { pattern: /c\.HTML\(/, type: 'response', vulnerabilityType: 'xss', severity: 'high' },
    { pattern: /c\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
  ],
  sanitizers: [],
}
```

#### 3.2.7 Echo フレームワークモデル

```typescript
{
  name: 'Echo',
  languages: ['go'],
  sources: [
    { pattern: /c\.QueryParam\(/, type: 'http_query', taintLabel: 'user_input' },
    { pattern: /c\.Param\(/, type: 'http_param', taintLabel: 'user_input' },
    { pattern: /c\.FormValue\(/, type: 'http_form', taintLabel: 'user_input' },
    { pattern: /c\.Request\(\)\.Header\.Get\(/, type: 'http_header', taintLabel: 'user_input' },
    { pattern: /c\.Bind\(/, type: 'binding', taintLabel: 'user_input' },
  ],
  sinks: [
    { pattern: /c\.String\(/, type: 'response', vulnerabilityType: 'xss', severity: 'high' },
    { pattern: /c\.HTML\(/, type: 'response', vulnerabilityType: 'xss', severity: 'high' },
    { pattern: /c\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
  ],
  sanitizers: [],
}
```

#### 3.2.8 Fiber フレームワークモデル

```typescript
{
  name: 'Fiber',
  languages: ['go'],
  sources: [
    { pattern: /c\.Query\(/, type: 'http_query', taintLabel: 'user_input' },
    { pattern: /c\.Params\(/, type: 'http_param', taintLabel: 'user_input' },
    { pattern: /c\.FormValue\(/, type: 'http_form', taintLabel: 'user_input' },
    { pattern: /c\.Get\(/, type: 'http_header', taintLabel: 'user_input' },
    { pattern: /c\.BodyParser\(/, type: 'body_parser', taintLabel: 'user_input' },
  ],
  sinks: [
    { pattern: /c\.SendString\(/, type: 'response', vulnerabilityType: 'xss', severity: 'high' },
    { pattern: /c\.Redirect\(/, type: 'redirect', vulnerabilityType: 'open_redirect', severity: 'medium' },
  ],
  sanitizers: [],
}
```

#### 3.2.9 GORM モデル

```typescript
{
  name: 'GORM',
  languages: ['go'],
  sources: [],
  sinks: [
    { pattern: /\.Raw\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    { pattern: /\.Exec\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'critical' },
    { pattern: /\.Where\([^)]*\+/, type: 'sql', vulnerabilityType: 'sql_injection', severity: 'high' },
  ],
  sanitizers: [
    { pattern: /\.Where\([^,]+,/, sanitizes: ['sql_injection'] }, // Parameterized
  ],
}
```

#### 3.2.10 SSRF モデル

```typescript
{
  name: 'Go SSRF',
  languages: ['go'],
  sources: [],
  sinks: [
    { pattern: /http\.Get\(/, type: 'http_request', vulnerabilityType: 'ssrf', severity: 'high' },
    { pattern: /http\.Post\(/, type: 'http_request', vulnerabilityType: 'ssrf', severity: 'high' },
    { pattern: /http\.NewRequest\(/, type: 'http_request', vulnerabilityType: 'ssrf', severity: 'high' },
    { pattern: /client\.Do\(/, type: 'http_request', vulnerabilityType: 'ssrf', severity: 'high' },
  ],
  sanitizers: [
    { pattern: /url\.Parse\(/, sanitizes: ['ssrf'] },
  ],
}
```

### 3.3 AST構築フロー

```
Source Code (.go)
       │
       ▼
┌──────────────┐
│ initParser() │ ── tree-sitter-go利用可能？
└──────────────┘
       │
       ├─── Yes ─────────────────────┐
       │                             ▼
       │                   ┌─────────────────────┐
       │                   │ parser.parse(code)  │
       │                   └─────────────────────┘
       │                             │
       │                             ▼
       │                   ┌─────────────────────┐
       │                   │ convertTreeSitter   │
       │                   │ Node()              │
       │                   └─────────────────────┘
       │                             │
       ▼                             │
┌──────────────┐                     │
│ Fallback AST │ ◄───── No ──────────┤
└──────────────┘                     │
       │                             │
       ▼                             ▼
┌──────────────────────────────────────┐
│ { ast, astNodes: Map, astEdges: [] } │
└──────────────────────────────────────┘
```

### 3.4 Go固有AST ノードタイプ

| Go構文 | ASTノードタイプ | プロパティ |
|--------|----------------|-----------|
| `package main` | `package_clause` | `name` |
| `import "fmt"` | `import_declaration` | `path`, `alias` |
| `func main()` | `function_declaration` | `name`, `parameters`, `returnType` |
| `func (r *Receiver) Method()` | `method_declaration` | `name`, `receiver`, `parameters` |
| `type T struct{}` | `type_declaration` | `name`, `kind` |
| `var x = 1` | `var_declaration` | `name`, `type`, `value` |
| `x := 1` | `short_var_declaration` | `names`, `values` |
| `if` | `if_statement` | `condition` |
| `for` | `for_statement` | `init`, `condition`, `post` |
| `switch` | `switch_statement` | `expression` |
| `select` | `select_statement` | - |
| `go func()` | `go_statement` | - |
| `defer func()` | `defer_statement` | - |
| `return` | `return_statement` | `values` |
| `func(){}` | `call_expression` | `function`, `arguments` |

### 3.5 Symbol Table エクスポート判定

Go言語では、識別子が大文字で始まる場合にエクスポートされる。

```typescript
/**
 * Check if Go identifier is exported
 * @trace REQ-SEC-GO-008
 */
private isExported(name: string): boolean {
  return /^[A-Z]/.test(name);
}
```

---

## 4. インターフェース設計

### 4.1 index.ts エクスポート追加

```typescript
// packages/security/src/extractors/index.ts

// 既存
export { RubyExtractor, createRubyExtractor } from './ruby-extractor.js';
export { RustExtractor, createRustExtractor } from './rust-extractor.js';

// 追加
export { GoExtractor, createGoExtractor } from './go-extractor.js';

// createExtractor factory 更新
export function createExtractor(language: SupportedLanguage): BaseExtractor | null {
  switch (language) {
    case 'ruby':
      return new RubyExtractor();
    case 'rust':
      return new RustExtractor();
    case 'go':          // 追加
      return new GoExtractor();
    default:
      return null;
  }
}

// getSupportedLanguages 更新
export function getSupportedLanguages(): SupportedLanguage[] {
  return ['typescript', 'javascript', 'python', 'php', 'go', 'java', 'ruby', 'rust'];
}
```

---

## 5. エラーハンドリング

| エラー種別 | 処理 |
|-----------|------|
| tree-sitter-go未インストール | フォールバックASTを生成、警告ログ |
| パース失敗 | ExtractionError追加、空ASTで継続 |
| 不正なノードタイプ | スキップして継続 |
| メモリ不足 | 早期終了、部分結果を返却 |

---

## 6. テスト設計

### 6.1 テストケース一覧

| テストID | カテゴリ | 説明 |
|---------|---------|------|
| GO-TEST-001 | コンストラクタ | GoExtractor生成 |
| GO-TEST-002 | コンストラクタ | createGoExtractor factory |
| GO-TEST-003 | supports | `.go`ファイル判定 |
| GO-TEST-004 | getFrameworkModels | 10モデル返却 |
| GO-TEST-005 | extract | シンプルGoコード解析 |
| GO-TEST-006 | ソース検出 | r.FormValue() 検出 |
| GO-TEST-007 | ソース検出 | os.Args 検出 |
| GO-TEST-008 | シンク検出 | db.Query() SQL injection |
| GO-TEST-009 | シンク検出 | exec.Command() command injection |
| GO-TEST-010 | シンク検出 | os.Open() path traversal |
| GO-TEST-011 | サニタイザー | filepath.Clean() |
| GO-TEST-012 | CFG | if文 |
| GO-TEST-013 | CFG | for文 |
| GO-TEST-014 | Symbols | 関数抽出 |
| GO-TEST-015 | Symbols | エクスポート判定 |
| GO-TEST-016 | Gin | c.Query() ソース |
| GO-TEST-017 | GORM | Raw() シンク |

---

## 7. トレーサビリティマトリクス

| 要件ID | 設計セクション | 実装ファイル |
|--------|---------------|-------------|
| REQ-SEC-GO-001 | 3.1 | go-extractor.ts |
| REQ-SEC-GO-002 | 3.3 | go-extractor.ts initParser() |
| REQ-SEC-GO-003 | 3.2.1-3.2.10 sources | go-extractor.ts buildDFG() |
| REQ-SEC-GO-004 | 3.2.1-3.2.10 sinks | go-extractor.ts buildDFG() |
| REQ-SEC-GO-005 | 3.2.1-3.2.10 sanitizers | go-extractor.ts buildDFG() |
| REQ-SEC-GO-006 | 3.2 | go-extractor.ts getFrameworkModels() |
| REQ-SEC-GO-007 | 3.4 | go-extractor.ts buildCFG() |
| REQ-SEC-GO-008 | 3.5 | go-extractor.ts extractSymbols() |

---

## 8. 成果物

| ファイル | 説明 |
|---------|------|
| `packages/security/src/extractors/go-extractor.ts` | GoExtractor実装 (~700行) |
| `packages/security/tests/go-extractor.test.ts` | テスト (~200行) |
| `packages/security/src/extractors/index.ts` | エクスポート更新 |

---

**Document End**
