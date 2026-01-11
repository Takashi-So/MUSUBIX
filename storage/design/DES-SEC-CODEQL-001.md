# 設計書: @nahisaho/musubix-security CodeQL同等機能強化

**Document ID**: DES-SEC-CODEQL-001  
**Version**: 1.0.0  
**Created**: 2026-01-12  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft (レビュー待ち)

---

## 1. トレーサビリティ

### 1.1 関連要件

| 要件ID | 要件名 | 設計コンポーネント |
|--------|--------|-------------------|
| REQ-SEC-LANG-001 | Go言語サポート | GoExtractor, GoScanner |
| REQ-SEC-LANG-002 | Java言語サポート | JavaExtractor, JavaScanner |
| REQ-SEC-LANG-003 | Ruby言語サポート | RubyExtractor, RubyScanner |
| REQ-SEC-LANG-004 | Rust言語サポート | RustExtractor, RustScanner |
| REQ-SEC-DB-001〜007 | コードデータベース | CodeDB, CodeDBBuilder, CodeDBQuery |
| REQ-SEC-MQL-001〜006 | クエリエンジン | MQLParser, MQLCompiler, MQLExecutor |
| REQ-SEC-CFG-001〜006 | 制御フローグラフ | CFGBuilder, CFGAnalyzer |
| REQ-SEC-DFG-001〜006 | データフロー解析 | DFGBuilder, TaintTracker |
| REQ-SEC-VAR-001〜004 | バリアント解析 | VariantAnalyzer |
| REQ-SEC-FW-001〜008 | フレームワーク認識 | FrameworkModels |
| REQ-SEC-RPT-001〜005 | レポーティング | SARIFGenerator |

---

## 2. C4モデル: Context

### 2.1 システムコンテキスト図

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           External Systems                                   │
└─────────────────────────────────────────────────────────────────────────────┘
        │                    │                    │                    │
        ▼                    ▼                    ▼                    ▼
┌───────────────┐   ┌───────────────┐   ┌───────────────┐   ┌───────────────┐
│   Developer   │   │  CI/CD System │   │   VS Code     │   │    GitHub     │
│   (User)      │   │ (GitHub       │   │  Extension    │   │    Code       │
│               │   │  Actions)     │   │               │   │    Scanning   │
└───────┬───────┘   └───────┬───────┘   └───────┬───────┘   └───────┬───────┘
        │                    │                    │                    │
        │    CLI/MCP         │    MCP/API         │    MCP             │   SARIF
        ▼                    ▼                    ▼                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                              │
│                    MUSUBIX Security System (v3.1.0+)                        │
│                                                                              │
│  ┌────────────────────────────────────────────────────────────────────┐    │
│  │                     Security Analysis Engine                        │    │
│  │  • Multi-language static analysis                                   │    │
│  │  • Taint tracking & data flow analysis                             │    │
│  │  • Control flow graph analysis                                      │    │
│  │  • Custom query language (MQL)                                      │    │
│  │  • Variant analysis                                                 │    │
│  └────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└──────────────────────────────────┬──────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Source Code Repository                             │
│                 (TypeScript, JavaScript, Python, PHP, Go,                    │
│                  Java, Ruby, Rust, Kotlin, Swift)                           │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 外部インターフェース

| インターフェース | 種類 | プロトコル | 説明 |
|-----------------|------|-----------|------|
| CLI | 入力 | stdin/stdout | コマンドライン操作 |
| MCP Server | 入力 | stdio/JSON-RPC | AIエージェント連携 |
| SARIF Output | 出力 | JSON | GitHub Code Scanning統合 |
| VS Code Extension | 入出力 | Language Server Protocol | IDE統合 |

---

## 3. C4モデル: Container

### 3.1 コンテナ構成図

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                       @nahisaho/musubix-security                              │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                               │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐              │
│  │   CLI Container │  │  MCP Container  │  │   API Container │              │
│  │                 │  │                 │  │                 │              │
│  │  • scan        │  │  • security_*   │  │  • REST API    │              │
│  │  • query       │  │    tools        │  │  • WebSocket   │              │
│  │  • report      │  │  • prompts      │  │                 │              │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘              │
│           │                    │                    │                        │
│           └────────────────────┼────────────────────┘                        │
│                                ▼                                              │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                      Core Analysis Engine                               │ │
│  │                                                                         │ │
│  │  ┌──────────────────────────────────────────────────────────────────┐  │ │
│  │  │                     Language Extractors                           │  │ │
│  │  │  ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐ │  │ │
│  │  │  │  TS  │ │  JS  │ │  PY  │ │ PHP  │ │  Go  │ │ Java │ │ Ruby │ │  │ │
│  │  │  │(既存)│ │(既存)│ │(既存)│ │(既存)│ │(NEW) │ │(NEW) │ │(NEW) │ │  │ │
│  │  │  └──────┘ └──────┘ └──────┘ └──────┘ └──────┘ └──────┘ └──────┘ │  │ │
│  │  └──────────────────────────────────────────────────────────────────┘  │ │
│  │                                │                                        │ │
│  │                                ▼                                        │ │
│  │  ┌──────────────────────────────────────────────────────────────────┐  │ │
│  │  │                       CodeDB (NEW)                                │  │ │
│  │  │  • AST Storage    • DFG Storage    • CFG Storage                 │  │ │
│  │  │  • Symbol Table   • Type Info      • Call Graph                  │  │ │
│  │  └──────────────────────────────────────────────────────────────────┘  │ │
│  │                                │                                        │ │
│  │           ┌────────────────────┼────────────────────┐                  │ │
│  │           ▼                    ▼                    ▼                  │ │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐           │ │
│  │  │  CFG Analyzer  │  │  DFG Analyzer  │  │ Taint Tracker  │           │ │
│  │  │   (強化)       │  │   (強化)       │  │   (強化)       │           │ │
│  │  └────────────────┘  └────────────────┘  └────────────────┘           │ │
│  │                                │                                        │ │
│  │                                ▼                                        │ │
│  │  ┌──────────────────────────────────────────────────────────────────┐  │ │
│  │  │                    MQL Query Engine (NEW)                         │  │ │
│  │  │  • Parser → Compiler → Optimizer → Executor                      │  │ │
│  │  └──────────────────────────────────────────────────────────────────┘  │ │
│  │                                │                                        │ │
│  │                                ▼                                        │ │
│  │  ┌────────────────────────────────────────────────────────────────┐    │ │
│  │  │                    Vulnerability Detector                       │    │ │
│  │  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │    │ │
│  │  │  │ OWASP    │ │ CWE      │ │ Variant  │ │ Zero-Day │          │    │ │
│  │  │  │ Top 10   │ │ Top 25   │ │ Analyzer │ │ Detector │          │    │ │
│  │  │  └──────────┘ └──────────┘ └──────────┘ └──────────┘          │    │ │
│  │  └────────────────────────────────────────────────────────────────┘    │ │
│  │                                │                                        │ │
│  └────────────────────────────────┼────────────────────────────────────────┘ │
│                                   ▼                                          │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                      Report Generator                                   │ │
│  │  • SARIF 2.1.0   • JSON   • Markdown   • HTML   • GitHub Alerts        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                               │
└──────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 コンテナ責務

| コンテナ | 責務 | 技術スタック |
|---------|------|-------------|
| CLI Container | コマンドライン操作 | Commander.js, Chalk |
| MCP Container | AIエージェント連携 | @modelcontextprotocol/sdk |
| Language Extractors | 言語別AST抽出 | Tree-sitter |
| CodeDB | コード情報永続化 | JSON, SQLite |
| CFG Analyzer | 制御フロー解析 | TypeScript |
| DFG Analyzer | データフロー解析 | TypeScript |
| Taint Tracker | テイント追跡 | TypeScript |
| MQL Engine | クエリ実行 | TypeScript |
| Vulnerability Detector | 脆弱性検出 | TypeScript |
| Report Generator | レポート生成 | TypeScript |

---

## 4. C4モデル: Component

### 4.1 CodeDB コンポーネント

```
┌──────────────────────────────────────────────────────────────────────────┐
│                              CodeDB                                       │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                         CodeDBBuilder                                │ │
│  │  @trace REQ-SEC-DB-001                                              │ │
│  │                                                                      │ │
│  │  • createDatabase(projectPath): CodeDatabase                        │ │
│  │  • updateDatabase(changes: FileChange[]): void                      │ │
│  │  • exportToJSON(): string                                           │ │
│  │  • importFromJSON(json: string): CodeDatabase                       │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                   │                                       │
│                                   ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                         CodeDatabase                                 │ │
│  │  @trace REQ-SEC-DB-002, REQ-SEC-DB-003, REQ-SEC-DB-004              │ │
│  │                                                                      │ │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐           │ │
│  │  │   ASTStore    │  │   DFGStore    │  │   CFGStore    │           │ │
│  │  │               │  │               │  │               │           │ │
│  │  │ • nodes       │  │ • nodes       │  │ • blocks      │           │ │
│  │  │ • edges       │  │ • edges       │  │ • edges       │           │ │
│  │  │ • symbols     │  │ • sources     │  │ • loops       │           │ │
│  │  │ • types       │  │ • sinks       │  │ • branches    │           │ │
│  │  └───────────────┘  └───────────────┘  └───────────────┘           │ │
│  │                                                                      │ │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐           │ │
│  │  │  SymbolTable  │  │  TypeInfo     │  │  CallGraph    │           │ │
│  │  │               │  │               │  │               │           │ │
│  │  │ • functions   │  │ • types       │  │ • nodes       │           │ │
│  │  │ • classes     │  │ • interfaces  │  │ • edges       │           │ │
│  │  │ • variables   │  │ • generics    │  │ • entry pts   │           │ │
│  │  └───────────────┘  └───────────────┘  └───────────────┘           │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                   │                                       │
│                                   ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                         CodeDBQuery                                  │ │
│  │  @trace REQ-SEC-DB-005, REQ-SEC-DB-006, REQ-SEC-DB-007              │ │
│  │                                                                      │ │
│  │  • queryAST(selector: ASTSelector): ASTNode[]                       │ │
│  │  • queryDataFlow(source: Node, sink: Node): DataFlowPath[]          │ │
│  │  • queryControlFlow(from: Block, to: Block): CFGPath[]              │ │
│  │  • querySymbols(pattern: string): Symbol[]                          │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                                                           │
└──────────────────────────────────────────────────────────────────────────┘
```

### 4.2 MQL Engine コンポーネント

```
┌──────────────────────────────────────────────────────────────────────────┐
│                            MQL Engine                                     │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                          MQLParser                                   │ │
│  │  @trace REQ-SEC-MQL-001                                             │ │
│  │                                                                      │ │
│  │  • parse(query: string): MQLAst                                     │ │
│  │  • validate(ast: MQLAst): ValidationResult                          │ │
│  │                                                                      │ │
│  │  Supported Syntax:                                                  │ │
│  │  • from <source> select <fields>                                    │ │
│  │  • where <condition>                                                │ │
│  │  • dataflow(<source>, <sink>)                                       │ │
│  │  • controlflow(<from>, <to>)                                        │ │
│  │  • transitive(<relation>)                                           │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                   │                                       │
│                                   ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                         MQLCompiler                                  │ │
│  │  @trace REQ-SEC-MQL-002, REQ-SEC-MQL-003                            │ │
│  │                                                                      │ │
│  │  • compile(ast: MQLAst): QueryPlan                                  │ │
│  │  • optimize(plan: QueryPlan): QueryPlan                             │ │
│  │                                                                      │ │
│  │  Optimizations:                                                     │ │
│  │  • Predicate pushdown                                               │ │
│  │  • Join reordering                                                  │ │
│  │  • Index utilization                                                │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                   │                                       │ 
│                                   ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                         MQLExecutor                                  │ │
│  │  @trace REQ-SEC-MQL-004, REQ-SEC-MQL-005, REQ-SEC-MQL-006           │ │
│  │                                                                      │ │
│  │  • execute(plan: QueryPlan, db: CodeDatabase): QueryResult          │ │
│  │  • executeWithCache(plan, db, cache): QueryResult                   │ │
│  │  • executeRecursive(plan, db, maxDepth): QueryResult                │ │
│  │                                                                      │ │
│  │  Built-in Functions:                                                │ │
│  │  • isTainted(node): boolean                                         │ │
│  │  • isSanitized(path): boolean                                       │ │
│  │  • reachable(from, to): boolean                                     │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                                                           │
└──────────────────────────────────────────────────────────────────────────┘
```

### 4.3 Language Extractors コンポーネント

```
┌──────────────────────────────────────────────────────────────────────────┐
│                        Language Extractors                                │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                           │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                    BaseExtractor (Abstract)                          │ │
│  │                                                                      │ │
│  │  • extract(source: string, filePath: string): ExtractionResult      │ │
│  │  • buildAST(source: string): ASTNode                                │ │
│  │  • buildDFG(ast: ASTNode): DataFlowGraph                           │ │
│  │  • buildCFG(ast: ASTNode): ControlFlowGraph                        │ │
│  │  • extractSymbols(ast: ASTNode): SymbolTable                       │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                   △                                       │
│          ┌────────────────────────┼────────────────────────┐             │
│          │                        │                        │             │
│  ┌───────┴───────┐  ┌────────────┴────────────┐  ┌───────┴───────┐     │
│  │TypeScriptExtractor│ │    GoExtractor (NEW)  │  │  JavaExtractor │     │
│  │  (既存強化)    │  │  @trace REQ-SEC-LANG-001│  │    (NEW)       │     │
│  │               │  │                         │  │@trace REQ-SEC- │     │
│  │ • tree-sitter │  │ • tree-sitter-go       │  │  LANG-002      │     │
│  │   -typescript │  │ • Go module resolution │  │ • tree-sitter  │     │
│  │ • TypeScript  │  │ • Goroutine tracking   │  │   -java        │     │
│  │   compiler API│  │ • Channel flow         │  │ • JVM bytecode │     │
│  └───────────────┘  └─────────────────────────┘  └───────────────┘     │
│                                                                           │
│  ┌───────────────┐  ┌─────────────────────────┐  ┌───────────────┐     │
│  │ RubyExtractor │  │    RustExtractor (NEW)   │  │PythonExtractor│     │
│  │    (NEW)      │  │  @trace REQ-SEC-LANG-004 │  │  (既存強化)   │     │
│  │@trace REQ-SEC-│  │                          │  │               │     │
│  │  LANG-003     │  │ • tree-sitter-rust       │  │ • tree-sitter │     │
│  │ • tree-sitter │  │ • Ownership tracking     │  │   -python     │     │
│  │   -ruby       │  │ • Lifetime analysis      │  │ • Type hints  │     │
│  │ • Rails aware │  │ • Unsafe block detection │  │ • Django/Flask│     │
│  └───────────────┘  └──────────────────────────┘  └───────────────┘     │
│                                                                           │
└──────────────────────────────────────────────────────────────────────────┘
```

### 4.4 Variant Analyzer コンポーネント

```
┌──────────────────────────────────────────────────────────────────────────┐
│                          Variant Analyzer                                 │
├──────────────────────────────────────────────────────────────────────────┤
│  @trace REQ-SEC-VAR-001, REQ-SEC-VAR-002, REQ-SEC-VAR-003, REQ-SEC-VAR-004│
│                                                                           │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                      PatternGenerator                                │ │
│  │                                                                      │ │
│  │  • fromVulnerability(vuln: Vulnerability): Pattern                  │ │
│  │  • generalize(pattern: Pattern): Pattern[]                          │ │
│  │  • abstract(pattern: Pattern, level: number): Pattern               │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                   │                                       │
│                                   ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                      PatternMatcher                                  │ │
│  │                                                                      │ │
│  │  • match(pattern: Pattern, codeDB: CodeDatabase): Match[]           │ │
│  │  • score(match: Match, original: Pattern): number                   │ │
│  │  • rank(matches: Match[]): Match[]                                  │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                   │                                       │
│                                   ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                      VariantReporter                                 │ │
│  │                                                                      │ │
│  │  • report(matches: Match[]): VariantReport                          │ │
│  │  • groupBySimilarity(matches: Match[]): MatchGroup[]                │ │
│  │  • exportToMQL(pattern: Pattern): string                            │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│                                                                           │
└──────────────────────────────────────────────────────────────────────────┘
```

---

## 5. データモデル

### 5.1 CodeDB スキーマ

```typescript
// @trace REQ-SEC-DB-002, REQ-SEC-DB-003, REQ-SEC-DB-004

/**
 * CodeDatabase - メインデータベース構造
 */
interface CodeDatabase {
  version: string;
  language: SupportedLanguage;
  projectPath: string;
  createdAt: Date;
  updatedAt: Date;
  
  // AST情報
  ast: ASTStore;
  
  // データフローグラフ
  dfg: DFGStore;
  
  // 制御フローグラフ
  cfg: CFGStore;
  
  // シンボルテーブル
  symbols: SymbolTable;
  
  // 型情報
  types: TypeStore;
  
  // コールグラフ
  callGraph: CallGraph;
}

/**
 * ASTStore - 抽象構文木ストレージ
 */
interface ASTStore {
  nodes: Map<string, ASTNode>;
  edges: ASTEdge[];
  rootNodes: string[]; // ファイルごとのルートノードID
}

interface ASTNode {
  id: string;
  type: string;           // 'FunctionDeclaration', 'CallExpression', etc.
  location: SourceLocation;
  properties: Record<string, unknown>;
  children: string[];     // 子ノードID
  parent?: string;        // 親ノードID
}

/**
 * DFGStore - データフローグラフストレージ
 */
interface DFGStore {
  nodes: Map<string, DFGNode>;
  edges: DFGEdge[];
  sources: string[];      // ソースノードID
  sinks: string[];        // シンクノードID
}

interface DFGNode {
  id: string;
  astNodeId: string;      // 対応するASTノード
  nodeType: 'source' | 'sink' | 'transform' | 'sanitizer' | 'propagator';
  taintLabel?: string;    // テイントラベル
  properties: Record<string, unknown>;
}

interface DFGEdge {
  from: string;
  to: string;
  edgeType: 'data' | 'control' | 'implicit';
  properties: Record<string, unknown>;
}

/**
 * CFGStore - 制御フローグラフストレージ
 */
interface CFGStore {
  blocks: Map<string, BasicBlock>;
  edges: CFGEdge[];
  entryBlocks: string[];
  exitBlocks: string[];
}

interface BasicBlock {
  id: string;
  statements: string[];   // ASTノードID
  predecessors: string[];
  successors: string[];
  dominators: string[];
  loopHeader?: boolean;
}

/**
 * SymbolTable - シンボルテーブル
 */
interface SymbolTable {
  functions: Map<string, FunctionSymbol>;
  classes: Map<string, ClassSymbol>;
  variables: Map<string, VariableSymbol>;
  imports: Map<string, ImportSymbol>;
  exports: Map<string, ExportSymbol>;
}

/**
 * CallGraph - コールグラフ
 */
interface CallGraph {
  nodes: Map<string, CallGraphNode>;
  edges: CallGraphEdge[];
  entryPoints: string[];
  virtualCalls: VirtualCall[];
}
```

### 5.2 MQL クエリ構文

```typescript
// @trace REQ-SEC-MQL-001

/**
 * MQL Query Language Grammar (EBNF-like)
 * 
 * query       ::= from_clause select_clause? where_clause? 
 * from_clause ::= 'from' source_spec
 * source_spec ::= 'functions' | 'calls' | 'dataflow' | 'classes' | 'variables'
 * select_clause ::= 'select' field_list
 * field_list  ::= field (',' field)*
 * where_clause ::= 'where' condition
 * condition   ::= simple_cond | compound_cond
 * simple_cond ::= field_ref operator value
 * compound_cond ::= condition ('and' | 'or') condition
 * 
 * Built-in predicates:
 * - isTainted(node)        : Check if node is tainted
 * - isSanitized(node)      : Check if node is sanitized
 * - reachable(from, to)    : Check reachability in CFG
 * - dataflow(source, sink) : Find data flow paths
 * - calls(caller, callee)  : Check call relationship
 */

// Example queries:

// Find all SQL injection vulnerabilities
const sqlInjectionQuery = `
  from dataflow(UserInput, SQLQuery)
  where not isSanitized(path)
  select source, sink, path
`;

// Find all functions that call eval with user input
const evalVulnQuery = `
  from calls
  where callee.name = 'eval'
    and isTainted(callee.arguments[0])
  select caller, callee, callee.arguments[0] as taintedArg
`;

// Find command injection patterns
const cmdInjectionQuery = `
  from functions
  where exists(call in function.calls 
    where call.name in ['exec', 'spawn', 'execSync']
      and isTainted(call.arguments[0]))
  select function, call, call.arguments[0]
`;
```

---

## 6. インターフェース設計

### 6.1 言語エクストラクター API

```typescript
// @trace REQ-SEC-LANG-001, REQ-SEC-LANG-002, REQ-SEC-LANG-003, REQ-SEC-LANG-004

/**
 * Language Extractor Interface
 */
interface LanguageExtractor {
  /**
   * Get supported language
   */
  readonly language: SupportedLanguage;
  
  /**
   * Get supported file extensions
   */
  readonly extensions: string[];
  
  /**
   * Extract code information from source
   */
  extract(source: string, filePath: string): Promise<ExtractionResult>;
  
  /**
   * Check if file is supported
   */
  supports(filePath: string): boolean;
  
  /**
   * Get framework models for this language
   */
  getFrameworkModels(): FrameworkModel[];
}

/**
 * Extraction result
 */
interface ExtractionResult {
  ast: ASTNode;
  dfg: DataFlowGraph;
  cfg: ControlFlowGraph;
  symbols: SymbolTable;
  types: TypeInfo;
  errors: ExtractionError[];
  metrics: ExtractionMetrics;
}

/**
 * Supported languages (extended)
 */
type SupportedLanguage = 
  | 'typescript' 
  | 'javascript' 
  | 'python' 
  | 'php'
  | 'go'      // NEW
  | 'java'    // NEW
  | 'ruby'    // NEW
  | 'rust'    // NEW
  | 'kotlin'  // Phase 2
  | 'swift';  // Phase 2
```

### 6.2 CodeDB API

```typescript
// @trace REQ-SEC-DB-001, REQ-SEC-DB-005, REQ-SEC-DB-007

/**
 * CodeDB Builder API
 */
interface CodeDBBuilder {
  /**
   * Create new code database from project
   */
  createDatabase(options: CreateDBOptions): Promise<CodeDatabase>;
  
  /**
   * Update existing database with file changes
   */
  updateDatabase(db: CodeDatabase, changes: FileChange[]): Promise<void>;
  
  /**
   * Export database to JSON (Git-friendly)
   */
  exportToJSON(db: CodeDatabase): string;
  
  /**
   * Import database from JSON
   */
  importFromJSON(json: string): CodeDatabase;
}

interface CreateDBOptions {
  projectPath: string;
  languages?: SupportedLanguage[];
  excludePatterns?: string[];
  includePatterns?: string[];
  maxFileSize?: number;
  parallel?: boolean;
}

interface FileChange {
  path: string;
  changeType: 'added' | 'modified' | 'deleted';
  content?: string;
}
```

### 6.3 MQL API

```typescript
// @trace REQ-SEC-MQL-001, REQ-SEC-MQL-002, REQ-SEC-MQL-005

/**
 * MQL Query Engine API
 */
interface MQLEngine {
  /**
   * Execute MQL query against code database
   */
  query(query: string, db: CodeDatabase): Promise<QueryResult>;
  
  /**
   * Parse and validate query
   */
  parse(query: string): ParseResult;
  
  /**
   * Execute parameterized query
   */
  queryWithParams(
    query: string, 
    params: Record<string, unknown>,
    db: CodeDatabase
  ): Promise<QueryResult>;
  
  /**
   * Register custom predicate
   */
  registerPredicate(
    name: string, 
    impl: PredicateFunction
  ): void;
}

interface QueryResult {
  rows: QueryRow[];
  columns: string[];
  executionTime: number;
  queryPlan?: QueryPlan;
}

type PredicateFunction = (
  node: ASTNode | DFGNode,
  db: CodeDatabase
) => boolean;
```

### 6.4 Variant Analyzer API

```typescript
// @trace REQ-SEC-VAR-001, REQ-SEC-VAR-002, REQ-SEC-VAR-003

/**
 * Variant Analyzer API
 */
interface VariantAnalyzer {
  /**
   * Find variants of a known vulnerability
   */
  findVariants(
    seed: Vulnerability,
    db: CodeDatabase,
    options?: VariantOptions
  ): Promise<VariantResult>;
  
  /**
   * Generate pattern from vulnerability
   */
  generatePattern(vuln: Vulnerability): Pattern;
  
  /**
   * Generalize pattern to find more variants
   */
  generalizePattern(
    pattern: Pattern, 
    level: GeneralizationLevel
  ): Pattern[];
  
  /**
   * Export pattern as MQL query
   */
  exportToMQL(pattern: Pattern): string;
}

interface VariantOptions {
  maxResults?: number;
  minSimilarity?: number;
  generalizationLevel?: GeneralizationLevel;
  crossRepository?: boolean;
}

type GeneralizationLevel = 'exact' | 'similar' | 'broad';

interface VariantResult {
  variants: VariantMatch[];
  pattern: Pattern;
  searchStats: SearchStats;
}

interface VariantMatch {
  vulnerability: Vulnerability;
  similarity: number;
  matchedPattern: Pattern;
}
```

---

## 7. ディレクトリ構造

```
packages/security/src/
├── index.ts                      # メインエントリポイント
├── types/                        # 型定義
│   ├── index.ts
│   ├── vulnerability.ts          # (既存)
│   ├── codedb.ts                 # NEW: CodeDB型
│   ├── mql.ts                    # NEW: MQL型
│   └── variant.ts                # NEW: バリアント型
├── extractors/                   # NEW: 言語エクストラクター
│   ├── index.ts
│   ├── base-extractor.ts         # 抽象基底クラス
│   ├── typescript-extractor.ts   # 既存強化
│   ├── python-extractor.ts       # 既存強化
│   ├── go-extractor.ts           # NEW
│   ├── java-extractor.ts         # NEW
│   ├── ruby-extractor.ts         # NEW
│   └── rust-extractor.ts         # NEW
├── codedb/                       # NEW: コードデータベース
│   ├── index.ts
│   ├── builder.ts                # CodeDBBuilder
│   ├── database.ts               # CodeDatabase
│   ├── query.ts                  # CodeDBQuery
│   ├── stores/
│   │   ├── ast-store.ts
│   │   ├── dfg-store.ts
│   │   ├── cfg-store.ts
│   │   └── symbol-store.ts
│   └── serializer.ts             # JSON serialization
├── mql/                          # NEW: MQLエンジン
│   ├── index.ts
│   ├── parser.ts                 # MQLParser
│   ├── compiler.ts               # MQLCompiler
│   ├── executor.ts               # MQLExecutor
│   ├── optimizer.ts              # Query optimizer
│   ├── predicates/               # Built-in predicates
│   │   ├── taint.ts
│   │   ├── reachability.ts
│   │   └── call.ts
│   └── stdlib/                   # Standard library queries
│       ├── owasp.mql
│       └── cwe.mql
├── analysis/                     # 解析エンジン（既存強化）
│   ├── cfg/                      # NEW: CFG強化
│   │   ├── builder.ts
│   │   ├── analyzer.ts
│   │   └── path-sensitive.ts
│   ├── dfg/                      # NEW: DFG強化
│   │   ├── builder.ts
│   │   ├── taint-tracker.ts
│   │   └── context-sensitive.ts
│   └── ... (既存ファイル)
├── variant/                      # NEW: バリアント解析
│   ├── index.ts
│   ├── pattern-generator.ts
│   ├── pattern-matcher.ts
│   └── reporter.ts
├── frameworks/                   # NEW: フレームワークモデル
│   ├── index.ts
│   ├── express.ts
│   ├── nestjs.ts
│   ├── react.ts
│   ├── django.ts
│   ├── flask.ts
│   ├── spring.ts
│   ├── rails.ts
│   └── gin.ts
└── ... (既存ディレクトリ)
```

---

## 8. Phase 1 実装計画

### 8.1 Phase 1 (v3.1.0) コンポーネント

| 優先度 | コンポーネント | 工数(人日) | 依存 |
|--------|---------------|-----------|------|
| P0 | GoExtractor | 3 | tree-sitter-go |
| P0 | JavaExtractor | 3 | tree-sitter-java |
| P0 | CodeDBBuilder | 4 | Extractors |
| P0 | CodeDatabase | 3 | - |
| P0 | CodeDBQuery | 3 | CodeDatabase |
| P0 | CFGBuilder (強化) | 3 | - |
| P0 | DFGBuilder (強化) | 3 | - |
| P1 | RubyExtractor | 2 | tree-sitter-ruby |
| P1 | RustExtractor | 2 | tree-sitter-rust |
| P1 | FrameworkModels (Express/NestJS/Django/Flask) | 4 | Extractors |

**合計工数**: 30人日（約1.5ヶ月）

### 8.2 依存パッケージ

```json
{
  "dependencies": {
    "tree-sitter": "^0.22.0",
    "tree-sitter-go": "^0.21.0",
    "tree-sitter-java": "^0.21.0",
    "tree-sitter-ruby": "^0.21.0",
    "tree-sitter-rust": "^0.21.0"
  }
}
```

---

## 9. 設計判断記録 (ADR)

### ADR-SEC-001: Tree-sitterの採用

**コンテキスト**: 多言語対応のためのAST解析ライブラリ選定

**決定**: Tree-sitterを採用

**理由**:
- 12以上の言語サポート
- 高速なインクリメンタル解析
- メモリ効率が良い
- CodeQL / GitHub内部でも使用実績あり

**代替案**:
- 各言語のネイティブパーサー（管理コストが高い）
- Babel/TypeScript Compiler API のみ（JS/TS限定）

### ADR-SEC-002: SQLiteではなくJSONストレージを採用

**コンテキスト**: CodeDBの永続化方式

**決定**: JSON形式でのファイルベースストレージを採用

**理由**:
- Git-friendly（diff/merge可能）
- 依存関係の削減（better-sqlite3不要）
- MUSUBIXの@musubix/knowledgeと整合性
- 小〜中規模プロジェクトで十分なパフォーマンス

**トレードオフ**:
- 大規模プロジェクトではSQLiteの方が高速
- Phase 3でオプショナルなSQLiteサポートを検討

---

## 10. セルフレビュー

### レビュー実施項目

| 観点 | 状態 | 詳細 |
|------|------|------|
| 要件トレーサビリティ | ✅ OK | 全主要要件を設計コンポーネントにマッピング |
| C4モデル完全性 | ✅ OK | Context/Container/Component図を作成 |
| インターフェース定義 | ✅ OK | 主要API（Extractor/CodeDB/MQL/Variant）を定義 |
| データモデル | ✅ OK | CodeDBスキーマ、MQL構文を定義 |
| 既存実装との整合性 | ✅ OK | 既存のAnalysis/Types構造を継承 |
| 設計パターン適用 | ✅ OK | Factory, Strategy, Visitorパターン適用 |
| ADR記録 | ✅ OK | Tree-sitter採用、JSONストレージ採用を記録 |
| Phase 1スコープ | ✅ OK | Go/Java/Ruby/Rust + CodeDB + CFG/DFG強化 |

### 確認事項

1. **Tree-sitter依存**: ネイティブモジュールが必要ですが、許容しますか？
2. **MQL構文**: SQL風の構文を採用しましたが、CodeQLのQL風が良いですか？
3. **Phase 1優先度**: Go/Javaを先行、Ruby/Rustを後続としましたが、変更が必要ですか？

---

👉 **次のアクションを選択してください:**
- **修正** / 具体的な修正指示 → 修正して再提示
- **承認** / **OK** / **進める** → Phase 3（タスク分解）へ

**⚠️ 注意**: Article Xに従い、設計承認後は必ずPhase 3（タスク分解）を経て実装に進みます。
