# DES-DFG-001: MUSUBIX Data Flow Graph (DFG) Package Design

**Document ID**: DES-DFG-001  
**Version**: 1.0.0  
**Status**: Draft  
**Created**: 2026-01-07  
**Author**: MUSUBIX SDD Agent  
**Package**: @nahisaho/musubix-dfg  
**Traces**: REQ-DFG-001

---

## 1. Overview

本ドキュメントは `@nahisaho/musubix-dfg` パッケージのC4モデル設計を定義します。

---

## 2. C4 Model

### 2.1 Context Diagram (Level 1)

```
┌─────────────────────────────────────────────────────────────────────┐
│                         MUSUBIX Ecosystem                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────┐     ┌─────────────────────┐     ┌──────────────────┐ │
│  │Developer │────▶│  @nahisaho/         │────▶│  YATA Local      │ │
│  │(User)    │     │  musubix-dfg        │     │  Knowledge Graph │ │
│  └──────────┘     └─────────────────────┘     └──────────────────┘ │
│       │                    │                                        │
│       │                    ▼                                        │
│       │           ┌─────────────────────┐                          │
│       └──────────▶│  LLM Context        │                          │
│                   │  (Prompt Generator) │                          │
│                   └─────────────────────┘                          │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

**External Actors**:
- **Developer**: CLI/APIを通じてDFG/CFG分析を実行
- **YATA Local**: DFGデータを知識グラフとして永続化
- **LLM**: コンテキスト情報を受け取りコード生成に活用

---

### 2.2 Container Diagram (Level 2)

```
┌─────────────────────────────────────────────────────────────────────┐
│                      @nahisaho/musubix-dfg                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────────────┐│
│  │  CLI Container │  │ API Container  │  │ Core Analysis Engine   ││
│  │  (bin/cli.js)  │  │ (src/index.ts) │  │ (src/analyzers/)       ││
│  └───────┬────────┘  └───────┬────────┘  └───────────┬────────────┘│
│          │                   │                       │              │
│          └───────────────────┼───────────────────────┘              │
│                              ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────┐│
│  │                    Graph Data Structures                         ││
│  │                    (src/graph/)                                  ││
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐ ││
│  │  │ DFGBuilder  │  │ CFGBuilder  │  │ DependencyGraph         │ ││
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘ ││
│  └─────────────────────────────────────────────────────────────────┘│
│                              │                                       │
│                              ▼                                       │
│  ┌─────────────────────────────────────────────────────────────────┐│
│  │                    Integration Layer                             ││
│  │  ┌─────────────────┐  ┌─────────────────────────────────────┐  ││
│  │  │ YATA Exporter   │  │ LLM Context Generator               │  ││
│  │  │ (src/yata/)     │  │ (src/llm/)                          │  ││
│  │  └─────────────────┘  └─────────────────────────────────────┘  ││
│  └─────────────────────────────────────────────────────────────────┘│
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

### 2.3 Component Diagram (Level 3)

#### 2.3.1 Core Analysis Engine

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Core Analysis Engine                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    DataFlowAnalyzer                           │  │
│  │  @traces REQ-DFG-EXTRACT-001, REQ-DFG-EXTRACT-002            │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  + analyze(sourceFile: SourceFile): DataFlowGraph            │  │
│  │  + analyzeFile(filePath: string): Promise<DataFlowGraph>     │  │
│  │  + extractDefUseChains(): DefUseChain[]                      │  │
│  │  + trackFunctionCalls(): FunctionCallFlow[]                  │  │
│  │  + trackPropertyAccess(): PropertyAccessFlow[]               │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│                              ▼                                       │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    ControlFlowAnalyzer                        │  │
│  │  @traces REQ-DFG-CFG-001, REQ-DFG-CFG-002, REQ-DFG-CFG-003   │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  + analyze(sourceFile: SourceFile): ControlFlowGraph         │  │
│  │  + analyzeFile(filePath: string): Promise<ControlFlowGraph>  │  │
│  │  + buildBasicBlocks(): BasicBlock[]                          │  │
│  │  + analyzeBranches(): BranchNode[]                           │  │
│  │  + analyzeLoops(): LoopInfo[]                                │  │
│  │  + analyzeExceptions(): ExceptionFlow[]                      │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│                              ▼                                       │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    DependencyAnalyzer                         │  │
│  │  @traces REQ-DFG-DEP-001, REQ-DFG-DEP-002, REQ-DFG-DEP-003   │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  + analyzeVariableDeps(): DependencyMap                      │  │
│  │  + analyzeFunctionDeps(): FunctionCallGraph                  │  │
│  │  + analyzeModuleDeps(): ModuleDependencyGraph                │  │
│  │  + detectCircularDeps(): CircularDependency[]                │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

#### 2.3.2 Graph Data Structures

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Graph Data Structures                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    DataFlowGraph                              │  │
│  │  @traces REQ-DFG-API-002                                     │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  - nodes: Map<string, DFGNode>                               │  │
│  │  - edges: DFGEdge[]                                          │  │
│  │  + addNode(node: DFGNode): void                              │  │
│  │  + addEdge(from: string, to: string, type: EdgeType): void   │  │
│  │  + getNode(id: string): DFGNode | undefined                  │  │
│  │  + getIncomingEdges(nodeId: string): DFGEdge[]               │  │
│  │  + getOutgoingEdges(nodeId: string): DFGEdge[]               │  │
│  │  + bfs(startId: string, visitor: Visitor): void              │  │
│  │  + dfs(startId: string, visitor: Visitor): void              │  │
│  │  + findPath(from: string, to: string): string[]              │  │
│  │  + reachableFrom(nodeId: string): Set<string>                │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    ControlFlowGraph                           │  │
│  │  @traces REQ-DFG-API-002                                     │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  - blocks: Map<string, BasicBlock>                           │  │
│  │  - edges: CFGEdge[]                                          │  │
│  │  - entry: string                                             │  │
│  │  - exit: string                                              │  │
│  │  + addBlock(block: BasicBlock): void                         │  │
│  │  + addEdge(from: string, to: string, type: CFGEdgeType): void│  │
│  │  + getBlock(id: string): BasicBlock | undefined              │  │
│  │  + getSuccessors(blockId: string): BasicBlock[]              │  │
│  │  + getPredecessors(blockId: string): BasicBlock[]            │  │
│  │  + dominators(): Map<string, Set<string>>                    │  │
│  │  + postDominators(): Map<string, Set<string>>                │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    DependencyGraph                            │  │
│  │  @traces REQ-DFG-DEP-001                                     │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  - dependencies: Map<string, Set<string>>                    │  │
│  │  + addDependency(from: string, to: string): void             │  │
│  │  + getDependencies(id: string): Set<string>                  │  │
│  │  + getDependents(id: string): Set<string>                    │  │
│  │  + getTransitiveDependencies(id: string): Set<string>        │  │
│  │  + detectCycles(): string[][]                                │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

#### 2.3.3 Integration Layer

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Integration Layer                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    YATAExporter                               │  │
│  │  @traces REQ-DFG-YATA-001, REQ-DFG-YATA-002                  │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  + toTriples(dfg: DataFlowGraph): Triple[]                   │  │
│  │  + toTriples(cfg: ControlFlowGraph): Triple[]                │  │
│  │  + exportToYATALocal(graph: Graph, yata: YATALocal): void    │  │
│  │  + exportToFile(graph: Graph, format: Format): string        │  │
│  │  + incrementalUpdate(oldGraph: Graph, newGraph: Graph): Diff │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    LLMContextGenerator                        │  │
│  │  @traces REQ-DFG-LLM-001, REQ-DFG-LLM-002                    │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  + toPromptContext(dfg: DataFlowGraph, opts?: Options): str  │  │
│  │  + toPromptContext(cfg: ControlFlowGraph, opts?: Options): str│ │
│  │  + filterByRelevance(graph: Graph, focus: Location): Graph   │  │
│  │  + compressForTokenLimit(context: string, limit: number): str│  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                    QueryEngine                                │  │
│  │  @traces REQ-DFG-YATA-003                                    │  │
│  ├──────────────────────────────────────────────────────────────┤  │
│  │  + query(sparql: string): QueryResult[]                      │  │
│  │  + findInfluencers(variable: string): string[]               │  │
│  │  + findCallers(function: string): string[]                   │  │
│  │  + findCircularDeps(): CircularDep[]                         │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

### 2.4 Code Diagram (Level 4)

#### 2.4.1 Type Definitions

```typescript
// src/types/index.ts
// @traces REQ-DFG-API-001

/**
 * DFG Node Types
 */
export type DFGNodeType = 
  | 'variable-def'      // 変数定義
  | 'variable-use'      // 変数使用
  | 'parameter'         // 関数パラメータ
  | 'return-value'      // 戻り値
  | 'property-access'   // プロパティアクセス
  | 'array-access'      // 配列アクセス
  | 'function-call'     // 関数呼び出し
  | 'literal';          // リテラル値

/**
 * DFG Node
 */
export interface DFGNode {
  id: string;
  type: DFGNodeType;
  name: string;
  location: SourceLocation;
  metadata?: Record<string, unknown>;
}

/**
 * DFG Edge Types
 */
export type DFGEdgeType =
  | 'def-use'           // 定義→使用
  | 'parameter-flow'    // 引数→パラメータ
  | 'return-flow'       // return→呼び出し元
  | 'property-flow'     // オブジェクトプロパティフロー
  | 'array-flow';       // 配列要素フロー

/**
 * DFG Edge
 */
export interface DFGEdge {
  from: string;
  to: string;
  type: DFGEdgeType;
  label?: string;
}

/**
 * CFG Node Types
 */
export type CFGNodeType =
  | 'entry'             // 入口
  | 'exit'              // 出口
  | 'basic-block'       // 基本ブロック
  | 'branch'            // 分岐
  | 'loop-header'       // ループヘッダー
  | 'try'               // try開始
  | 'catch'             // catch
  | 'finally';          // finally

/**
 * Basic Block
 */
export interface BasicBlock {
  id: string;
  type: CFGNodeType;
  statements: Statement[];
  location: SourceLocation;
}

/**
 * CFG Edge Types
 */
export type CFGEdgeType =
  | 'unconditional'     // 無条件ジャンプ
  | 'true-branch'       // 条件true
  | 'false-branch'      // 条件false
  | 'back-edge'         // バックエッジ（ループ）
  | 'exception';        // 例外フロー

/**
 * CFG Edge
 */
export interface CFGEdge {
  from: string;
  to: string;
  type: CFGEdgeType;
  condition?: string;
}

/**
 * Source Location
 */
export interface SourceLocation {
  filePath: string;
  startLine: number;
  startColumn: number;
  endLine: number;
  endColumn: number;
}

/**
 * Analysis Options
 */
export interface AnalysisOptions {
  includeImports?: boolean;
  maxDepth?: number;
  trackClosures?: boolean;
}

/**
 * LLM Context Options
 */
export interface LLMContextOptions {
  maxTokens?: number;
  hopDistance?: number;       // @traces REQ-DFG-LLM-002 (1-10)
  relevanceThreshold?: number; // @traces REQ-DFG-LLM-002 (0.0-1.0)
  format?: 'compact' | 'detailed';
}
```

#### 2.4.2 DataFlowAnalyzer Implementation

```typescript
// src/analyzers/data-flow-analyzer.ts
// @traces REQ-DFG-EXTRACT-001, REQ-DFG-EXTRACT-002, REQ-DFG-EXTRACT-003

import { Project, SourceFile, Node, SyntaxKind } from 'ts-morph';
import { DataFlowGraph, DFGNode, DFGEdge, AnalysisOptions } from '../types/index.js';

export class DataFlowAnalyzer {
  private project: Project;

  constructor() {
    this.project = new Project({
      useInMemoryFileSystem: false,
    });
  }

  /**
   * Analyze a file and extract DFG
   * @traces REQ-DFG-EXTRACT-001
   */
  async analyzeFile(filePath: string, options?: AnalysisOptions): Promise<DataFlowGraph> {
    const sourceFile = this.project.addSourceFileAtPath(filePath);
    return this.analyze(sourceFile, options);
  }

  /**
   * Analyze source file and extract DFG
   * @traces REQ-DFG-EXTRACT-001
   */
  analyze(sourceFile: SourceFile, options?: AnalysisOptions): DataFlowGraph {
    const graph = new DataFlowGraph();
    
    // Extract variable definitions
    this.extractVariableDefinitions(sourceFile, graph);
    
    // Extract variable usages and create def-use chains
    this.extractVariableUsages(sourceFile, graph);
    
    // Track function calls
    if (options?.trackClosures !== false) {
      this.trackFunctionCalls(sourceFile, graph);
    }
    
    // Track property access
    this.trackPropertyAccess(sourceFile, graph);
    
    return graph;
  }

  /**
   * Extract variable definitions
   * @traces REQ-DFG-EXTRACT-001
   */
  private extractVariableDefinitions(sourceFile: SourceFile, graph: DataFlowGraph): void {
    sourceFile.getDescendantsOfKind(SyntaxKind.VariableDeclaration).forEach(decl => {
      const node: DFGNode = {
        id: this.generateNodeId(decl),
        type: 'variable-def',
        name: decl.getName(),
        location: this.getLocation(decl),
      };
      graph.addNode(node);
    });
  }

  /**
   * Track function calls and parameter flow
   * @traces REQ-DFG-EXTRACT-002
   */
  private trackFunctionCalls(sourceFile: SourceFile, graph: DataFlowGraph): void {
    sourceFile.getDescendantsOfKind(SyntaxKind.CallExpression).forEach(call => {
      const callNode: DFGNode = {
        id: this.generateNodeId(call),
        type: 'function-call',
        name: call.getExpression().getText(),
        location: this.getLocation(call),
      };
      graph.addNode(callNode);
      
      // Track arguments
      call.getArguments().forEach((arg, index) => {
        const argSource = this.resolveExpression(arg, graph);
        if (argSource) {
          graph.addEdge(argSource, callNode.id, 'parameter-flow');
        }
      });
    });
  }

  /**
   * Track property access
   * @traces REQ-DFG-EXTRACT-003
   */
  private trackPropertyAccess(sourceFile: SourceFile, graph: DataFlowGraph): void {
    sourceFile.getDescendantsOfKind(SyntaxKind.PropertyAccessExpression).forEach(access => {
      const node: DFGNode = {
        id: this.generateNodeId(access),
        type: 'property-access',
        name: access.getText(),
        location: this.getLocation(access),
      };
      graph.addNode(node);
      
      // Link to object
      const objectSource = this.resolveExpression(access.getExpression(), graph);
      if (objectSource) {
        graph.addEdge(objectSource, node.id, 'property-flow');
      }
    });
  }

  // ... helper methods
}
```

---

## 3. Package Structure

```
packages/dfg/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── README.md
├── bin/
│   └── musubix-dfg.js           # CLI entry point
├── src/
│   ├── index.ts                  # Public API exports
│   ├── types/
│   │   ├── index.ts              # Type definitions
│   │   ├── dfg.ts                # DFG types
│   │   ├── cfg.ts                # CFG types
│   │   └── dependency.ts         # Dependency types
│   ├── analyzers/
│   │   ├── index.ts              # Analyzer exports
│   │   ├── data-flow-analyzer.ts # DFG extraction
│   │   ├── control-flow-analyzer.ts # CFG extraction
│   │   └── dependency-analyzer.ts # Dependency analysis
│   ├── graph/
│   │   ├── index.ts              # Graph exports
│   │   ├── data-flow-graph.ts    # DFG data structure
│   │   ├── control-flow-graph.ts # CFG data structure
│   │   └── dependency-graph.ts   # Dependency graph
│   ├── yata/
│   │   ├── index.ts              # YATA integration exports
│   │   ├── exporter.ts           # YATA exporter
│   │   └── query-engine.ts       # Query support
│   ├── llm/
│   │   ├── index.ts              # LLM integration exports
│   │   └── context-generator.ts  # LLM context generator
│   └── cli/
│       ├── index.ts              # CLI exports
│       └── commands.ts           # CLI commands
└── __tests__/
    ├── data-flow-analyzer.test.ts
    ├── control-flow-analyzer.test.ts
    ├── dependency-analyzer.test.ts
    ├── graph.test.ts
    ├── yata-exporter.test.ts
    └── cli.test.ts
```

---

## 4. Design Patterns Applied

| Pattern | Application | Traces |
|---------|-------------|--------|
| **Builder** | DataFlowGraph/ControlFlowGraph construction | REQ-DFG-API-001 |
| **Visitor** | AST traversal for analysis | REQ-DFG-EXTRACT-001 |
| **Strategy** | Different graph traversal algorithms | REQ-DFG-API-002 |
| **Adapter** | YATA knowledge graph integration | REQ-DFG-YATA-001 |
| **Facade** | Simplified API for complex analysis | REQ-DFG-API-001 |

---

## 5. Sequence Diagrams

### 5.1 DFG Extraction Flow

```
Developer          CLI              DataFlowAnalyzer      ts-morph       DataFlowGraph
    │                │                     │                  │                │
    │─extract file──▶│                     │                  │                │
    │                │──analyzeFile()─────▶│                  │                │
    │                │                     │──parse()────────▶│                │
    │                │                     │◀──SourceFile─────│                │
    │                │                     │                  │                │
    │                │                     │──extractDefs()───┼───────────────▶│
    │                │                     │──extractUses()───┼───────────────▶│
    │                │                     │──trackCalls()────┼───────────────▶│
    │                │                     │◀─────────────────┼────DFG─────────│
    │                │◀──DataFlowGraph─────│                  │                │
    │◀──JSON/DOT────│                     │                  │                │
    │                │                     │                  │                │
```

### 5.2 YATA Export Flow

```
Developer          CLI              YATAExporter         YATALocal
    │                │                     │                  │
    │─export --yata─▶│                     │                  │
    │                │──toTriples()───────▶│                  │
    │                │◀──Triple[]──────────│                  │
    │                │                     │                  │
    │                │──exportToYATA()────▶│                  │
    │                │                     │──addTriples()───▶│
    │                │                     │◀──success────────│
    │                │◀──success───────────│                  │
    │◀──Exported────│                     │                  │
    │                │                     │                  │
```

---

## 6. Traceability Matrix

| Requirement | Design Component | Test Case |
|-------------|------------------|-----------|
| REQ-DFG-EXTRACT-001 | DataFlowAnalyzer.analyze() | TST-DFG-EXTRACT-001 |
| REQ-DFG-EXTRACT-002 | DataFlowAnalyzer.trackFunctionCalls() | TST-DFG-EXTRACT-002 |
| REQ-DFG-EXTRACT-003 | DataFlowAnalyzer.trackPropertyAccess() | TST-DFG-EXTRACT-003 |
| REQ-DFG-EXTRACT-004 | DataFlowAnalyzer.trackArrayAccess() | TST-DFG-EXTRACT-004 |
| REQ-DFG-CFG-001 | ControlFlowAnalyzer.buildBasicBlocks() | TST-DFG-CFG-001 |
| REQ-DFG-CFG-002 | ControlFlowAnalyzer.analyzeBranches() | TST-DFG-CFG-002 |
| REQ-DFG-CFG-003 | ControlFlowAnalyzer.analyzeLoops() | TST-DFG-CFG-003 |
| REQ-DFG-CFG-004 | ControlFlowAnalyzer.analyzeExceptions() | TST-DFG-CFG-004 |
| REQ-DFG-DEP-001 | DependencyAnalyzer.analyzeVariableDeps() | TST-DFG-DEP-001 |
| REQ-DFG-DEP-002 | DependencyAnalyzer.analyzeFunctionDeps() | TST-DFG-DEP-002 |
| REQ-DFG-DEP-003 | DependencyAnalyzer.analyzeModuleDeps() | TST-DFG-DEP-003 |
| REQ-DFG-YATA-001 | YATAExporter.toTriples() | TST-DFG-YATA-001 |
| REQ-DFG-YATA-002 | YATAExporter.incrementalUpdate() | TST-DFG-YATA-002 |
| REQ-DFG-YATA-003 | QueryEngine.query() | TST-DFG-YATA-003 |
| REQ-DFG-LLM-001 | LLMContextGenerator.toPromptContext() | TST-DFG-LLM-001 |
| REQ-DFG-LLM-002 | LLMContextGenerator.filterByRelevance() | TST-DFG-LLM-002 |
| REQ-DFG-CLI-001 | CLI extract command | TST-DFG-CLI-001 |
| REQ-DFG-CLI-002 | CLI analyze command | TST-DFG-CLI-002 |
| REQ-DFG-CLI-003 | CLI export command | TST-DFG-CLI-003 |
| REQ-DFG-API-001 | Public API exports | TST-DFG-API-001 |
| REQ-DFG-API-002 | Graph traversal methods | TST-DFG-API-002 |
| REQ-DFG-PERF-001 | Performance benchmarks | TST-DFG-PERF-001 |
| REQ-DFG-PERF-002 | Memory profiling | TST-DFG-PERF-002 |
| REQ-DFG-ACC-001 | Accuracy validation | TST-DFG-ACC-001 |
| REQ-DFG-COMPAT-001 | TypeScript 5.0+ tests | TST-DFG-COMPAT-001 |
| REQ-DFG-COMPAT-002 | Node.js 20+ tests | TST-DFG-COMPAT-002 |

---

## 7. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-07 | SDD Agent | Initial design |

---

**© 2026 MUSUBIX Project - Constitutional Article VII Compliant (Design Patterns)**
