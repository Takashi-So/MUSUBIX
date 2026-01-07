# REQ-DFG-001: MUSUBIX Data Flow Graph (DFG) Package Requirements

**Document ID**: REQ-DFG-001  
**Version**: 1.0.0  
**Status**: Draft  
**Created**: 2026-01-07  
**Author**: MUSUBIX SDD Agent  
**Package**: @nahisaho/musubix-dfg  

---

## 1. Executive Summary

本ドキュメントは、MUSUBIXのコード理解基盤となる `@nahisaho/musubix-dfg` パッケージの要件を定義します。データフローグラフ（DFG）および制御フローグラフ（CFG）の抽出・分析機能を提供し、Neuro-Symbolic統合の記号的分析を強化します。

**参考文献**: GraphCodeBERT、JetBrains PSI

---

## 2. Scope

### 2.1 In Scope

- TypeScript/JavaScript コードからのDFG/CFG抽出
- 変数・関数間の依存関係分析
- YATA知識グラフへのDFG統合
- LLMコンテキスト生成
- CLI/API提供

### 2.2 Out of Scope

- 他言語（Python, Java等）のサポート（将来拡張）
- IDE統合（Phase 3で実施）
- リアルタイム解析（Phase 3で実施）

---

## 3. Functional Requirements (EARS Format)

### 3.1 DFG Extraction (REQ-DFG-EXTRACT)

#### REQ-DFG-EXTRACT-001: Basic DFG Extraction
**Pattern**: Event-driven  
**Priority**: P0  

WHEN a TypeScript/JavaScript source file is provided,  
THE system SHALL extract a Data Flow Graph representing all variable definitions and their usages.

**Acceptance Criteria**:
- 変数定義（VariableDeclaration）を正確に識別
- 変数使用（Identifier参照）を追跡
- def-use チェーンを構築
- 精度 > 95%

#### REQ-DFG-EXTRACT-002: Function Call Analysis
**Pattern**: Event-driven  
**Priority**: P0  

WHEN a function call is encountered in the source code,  
THE system SHALL track data flow through function parameters and return values.

**Acceptance Criteria**:
- 関数引数へのデータフロー追跡
- 戻り値のデータフロー追跡
- クロージャ内の変数キャプチャ検出

#### REQ-DFG-EXTRACT-003: Object Property Flow
**Pattern**: Event-driven  
**Priority**: P0  

WHEN object properties are accessed or modified,  
THE system SHALL track data flow through object property chains.

**Acceptance Criteria**:
- `obj.prop` 形式のプロパティアクセス追跡
- `obj['prop']` 形式のプロパティアクセス追跡
- スプレッド演算子（`...obj`）のフロー追跡

#### REQ-DFG-EXTRACT-004: Array Element Flow
**Pattern**: Event-driven  
**Priority**: P1  

WHEN array elements are accessed or modified,  
THE system SHALL track data flow through array indices where statically determinable.

**Acceptance Criteria**:
- 静的インデックスアクセスの追跡
- 配列メソッド（map, filter, reduce）のフロー追跡

---

### 3.2 CFG Extraction (REQ-DFG-CFG)

#### REQ-DFG-CFG-001: Basic Control Flow
**Pattern**: Event-driven  
**Priority**: P0  

WHEN a function or method body is analyzed,  
THE system SHALL construct a Control Flow Graph with basic blocks and edges.

**Acceptance Criteria**:
- 基本ブロック（BasicBlock）の識別
- 分岐エッジ（conditional, unconditional）の生成
- 入口・出口ノードの明示

#### REQ-DFG-CFG-002: Conditional Branch Analysis
**Pattern**: Event-driven  
**Priority**: P0  

WHEN if/else, switch, or ternary expressions are encountered,  
THE system SHALL create branch nodes with true/false edges and condition expressions in the CFG.

**Acceptance Criteria**:
- if/else 分岐の正確なモデリング
- switch 文の全ケース分岐
- 三項演算子の分岐表現

#### REQ-DFG-CFG-003: Loop Analysis
**Pattern**: Event-driven  
**Priority**: P0  

WHEN loop constructs (for, while, do-while, for-of, for-in) are encountered,  
THE system SHALL create back-edges and loop headers in the CFG.

**Acceptance Criteria**:
- ループヘッダーの識別
- バックエッジの生成
- break/continue による制御フローの正確なモデリング

#### REQ-DFG-CFG-004: Exception Handling
**Pattern**: Event-driven  
**Priority**: P1  

WHEN try/catch/finally blocks are encountered,  
THE system SHALL model exceptional control flow paths.

**Acceptance Criteria**:
- try ブロックから catch への例外エッジ
- finally ブロックへのフロー
- throw 文からの例外フロー

---

### 3.3 Dependency Analysis (REQ-DFG-DEP)

#### REQ-DFG-DEP-001: Variable Dependency Map
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL maintain a dependency map showing which variables depend on which other variables.

**Acceptance Criteria**:
- 直接依存の検出
- 推移的依存の計算
- 循環依存の検出と報告

#### REQ-DFG-DEP-002: Function Dependency Graph
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL build a function call graph showing dependencies between functions.

**Acceptance Criteria**:
- 直接呼び出し関係の抽出
- コールバック・高階関数の依存追跡
- 再帰呼び出しの検出

#### REQ-DFG-DEP-003: Module Dependency Analysis
**Pattern**: Event-driven  
**Priority**: P1  

WHEN import/export statements are analyzed,  
THE system SHALL track cross-module dependencies.

**Acceptance Criteria**:
- ESM import/export の追跡
- CommonJS require/module.exports の追跡
- 動的インポートの検出（静的解析可能な範囲）

---

### 3.4 YATA Integration (REQ-DFG-YATA)

#### REQ-DFG-YATA-001: DFG to Knowledge Graph
**Pattern**: Event-driven  
**Priority**: P1  

WHEN a DFG is extracted,  
THE system SHALL convert it to RDF triples compatible with YATA knowledge graph.

**Acceptance Criteria**:
- DFGノードをYATAエンティティに変換
- DFGエッジをYATA関係に変換
- 名前空間 `code:dfg` の使用

#### REQ-DFG-YATA-002: Incremental Update
**Pattern**: Event-driven  
**Priority**: P1  

WHEN source files are modified,  
THE system SHALL perform incremental updates to the knowledge graph.

**Acceptance Criteria**:
- 変更されたファイルのみ再解析
- 古いトリプルの削除と新規トリプルの追加
- 整合性の維持

#### REQ-DFG-YATA-003: Query Support
**Pattern**: Event-driven  
**Priority**: P1  

WHEN a user queries data flow information,  
THE system SHALL support SPARQL-like queries against the DFG knowledge graph.

**Acceptance Criteria**:
- 「変数Xに影響を与える変数を列挙」
- 「関数Fの呼び出し元を列挙」
- 「循環依存を検出」

---

### 3.5 LLM Context Generation (REQ-DFG-LLM)

#### REQ-DFG-LLM-001: Context Serialization
**Pattern**: Event-driven  
**Priority**: P1  

WHEN LLM context is requested,  
THE system SHALL serialize relevant DFG/CFG information into a format suitable for LLM prompts.

**Acceptance Criteria**:
- トークン効率の良い表現
- 重要度に基づく情報の選別
- コンテキストウィンドウサイズへの適応

#### REQ-DFG-LLM-002: Relevance Filtering
**Pattern**: Optional  
**Priority**: P2  

IF a specific code location is specified,  
THEN THE system SHALL filter DFG/CFG to include only nodes within a configurable hop distance (default: 3 hops).

**Acceptance Criteria**:
- ホップ数による範囲限定（1-10ホップ設定可能）
- 重要度スコアによるフィルタリング（閾値0.0-1.0）

---

### 3.6 CLI Interface (REQ-DFG-CLI)

#### REQ-DFG-CLI-001: Extract Command
**Pattern**: Event-driven  
**Priority**: P0  

WHEN the user executes `musubix-dfg extract <file>`,  
THE system SHALL extract and display DFG/CFG information.

**Acceptance Criteria**:
- JSON/GraphML/DOT 出力形式サポート
- --type オプションで DFG/CFG/both 選択
- --output オプションでファイル出力

#### REQ-DFG-CLI-002: Analyze Command
**Pattern**: Event-driven  
**Priority**: P1  

WHEN the user executes `musubix-dfg analyze <dir>`,  
THE system SHALL analyze a directory and report dependency information.

**Acceptance Criteria**:
- 循環依存の報告
- 複雑度メトリクスの表示
- 依存関係サマリー

#### REQ-DFG-CLI-003: Export Command
**Pattern**: Event-driven  
**Priority**: P1  

WHEN the user executes `musubix-dfg export --yata`,  
THE system SHALL export DFG to YATA knowledge graph.

**Acceptance Criteria**:
- YATA Local への直接エクスポート
- N-Triples/Turtle 形式でのファイル出力

---

### 3.7 API Interface (REQ-DFG-API)

#### REQ-DFG-API-001: Programmatic Access
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL provide a TypeScript API for programmatic DFG/CFG extraction and analysis.

**Acceptance Criteria**:
```typescript
import { DataFlowAnalyzer, ControlFlowAnalyzer } from '@nahisaho/musubix-dfg';

const dfgAnalyzer = new DataFlowAnalyzer();
const dfg = await dfgAnalyzer.analyze('src/file.ts');

const cfgAnalyzer = new ControlFlowAnalyzer();
const cfg = await cfgAnalyzer.analyze('src/file.ts');
```

#### REQ-DFG-API-002: Graph Traversal API
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL provide graph traversal utilities.

**Acceptance Criteria**:
- BFS/DFS トラバーサル
- パス検索（shortest path）
- 到達可能性分析

---

## 4. Non-Functional Requirements

### 4.1 Performance (REQ-DFG-PERF)

#### REQ-DFG-PERF-001: Analysis Speed
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL analyze a 1000-line TypeScript file in under 500ms.

#### REQ-DFG-PERF-002: Memory Efficiency
**Pattern**: Ubiquitous  
**Priority**: P1  

THE system SHALL use no more than 500MB of memory for analyzing a 100,000-line codebase.

### 4.2 Accuracy (REQ-DFG-ACC)

#### REQ-DFG-ACC-001: Extraction Accuracy
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL achieve >95% accuracy in DFG/CFG extraction on standard TypeScript codebases.

### 4.3 Compatibility (REQ-DFG-COMPAT)

#### REQ-DFG-COMPAT-001: TypeScript Version
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL support TypeScript 5.0+ syntax.

#### REQ-DFG-COMPAT-002: Node.js Version
**Pattern**: Ubiquitous  
**Priority**: P0  

THE system SHALL run on Node.js 20.0.0+.

---

## 5. Constraints

### 5.1 Technical Constraints

- TypeScript コンパイラAPI（ts-morph）を使用
- 静的解析のみ（実行時情報なし）
- 単一リポジトリスコープ

### 5.2 Business Constraints

- オープンソース（MIT License）
- 既存MUSUBIXパッケージとの互換性維持

---

## 6. Dependencies

| Dependency | Type | Description |
|------------|------|-------------|
| `@nahisaho/yata-local` | Internal | 知識グラフ統合 |
| `ts-morph` | External | TypeScript AST操作 |
| `typescript` | External | TypeScriptコンパイラ |

---

## 7. Traceability

| Requirement ID | Design ID | Test ID |
|---------------|-----------|---------|
| REQ-DFG-EXTRACT-001 | DES-DFG-EXTRACT-001 | TST-DFG-EXTRACT-001 |
| REQ-DFG-EXTRACT-002 | DES-DFG-EXTRACT-002 | TST-DFG-EXTRACT-002 |
| REQ-DFG-CFG-001 | DES-DFG-CFG-001 | TST-DFG-CFG-001 |
| REQ-DFG-YATA-001 | DES-DFG-YATA-001 | TST-DFG-YATA-001 |
| ... | ... | ... |

---

## 8. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-07 | SDD Agent | Initial draft |

---

**© 2026 MUSUBIX Project - Constitutional Article IV Compliant (EARS Format)**
