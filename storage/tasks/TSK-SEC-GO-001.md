# タスク分解書: Go言語セキュリティエクストラクター

**Document ID**: TSK-SEC-GO-001  
**Version**: 1.0.0  
**Created**: 2026-01-12  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft (レビュー待ち)  
**Requirements**: REQ-SEC-GO-001  
**Design**: DES-SEC-GO-001

---

## 1. トレーサビリティ

| 要件ID | 設計ID | タスクID |
|--------|--------|----------|
| REQ-SEC-GO-001 | DES-SEC-GO-001 | TSK-GO-001 |
| REQ-SEC-GO-002 | DES-SEC-GO-001 | TSK-GO-002 |
| REQ-SEC-GO-003 | DES-SEC-GO-001 | TSK-GO-003 |
| REQ-SEC-GO-004 | DES-SEC-GO-001 | TSK-GO-003 |
| REQ-SEC-GO-005 | DES-SEC-GO-001 | TSK-GO-003 |
| REQ-SEC-GO-006 | DES-SEC-GO-001 | TSK-GO-003 |
| REQ-SEC-GO-007 | DES-SEC-GO-001 | TSK-GO-004 |
| REQ-SEC-GO-008 | DES-SEC-GO-001 | TSK-GO-005 |

---

## 2. タスク一覧

### TSK-GO-001: GoExtractor基本構造実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-001 |
| **タイトル** | GoExtractor基本構造とtree-sitter統合 |
| **説明** | GoExtractorクラスの基本構造を実装。BaseExtractor継承、tree-sitter-go統合、フォールバックAST |
| **成果物** | `packages/security/src/extractors/go-extractor.ts` (基本部分 ~200行) |
| **依存タスク** | なし |
| **見積もり** | 1時間 |
| **受入基準** | - GoExtractorクラスが作成される<br>- `language: 'go'`, `extensions: ['.go']` が設定される<br>- `supports()` が`.go`ファイルを正しく判定<br>- tree-sitter未インストール時にフォールバック |

**実装内容**:
```typescript
export class GoExtractor extends BaseExtractor {
  readonly language: SupportedLanguage = 'go';
  readonly extensions: string[] = ['.go'];
  
  private parser: TreeSitterParser | null = null;
  private nodeIdCounter = 0;
  private blockIdCounter = 0;

  private async initParser(): Promise<void> { ... }
  private createFallbackAST(...): ASTNode { ... }
  protected async buildAST(...): Promise<ASTBuildResult> { ... }
}
```

---

### TSK-GO-002: AST構築実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-002 |
| **タイトル** | AST構築とノード変換 |
| **説明** | tree-sitter-goノードをASTNode形式に変換。Go固有のノードプロパティ抽出 |
| **成果物** | `go-extractor.ts` buildAST, convertTreeSitterNode, extractNodeProperties (~150行追加) |
| **依存タスク** | TSK-GO-001 |
| **見積もり** | 1時間 |
| **受入基準** | - `buildAST()` がASTNode, astNodes Map, astEdgesを返す<br>- Go固有ノードタイプ（function_declaration等）が正しく変換 |

**実装内容**:
```typescript
private convertTreeSitterNode(
  node: TreeSitterNode,
  filePath: string,
  astNodes: Map<string, ASTNode>,
  astEdges: ASTEdge[]
): ASTNode { ... }

private extractNodeProperties(node: TreeSitterNode): Record<string, unknown> {
  // function_declaration, method_declaration, type_declaration 等
}
```

---

### TSK-GO-003: フレームワークモデルとDFG構築

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-003 |
| **タイトル** | 10個のフレームワークモデル定義とDFG構築 |
| **説明** | Go固有のソース/シンク/サニタイザーパターンを定義し、DFGを構築 |
| **成果物** | `go-extractor.ts` GO_FRAMEWORK_MODELS, buildDFG (~250行追加) |
| **依存タスク** | TSK-GO-002 |
| **見積もり** | 1.5時間 |
| **受入基準** | - `getFrameworkModels()` が10モデルを返す<br>- ソース検出: r.FormValue, os.Args 等<br>- シンク検出: db.Query, exec.Command, os.Open 等<br>- サニタイザー検出: filepath.Clean, html.EscapeString 等 |

**フレームワークモデル一覧**:
1. `net/http` - 標準HTTPライブラリ
2. `database/sql` - 標準データベース
3. `os/exec` - コマンド実行
4. `os` - ファイル操作
5. `encoding/xml` - XML処理
6. `Gin` - Ginフレームワーク
7. `Echo` - Echoフレームワーク
8. `Fiber` - Fiberフレームワーク
9. `GORM` - GORM ORM
10. `Go SSRF` - SSRFパターン

---

### TSK-GO-004: CFG構築

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-004 |
| **タイトル** | Control Flow Graph構築 |
| **説明** | Go制御構造（if, for, switch, select, defer, go）をCFGに変換 |
| **成果物** | `go-extractor.ts` buildCFG (~100行追加) |
| **依存タスク** | TSK-GO-002 |
| **見積もり** | 45分 |
| **受入基準** | - `buildCFG()` がControlFlowGraphを返す<br>- if/for/switch文が正しくBasicBlockに変換<br>- エントリ/エグジットブロックが設定される |

**実装内容**:
```typescript
protected async buildCFG(
  astNodes: Map<string, ASTNode>,
  astEdges: ASTEdge[]
): Promise<ControlFlowGraph> {
  // if_statement, for_statement, switch_statement 等の処理
}
```

---

### TSK-GO-005: Symbol Table構築

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-005 |
| **タイトル** | Symbol Table構築とエクスポート判定 |
| **説明** | Go シンボル（func, type, var, const）抽出。大文字始まりのエクスポート判定 |
| **成果物** | `go-extractor.ts` extractSymbols, isExported (~100行追加) |
| **依存タスク** | TSK-GO-002 |
| **見積もり** | 45分 |
| **受入基準** | - `extractSymbols()` がSymbolTableを返す<br>- 関数、型、変数が正しく分類<br>- `isExported()` が大文字始まりを判定 |

**実装内容**:
```typescript
protected async extractSymbols(
  astNodes: Map<string, ASTNode>
): Promise<SymbolTable> { ... }

private isExported(name: string): boolean {
  return /^[A-Z]/.test(name);
}
```

---

### TSK-GO-006: index.ts更新

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-006 |
| **タイトル** | エクスポート追加とファクトリ更新 |
| **説明** | GoExtractorをindex.tsにエクスポート。createExtractor, getSupportedLanguages更新 |
| **成果物** | `packages/security/src/extractors/index.ts` 更新 |
| **依存タスク** | TSK-GO-001〜005 |
| **見積もり** | 15分 |
| **受入基準** | - `GoExtractor`, `createGoExtractor` がエクスポートされる<br>- `createExtractor('go')` がGoExtractorを返す |

---

### TSK-GO-007: テスト実装

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-007 |
| **タイトル** | GoExtractorユニットテスト |
| **説明** | 17テストケースを実装 |
| **成果物** | `packages/security/tests/go-extractor.test.ts` (~200行) |
| **依存タスク** | TSK-GO-006 |
| **見積もり** | 1時間 |
| **受入基準** | - 17テストケース全合格<br>- コンストラクタ、supports、getFrameworkModels、extract、ソース/シンク検出テスト |

**テストケース**:
1. コンストラクタ - インスタンス生成
2. createGoExtractor factory
3. supports - `.go`ファイル判定
4. getFrameworkModels - 10モデル返却
5. extract - シンプルGoコード
6. ソース検出 - r.FormValue()
7. ソース検出 - os.Args
8. シンク検出 - db.Query() SQL injection
9. シンク検出 - exec.Command() command injection
10. シンク検出 - os.Open() path traversal
11. サニタイザー - filepath.Clean()
12. CFG - if文
13. CFG - for文
14. Symbols - 関数抽出
15. Symbols - エクスポート判定
16. Gin - c.Query() ソース
17. GORM - Raw() シンク

---

### TSK-GO-008: リリース準備

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-GO-008 |
| **タイトル** | v3.0.14リリース準備 |
| **説明** | バージョン更新、CHANGELOG更新、ビルド・テスト確認 |
| **成果物** | 全package.json更新、CHANGELOG.md更新 |
| **依存タスク** | TSK-GO-007 |
| **見積もり** | 30分 |
| **受入基準** | - 全パッケージバージョンが3.0.14<br>- CHANGELOG.md にv3.0.14セクション追加<br>- `npm run build` 成功<br>- `npm run test --workspace=packages/security` 全合格 |

---

## 3. 実行順序

```
TSK-GO-001 (基本構造)
    │
    ▼
TSK-GO-002 (AST構築)
    │
    ├────────┬────────┐
    ▼        ▼        ▼
TSK-GO-003 TSK-GO-004 TSK-GO-005
(DFG)      (CFG)      (Symbols)
    │        │        │
    └────────┴────────┘
             │
             ▼
      TSK-GO-006 (index.ts)
             │
             ▼
      TSK-GO-007 (テスト)
             │
             ▼
      TSK-GO-008 (リリース)
```

---

## 4. 工数見積もり

| タスクID | 見積もり |
|----------|----------|
| TSK-GO-001 | 1時間 |
| TSK-GO-002 | 1時間 |
| TSK-GO-003 | 1.5時間 |
| TSK-GO-004 | 45分 |
| TSK-GO-005 | 45分 |
| TSK-GO-006 | 15分 |
| TSK-GO-007 | 1時間 |
| TSK-GO-008 | 30分 |
| **合計** | **約6.75時間** |

---

## 5. リスクと対策

| リスク | 対策 |
|--------|------|
| tree-sitter-go動的インポート失敗 | try/catchでフォールバック |
| Go構文の複雑さ | 基本パターンから段階的に実装 |
| テスト実行時間増大 | 並列実行維持 |

---

## 6. 受入基準（全体）

1. ✅ GoExtractorがBaseExtractor抽象クラスを正しく実装
2. ✅ 10個のフレームワークモデルが定義済み
3. ✅ 17テストケース全合格
4. ✅ 既存テスト（1102件）全合格
5. ✅ v3.0.14としてリリース可能

---

**Document End**
