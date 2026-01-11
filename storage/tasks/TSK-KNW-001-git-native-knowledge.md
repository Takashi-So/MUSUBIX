# TSK-KNW-001: Git-Native Knowledge System タスク分解

| 項目 | 内容 |
|------|------|
| **タスクID** | TSK-KNW-001 |
| **設計参照** | DES-KNW-001 |
| **要件参照** | REQ-KNW-001〜007, REQ-POL-001〜007, REQ-ADR-001〜004 |
| **作成日** | 2026-01-11 |
| **見積もり合計** | 約32時間 |

---

## タスク一覧

### Phase A: パッケージ基盤（8時間）

| ID | タスク | 見積もり | 依存 | 優先度 |
|----|--------|---------|------|--------|
| TSK-A01 | `packages/knowledge/` パッケージスキャフォールド | 1h | - | P0 |
| TSK-A02 | `packages/policy/` パッケージスキャフォールド | 1h | - | P0 |
| TSK-A03 | `packages/decisions/` パッケージスキャフォールド | 1h | - | P0 |
| TSK-A04 | 共通型定義（`types.ts`） | 2h | A01-A03 | P0 |
| TSK-A05 | パッケージ間依存関係設定 | 1h | A04 | P0 |
| TSK-A06 | ビルド・テスト環境設定 | 2h | A05 | P0 |

---

### Phase B: Knowledge Store実装（10時間）

| ID | タスク | 見積もり | 依存 | 優先度 |
|----|--------|---------|------|--------|
| TSK-B01 | `KnowledgeStore` インターフェース定義 | 1h | A04 | P0 |
| TSK-B02 | `FileKnowledgeStore` 基本実装（CRUD） | 3h | B01 | P0 |
| TSK-B03 | リレーション管理実装 | 2h | B02 | P0 |
| TSK-B04 | クエリ・検索機能実装 | 2h | B02 | P1 |
| TSK-B05 | グラフ探索（traverse）実装 | 2h | B03 | P1 |

**テスト**: 各タスクでユニットテスト作成（Red-Green-Blue）

---

### Phase C: Policy Engine実装（8時間）

| ID | タスク | 見積もり | 依存 | 優先度 |
|----|--------|---------|------|--------|
| TSK-C01 | `Policy` インターフェース定義 | 1h | A04 | P0 |
| TSK-C02 | `PolicyEngine` 基本実装 | 2h | C01 | P0 |
| TSK-C03 | 9憲法ポリシー実装（CONST-001〜009） | 3h | C02 | P0 |
| TSK-C04 | カスタムポリシーローダー実装 | 1h | C02 | P1 |
| TSK-C05 | 自動修正（fix）機能実装 | 1h | C02 | P2 |

---

### Phase D: Decision Records実装（4時間）

| ID | タスク | 見積もり | 依存 | 優先度 |
|----|--------|---------|------|--------|
| TSK-D01 | `DecisionManager` インターフェース定義 | 0.5h | A04 | P0 |
| TSK-D02 | ADR CRUD実装 | 1.5h | D01 | P0 |
| TSK-D03 | ADRテンプレート・インデックス生成 | 1h | D02 | P0 |
| TSK-D04 | ADR検索機能実装 | 1h | D02 | P1 |

---

### Phase E: MCP統合（6時間）

| ID | タスク | 見積もり | 依存 | 優先度 |
|----|--------|---------|------|--------|
| TSK-E01 | Knowledge MCPツール実装（6ツール） | 2h | B05 | P0 |
| TSK-E02 | Policy MCPツール実装（4ツール） | 1.5h | C04 | P0 |
| TSK-E03 | Decision MCPツール実装（4ツール） | 1h | D03 | P0 |
| TSK-E04 | 既存`validateConstitutionTool`統合 | 1h | E02 | P0 |
| TSK-E05 | MCPツールテスト | 0.5h | E01-E04 | P0 |

---

### Phase F: CLI統合（4時間）

| ID | タスク | 見積もり | 依存 | 優先度 |
|----|--------|---------|------|--------|
| TSK-F01 | `musubix knowledge` コマンド実装 | 1.5h | B05 | P1 |
| TSK-F02 | `musubix policy` コマンド実装 | 1h | C04 | P1 |
| TSK-F03 | `musubix decision` コマンド実装 | 1h | D03 | P1 |
| TSK-F04 | `musubix init` 拡張 | 0.5h | F01-F03 | P0 |

---

### Phase G: ドキュメント・仕上げ（2時間）

| ID | タスク | 見積もり | 依存 | 優先度 |
|----|--------|---------|------|--------|
| TSK-G01 | AGENTS.md 更新（新ツール追記） | 0.5h | E05 | P0 |
| TSK-G02 | README更新 | 0.5h | G01 | P1 |
| TSK-G03 | CHANGELOG更新 | 0.5h | G02 | P0 |
| TSK-G04 | 統合テスト実行・修正 | 0.5h | G01-G03 | P0 |

---

## 実行順序（依存関係グラフ）

```
Phase A: パッケージ基盤
  A01 ─┬─▶ A04 ─▶ A05 ─▶ A06
  A02 ─┤
  A03 ─┘

Phase B: Knowledge Store
  A04 ─▶ B01 ─▶ B02 ─┬─▶ B04
                     └─▶ B03 ─▶ B05

Phase C: Policy Engine
  A04 ─▶ C01 ─▶ C02 ─┬─▶ C03
                     ├─▶ C04
                     └─▶ C05

Phase D: Decision Records
  A04 ─▶ D01 ─▶ D02 ─┬─▶ D03
                     └─▶ D04

Phase E: MCP統合
  B05 ─▶ E01 ─┐
  C04 ─▶ E02 ─┼─▶ E05
  D03 ─▶ E03 ─┤
  E02 ─▶ E04 ─┘

Phase F: CLI統合
  B05 ─▶ F01 ─┐
  C04 ─▶ F02 ─┼─▶ F04
  D03 ─▶ F03 ─┘

Phase G: ドキュメント
  E05 ─▶ G01 ─▶ G02 ─▶ G03 ─▶ G04
```

---

## 並列実行可能なタスク

| ステップ | 並列実行タスク |
|---------|---------------|
| Step 1 | A01, A02, A03 |
| Step 2 | A04 |
| Step 3 | A05 |
| Step 4 | A06, B01, C01, D01 |
| Step 5 | B02, C02, D02 |
| Step 6 | B03, B04, C03, C04, D03, D04 |
| Step 7 | B05, C05 |
| Step 8 | E01, E02, E03, F01, F02, F03 |
| Step 9 | E04, E05, F04 |
| Step 10 | G01 |
| Step 11 | G02, G03 |
| Step 12 | G04 |

---

## タスク詳細

### TSK-A01: `packages/knowledge/` パッケージスキャフォールド

**入力**: なし
**出力**:
```
packages/knowledge/
├── package.json
├── tsconfig.json
├── src/
│   └── index.ts
└── __tests__/
    └── index.test.ts
```

**受入条件**:
- [x] `npm run build` 成功
- [x] `npm test` 成功（空テスト）
- [x] モノレポから参照可能

---

### TSK-B02: `FileKnowledgeStore` 基本実装

**入力**: TSK-B01のインターフェース
**出力**:
```typescript
// packages/knowledge/src/store.ts
export class FileKnowledgeStore implements KnowledgeStore {
  constructor(basePath: string);
  
  async getEntity(id: string): Promise<Entity | undefined>;
  async putEntity(entity: Entity): Promise<void>;
  async deleteEntity(id: string): Promise<boolean>;
  async save(): Promise<void>;
  async load(): Promise<void>;
}
```

**受入条件**:
- [x] CRUD操作が正常動作
- [x] `.knowledge/graph.json` への永続化
- [x] バリデーション（重複ID検出等）
- [x] ユニットテスト10件以上

---

### TSK-C03: 9憲法ポリシー実装

**入力**: TSK-C02のPolicyEngine
**出力**:
```typescript
// packages/policy/src/builtin/constitution.ts
export const constitutionPolicies: Policy[] = [
  // CONST-001: Library-First
  // CONST-002: CLI Interface
  // ...
  // CONST-009: Quality Gates
];
```

**受入条件**:
- [x] 9ポリシーすべて実装
- [x] 各ポリシーのvalidate()が動作
- [x] steering/rules/constitution.md との整合性
- [x] ユニットテスト各ポリシー2件以上

---

### TSK-E04: 既存`validateConstitutionTool`統合

**入力**: TSK-E02完了
**出力**:
```typescript
// packages/mcp-server/src/tools/sdd-tools.ts
// validateConstitutionTool を @musubix/policy に委譲
```

**受入条件**:
- [x] 既存APIの後方互換性維持
- [x] 内部実装が@musubix/policyを使用
- [x] 既存テストがパス

---

## トレーサビリティ

| タスクID | 設計セクション | 要件ID |
|---------|---------------|--------|
| TSK-B02 | 3.1 Knowledge Store | REQ-KNW-001 |
| TSK-B03 | 3.1.3 API設計 | REQ-KNW-003 |
| TSK-B04 | 3.1.3 API設計 | REQ-KNW-002 |
| TSK-B05 | 3.1.3 API設計 | REQ-KNW-005 |
| TSK-C02 | 3.2 Policy Engine | REQ-POL-001 |
| TSK-C03 | 3.2.3 組み込みポリシー | REQ-POL-003 |
| TSK-C04 | 3.2.4 API設計 | REQ-POL-005 |
| TSK-D02 | 3.3 Decision Records | REQ-ADR-001 |
| TSK-D03 | 3.3.2 ADRテンプレート | REQ-ADR-002 |
| TSK-E01 | 5.1 Knowledge ツール | REQ-KNW-001〜007 |
| TSK-E02 | 5.2 Policy ツール | REQ-POL-001〜007 |
| TSK-E03 | 5.3 Decision ツール | REQ-ADR-001〜004 |
| TSK-F04 | 12.1 musubix init拡張 | REQ-INIT-001 |

---

**作成日**: 2026-01-11
**ステータス**: Draft
