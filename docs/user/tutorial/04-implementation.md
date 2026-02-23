# チュートリアル Part 4: 実装

> 所要時間: 約30分
> 前提: [Part 3: 設計](03-design.md) が完了し、承認済みであること

---

## 1. タスク分解（Phase 3）

まず、設計をタスクに分解します。AIエージェントに以下のように話しかけます：

```
実装タスクに分解して
```

### 内部で起きること

AIエージェントが `sdd_task_decomposition` を使用し、設計ファイル（DES-*）から実装タスクを生成します。

### 生成されるタスクリストの例

**基盤設定:**

| # | タスク | 内容 |
|---|--------|------|
| 1 | プロジェクト初期設定 | package.json, tsconfig.json, Vitest設定 |
| 2 | ドメインモデル定義 | Equipment, BorrowRecord型の定義 |

**コア機能（P0）:**

| # | タスク | 対応する要件 |
|---|--------|-------------|
| 3 | 備品ID生成ロジック | REQ-EQUIP-001-02（EQ-YYYYMMDD-NNN形式） |
| 4 | 備品登録機能 | REQ-EQUIP-001-01 |
| 5 | 備品検索機能 | REQ-EQUIP-001-03 |
| 6 | 貸出記録機能 | REQ-EQUIP-001-04 |
| 7 | 返却記録機能 | REQ-EQUIP-001-05 |
| 8 | 貸出中重複防止 | REQ-EQUIP-001-06 |
| 9 | 廃棄記録機能 | REQ-EQUIP-001-07 |
| 10 | 廃棄済み貸出防止 | REQ-EQUIP-001-08 |

**インフラ・テスト:**

| # | タスク | 内容 |
|---|--------|------|
| 11 | JSON永続化層 | ローカルストレージ |
| 12 | CLIインターフェース | 憲法 Article II準拠 |
| 13 | ユニットテスト | 各機能のテスト |
| 14 | 統合テスト | E2Eテスト |

### タスクの承認

タスクリストを確認して問題なければ：

```
承認
```

これで Phase 4（実装）に進めます。

---

## 2. 実装の開始

AIエージェントに以下のように話しかけます：

```
実装を開始して
```

### 実装の進め方（Red-Green-Blue）

AIエージェントは各タスクを以下のサイクルで進めます：

```
1. Red:   テストを書く（失敗する状態）
2. Green: テストが通る最小限の実装
3. Blue:  リファクタリング
```

### 実装例: 備品ID生成（TSK-003）

**Red（テストを先に書く）:**

```typescript
// equipment-id.test.ts
describe('generateEquipmentId', () => {
  it('should generate ID in EQ-YYYYMMDD-NNN format', () => {
    const id = generateEquipmentId();
    expect(id).toMatch(/^EQ-\d{8}-\d{3}$/);
  });

  it('should increment counter for same date', () => {
    const id1 = generateEquipmentId();
    const id2 = generateEquipmentId();
    // 同じ日付なら連番が増える
    const num1 = parseInt(id1.split('-')[2]);
    const num2 = parseInt(id2.split('-')[2]);
    expect(num2).toBe(num1 + 1);
  });
});
```

**Green（テストが通る実装）:**

```typescript
// equipment-id.ts
let counter = 0;
let lastDate = '';

export function generateEquipmentId(): string {
  const today = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  if (today !== lastDate) {
    counter = 0;
    lastDate = today;
  }
  counter++;
  return `EQ-${today}-${String(counter).padStart(3, '0')}`;
}

export function resetEquipmentIdCounter(): void {
  counter = 0;
  lastDate = '';
}
```

**Blue（リファクタリング）:**
- テストにresetCounter()のbeforeEach追加
- 型をResult<T, E>パターンに変更（ベストプラクティスBP-CODE-005）

### 実装のベストプラクティス

MUSUBIXが学習済みのベストプラクティスが自動適用されます：

| ID | パターン | 適用箇所 |
|----|---------|---------|
| BP-CODE-001 | Entity Input DTO | 備品登録の入力型 |
| BP-CODE-002 | Date-based ID Format | EQ-YYYYMMDD-NNN |
| BP-CODE-004 | Function-based Value Objects | Price, EquipmentId |
| BP-CODE-005 | Result Type | 失敗可能な操作の戻り値 |
| BP-DESIGN-001 | Status Transition Map | 備品ステータス遷移 |
| BP-DESIGN-006 | Entity Counter Reset | テスト用のresetCounter() |

---

## 3. 進捗の確認

実装中にAIエージェントに進捗を確認できます：

```
進捗を確認して
```

### 進捗表示の例

```
実装進捗:
✅ TSK-001: プロジェクト初期設定
✅ TSK-002: ドメインモデル定義
✅ TSK-003: 備品ID生成ロジック
🔄 TSK-004: 備品登録機能（実装中）
⬜ TSK-005: 備品検索機能
⬜ TSK-006: 貸出記録機能
...

進捗: 3/14 (21%)
```

---

## 4. コード生成（スケルトン）

設計から一括でスケルトンコードを生成することもできます：

```
設計からスケルトンコードを生成して
```

### 内部で起きること

`musubix codegen generate storage/design/DES-EQUIP-001.md` が実行されます。

### 生成されるファイルの例

```
src/
├── domain/
│   ├── equipment.ts           # Equipmentエンティティ
│   ├── borrow-record.ts       # BorrowRecordエンティティ
│   ├── equipment-id.ts        # ID生成（Value Object）
│   └── equipment-status.ts    # ステータス遷移マップ
├── application/
│   └── equipment-service.ts   # EquipmentService
├── infrastructure/
│   └── equipment-repository.ts # EquipmentRepository
└── interface/
    └── cli.ts                 # CLIインターフェース
```

## このパートのまとめ

| 項目 | 結果 |
|------|------|
| タスク数 | 14タスク |
| 実装サイクル | Red-Green-Blue |
| ベストプラクティス | 6パターン自動適用 |
| 成果物 | `src/` 以下の実装コード + テスト |

### 学んだこと

- 設計から実装に進む前に、必ずタスク分解が必要
- 各タスクはRed-Green-Blue（テスト先行）で進む
- MUSUBIXのベストプラクティスが自動適用される
- スケルトンコードの一括生成も可能

---

**前へ**: [Part 3: 設計](03-design.md) | **次へ**: [Part 5: 検証](05-verification.md)
