# Budget Tracker System - タスク分解

**Project ID**: project-13-budget-tracker
**Document ID**: TSK-001
**Created**: 2026-01-04
**Status**: Approved

---

## タスク一覧

### Sprint 1: Foundation（基盤構築）

| Task ID | タスク名 | 依存 | 優先度 | 見積 | 要件ID |
|---------|---------|------|--------|------|--------|
| TSK-001 | プロジェクト初期設定 | - | P0 | 0.5h | - |
| TSK-002 | Money Value Object 実装 | TSK-001 | P0 | 1h | REQ-001 §2.1 |
| TSK-003 | BudgetPeriod Value Object 実装 | TSK-001 | P0 | 1h | REQ-001 §2.2 |
| TSK-004 | BudgetStatus 実装 | TSK-002 | P0 | 0.5h | REQ-BT-022, 023 |

### Sprint 2: Entities & Repositories

| Task ID | タスク名 | 依存 | 優先度 | 見積 | 要件ID |
|---------|---------|------|--------|------|--------|
| TSK-005 | User Entity 実装 | TSK-001 | P0 | 1h | REQ-BT-040 |
| TSK-006 | Category Entity 実装 | TSK-002, TSK-003 | P0 | 1.5h | REQ-BT-001 |
| TSK-007 | Expense Entity 実装 | TSK-002, TSK-006 | P0 | 1.5h | REQ-BT-010 |
| TSK-008 | Alert Entity 実装 | TSK-003, TSK-006 | P1 | 1h | REQ-BT-030 |
| TSK-009 | Repository Interfaces 定義 | TSK-005〜008 | P0 | 1h | - |
| TSK-010 | JSON Storage 実装 | TSK-009 | P0 | 2h | - |

### Sprint 3: Core Services

| Task ID | タスク名 | 依存 | 優先度 | 見積 | 要件ID |
|---------|---------|------|--------|------|--------|
| TSK-011 | AuthService 実装 | TSK-005, TSK-010 | P0 | 2h | REQ-BT-040〜042 |
| TSK-012 | CategoryService 実装 | TSK-006, TSK-010 | P0 | 2h | REQ-BT-001〜004 |
| TSK-013 | ExpenseService 実装 | TSK-007, TSK-012 | P0 | 2h | REQ-BT-010〜013 |
| TSK-014 | AnalysisService 実装 | TSK-012, TSK-013 | P0 | 2h | REQ-BT-020, 021 |
| TSK-015 | AlertService 実装 | TSK-008, TSK-012 | P1 | 2h | REQ-BT-030〜033 |

### Sprint 4: CLI & Integration

| Task ID | タスク名 | 依存 | 優先度 | 見積 | 要件ID |
|---------|---------|------|--------|------|--------|
| TSK-016 | CLI基盤実装 | TSK-011 | P0 | 1h | Article II |
| TSK-017 | Auth CLI コマンド | TSK-011, TSK-016 | P0 | 1h | REQ-BT-040〜042 |
| TSK-018 | Category CLI コマンド | TSK-012, TSK-016 | P0 | 1h | REQ-BT-001〜004 |
| TSK-019 | Expense CLI コマンド | TSK-013, TSK-016 | P0 | 1h | REQ-BT-010〜013 |
| TSK-020 | Analysis CLI コマンド | TSK-014, TSK-016 | P0 | 1h | REQ-BT-020, 021 |
| TSK-021 | Alert CLI コマンド | TSK-015, TSK-016 | P1 | 1h | REQ-BT-030〜033 |
| TSK-022 | 統合テスト | TSK-017〜021 | P0 | 2h | - |

---

## タスク詳細

### TSK-001: プロジェクト初期設定

**説明**: プロジェクトの基本構造とビルド設定を構築

**成果物**:
- package.json
- tsconfig.json
- vitest.config.ts
- ディレクトリ構造

**完了条件**:
- [x] `npm install` が成功
- [x] `npm run build` が成功
- [x] `npm test` が実行可能

---

### TSK-002: Money Value Object 実装

**説明**: 金額を表すイミュータブルなValue Objectを実装

**成果物**:
- src/domain/value-objects/money.ts
- tests/domain/value-objects/money.test.ts

**実装詳細**:
```typescript
// 主要メソッド
- Money.create(amount: number): Result<Money, ValidationError>
- Money.zero(): Money
- add(other: Money): Money
- subtract(other: Money): Money
- percentage(total: Money): number
- toNumber(): number
- equals(other: Money): boolean
```

**完了条件**:
- [ ] 1〜999,999,999の範囲チェック
- [ ] 整数のみ許可
- [ ] 四則演算の正確性
- [ ] パーセンテージ計算
- [ ] テストカバレッジ100%

---

### TSK-003: BudgetPeriod Value Object 実装

**説明**: 予算期間（年月）を表すValue Objectを実装

**成果物**:
- src/domain/value-objects/budget-period.ts
- tests/domain/value-objects/budget-period.test.ts

**実装詳細**:
```typescript
// 主要メソッド
- BudgetPeriod.current(): BudgetPeriod
- BudgetPeriod.fromDate(date: Date): BudgetPeriod
- BudgetPeriod.fromYearMonth(year, month): Result<BudgetPeriod, ValidationError>
- getStartDate(): Date
- getEndDate(): Date
- equals(other: BudgetPeriod): boolean
- toString(): string
```

**完了条件**:
- [ ] 月の範囲チェック（1-12）
- [ ] 月初・月末の正確な計算
- [ ] タイムゾーン対応（JST）
- [ ] テストカバレッジ100%

---

### TSK-006: Category Entity 実装

**説明**: 予算カテゴリエンティティと関連ロジックを実装

**成果物**:
- src/domain/entities/category.ts
- tests/domain/entities/category.test.ts

**実装詳細**:
```typescript
interface Category {
  id: CategoryId;
  userId: UserId;
  name: string;
  description: string;
  monthlyLimit: Money;
  status: CategoryStatus;
  createdAt: Date;
  updatedAt: Date;
}

// Factory
function createCategory(input: CreateCategoryInput): Result<Category, ValidationError>

// ID生成
function generateCategoryId(): CategoryId
function resetCategoryCounter(): void  // テスト用
```

**完了条件**:
- [ ] バリデーション（名前1-50文字、金額範囲）
- [ ] Status Transition Map の実装
- [ ] ID生成とカウンターリセット
- [ ] テストカバレッジ100%

---

### TSK-012: CategoryService 実装

**説明**: カテゴリ管理のビジネスロジックを実装

**成果物**:
- src/application/category-service.ts
- tests/application/category-service.test.ts

**実装詳細**:
```typescript
class CategoryService {
  constructor(
    private readonly categoryRepository: CategoryRepository,
    private readonly expenseRepository: ExpenseRepository
  ) {}

  async create(userId: UserId, input: CreateCategoryInput): Promise<Result<Category, DomainError>>
  async list(userId: UserId): Promise<CategoryWithSpending[]>
  async update(userId: UserId, categoryId: CategoryId, input: UpdateCategoryInput): Promise<Result<Category, DomainError>>
  async archive(userId: UserId, categoryId: CategoryId): Promise<Result<void, DomainError>>
}
```

**完了条件**:
- [ ] カテゴリ作成（重複名チェック）
- [ ] 一覧取得（支出額計算込み）
- [ ] 更新（部分更新対応）
- [ ] アーカイブ（論理削除）
- [ ] テストカバレッジ80%以上

---

## 依存関係図

```
TSK-001 (プロジェクト設定)
    │
    ├──▶ TSK-002 (Money VO)
    │        │
    │        ├──▶ TSK-004 (BudgetStatus)
    │        │
    │        └──▶ TSK-006 (Category Entity)
    │                 │
    │                 └──▶ TSK-007 (Expense Entity)
    │                          │
    │                          └──▶ TSK-008 (Alert Entity)
    │
    ├──▶ TSK-003 (BudgetPeriod VO)
    │        │
    │        └──▶ TSK-006, TSK-008
    │
    └──▶ TSK-005 (User Entity)
             │
             └──▶ TSK-009 (Repository IF)
                      │
                      └──▶ TSK-010 (JSON Storage)
                               │
                               ├──▶ TSK-011 (AuthService)
                               ├──▶ TSK-012 (CategoryService)
                               ├──▶ TSK-013 (ExpenseService)
                               ├──▶ TSK-014 (AnalysisService)
                               └──▶ TSK-015 (AlertService)
                                        │
                                        └──▶ TSK-016〜022 (CLI & 統合)
```

---

## 見積もりサマリー

| Sprint | タスク数 | 合計見積 |
|--------|---------|---------|
| Sprint 1 | 4 | 3h |
| Sprint 2 | 6 | 8h |
| Sprint 3 | 5 | 10h |
| Sprint 4 | 7 | 8h |
| **合計** | **22** | **29h** |

---

**Approval**:
- [x] タスク分解完了
- [x] 依存関係明確
- [x] 見積もり妥当
- [x] Ready for Implementation
