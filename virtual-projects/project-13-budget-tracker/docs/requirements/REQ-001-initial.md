# Budget Tracker System - 要件定義書 v1.0

**Project ID**: project-13-budget-tracker
**Document ID**: REQ-001
**Version**: 1.0 (Initial Draft)
**Created**: 2026-01-04
**Status**: Draft - Pending Review

---

## 1. ビジネス概要

### 1.1 プロジェクト目的
個人およびチーム向けの予算管理システムを構築し、収支の可視化と予算遵守を支援する。

### 1.2 ビジネス目標
- 予算計画の立案と追跡を容易にする
- 支出パターンの分析により節約機会を特定する
- 予算超過を事前に警告し、財務健全性を維持する

### 1.3 ステークホルダー
| ステークホルダー | 関心事 |
|-----------------|--------|
| エンドユーザー | 簡単な予算管理、直感的なUI |
| システム管理者 | 安定稼働、データ保全 |
| 開発チーム | 保守性、拡張性 |

---

## 2. 機能要件（EARS形式）

### 2.1 予算カテゴリ管理

#### REQ-BT-001: カテゴリ作成
**Priority**: P0 (必須)
**EARS Pattern**: Event-driven

```
WHEN a user requests to create a budget category,
THE system SHALL create a new category with name, description, and monthly limit,
AND assign a unique category ID in format CAT-YYYYMMDD-NNN.
```

**Acceptance Criteria**:
- カテゴリ名は1-50文字
- 月間上限金額は0より大きい正の数
- 同一ユーザー内でカテゴリ名の重複不可

#### REQ-BT-002: カテゴリ一覧取得
**Priority**: P0 (必須)
**EARS Pattern**: Event-driven

```
WHEN a user requests their budget categories,
THE system SHALL return all categories owned by the user,
AND include current month spending amount for each category.
```

#### REQ-BT-003: カテゴリ更新
**Priority**: P1 (重要)
**EARS Pattern**: Event-driven

```
WHEN a user requests to update a budget category,
THE system SHALL update the category's name, description, or monthly limit,
AND preserve the category's spending history.
```

#### REQ-BT-004: カテゴリ削除
**Priority**: P1 (重要)
**EARS Pattern**: Event-driven

```
WHEN a user requests to delete a budget category,
THE system SHALL mark the category as archived,
AND NOT allow new expenses to be recorded to the archived category.
```

**Note**: 物理削除ではなく論理削除（アーカイブ）を採用

---

### 2.2 支出記録管理

#### REQ-BT-010: 支出記録作成
**Priority**: P0 (必須)
**EARS Pattern**: Event-driven

```
WHEN a user records an expense,
THE system SHALL create an expense record with amount, category, date, and description,
AND assign a unique expense ID in format EXP-YYYYMMDD-NNN.
```

**Acceptance Criteria**:
- 金額は0.01以上の正の数
- 日付は過去または当日のみ許可
- カテゴリは既存の有効なカテゴリのみ

#### REQ-BT-011: 支出記録一覧取得
**Priority**: P0 (必須)
**EARS Pattern**: Event-driven

```
WHEN a user requests their expense records,
THE system SHALL return expenses filtered by date range and/or category,
AND sort by date in descending order by default.
```

#### REQ-BT-012: 支出記録更新
**Priority**: P1 (重要)
**EARS Pattern**: Event-driven

```
WHEN a user requests to update an expense record,
THE system SHALL update the expense's amount, category, date, or description,
AND recalculate the affected category's spending totals.
```

#### REQ-BT-013: 支出記録削除
**Priority**: P1 (重要)
**EARS Pattern**: Event-driven

```
WHEN a user requests to delete an expense record,
THE system SHALL remove the expense record,
AND recalculate the affected category's spending totals.
```

---

### 2.3 予算分析

#### REQ-BT-020: 月次サマリー取得
**Priority**: P0 (必須)
**EARS Pattern**: Event-driven

```
WHEN a user requests a monthly budget summary,
THE system SHALL calculate and return:
  - Total budget (sum of all category limits)
  - Total spending (sum of all expenses)
  - Remaining budget (total budget - total spending)
  - Spending percentage per category.
```

#### REQ-BT-021: カテゴリ別分析
**Priority**: P1 (重要)
**EARS Pattern**: Event-driven

```
WHEN a user requests category analysis for a specific period,
THE system SHALL return:
  - Spending trend over time
  - Average daily spending
  - Comparison with previous period.
```

#### REQ-BT-022: 予算超過検出
**Priority**: P0 (必須)
**EARS Pattern**: State-driven

```
WHILE a category's spending exceeds 80% of its monthly limit,
THE system SHALL flag the category as "warning" status.

WHILE a category's spending exceeds 100% of its monthly limit,
THE system SHALL flag the category as "exceeded" status.
```

---

### 2.4 アラート通知

#### REQ-BT-030: 予算警告アラート
**Priority**: P1 (重要)
**EARS Pattern**: Event-driven

```
WHEN a category's spending first reaches 80% of its monthly limit,
THE system SHALL generate a warning alert for the user.
```

#### REQ-BT-031: 予算超過アラート
**Priority**: P1 (重要)
**EARS Pattern**: Event-driven

```
WHEN a category's spending first exceeds 100% of its monthly limit,
THE system SHALL generate an exceeded alert for the user.
```

#### REQ-BT-032: アラート確認
**Priority**: P2 (任意)
**EARS Pattern**: Event-driven

```
WHEN a user acknowledges an alert,
THE system SHALL mark the alert as read,
AND NOT generate duplicate alerts for the same threshold crossing.
```

---

## 3. 非機能要件

### 3.1 パフォーマンス

#### REQ-BT-NFR-001: レスポンスタイム
**Priority**: P1 (重要)
**EARS Pattern**: Ubiquitous

```
THE system SHALL respond to API requests within 200ms for 95% of requests.
```

#### REQ-BT-NFR-002: データ容量
**Priority**: P1 (重要)
**EARS Pattern**: Ubiquitous

```
THE system SHALL support up to 10,000 expense records per user.
```

### 3.2 セキュリティ

#### REQ-BT-NFR-010: データ分離
**Priority**: P0 (必須)
**EARS Pattern**: Ubiquitous

```
THE system SHALL ensure users can only access their own budget data.
```

#### REQ-BT-NFR-011: 入力検証
**Priority**: P0 (必須)
**EARS Pattern**: Ubiquitous

```
THE system SHALL validate all user inputs to prevent injection attacks.
```

### 3.3 信頼性

#### REQ-BT-NFR-020: データ整合性
**Priority**: P0 (必須)
**EARS Pattern**: Ubiquitous

```
THE system SHALL maintain consistency between expense records and category totals.
```

---

## 4. ユースケース

### UC-001: 月間予算を設定する
**Actor**: ユーザー
**Precondition**: ユーザーがログイン済み
**Main Flow**:
1. ユーザーがカテゴリ作成を選択
2. カテゴリ名と月間上限を入力
3. システムがカテゴリを作成
4. 確認メッセージを表示

### UC-002: 支出を記録する
**Actor**: ユーザー
**Precondition**: 1つ以上のカテゴリが存在
**Main Flow**:
1. ユーザーが支出記録を選択
2. 金額、カテゴリ、日付、説明を入力
3. システムが支出を記録
4. カテゴリの残予算を表示

### UC-003: 予算状況を確認する
**Actor**: ユーザー
**Precondition**: 1つ以上のカテゴリと支出が存在
**Main Flow**:
1. ユーザーがダッシュボードを表示
2. システムが月次サマリーを表示
3. カテゴリ別の予算消化率を表示

---

## 5. 用語集

| 用語 | 定義 |
|------|------|
| Budget Category | 予算を管理する単位（食費、交通費等） |
| Monthly Limit | カテゴリごとの月間予算上限 |
| Expense | 個別の支出記録 |
| Spending | 特定期間内の支出合計 |
| Alert | 予算状況に関する通知 |

---

## 6. トレーサビリティ準備

| 要件ID | 設計ID | テストID |
|--------|--------|----------|
| REQ-BT-001 | TBD | TBD |
| REQ-BT-002 | TBD | TBD |
| REQ-BT-010 | TBD | TBD |
| REQ-BT-020 | TBD | TBD |
| REQ-BT-022 | TBD | TBD |

---

**Document History**:
| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-04 | AI Architect | Initial draft |
