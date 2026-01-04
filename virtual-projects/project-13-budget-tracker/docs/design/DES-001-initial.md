# Budget Tracker System - 設計書 v1.0

**Project ID**: project-13-budget-tracker
**Document ID**: DES-001
**Version**: 1.0 (Initial)
**Created**: 2026-01-04
**Status**: Draft - Pending Review

---

## 1. C4 Model - Context Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                         Context Level                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│    ┌──────────┐         ┌─────────────────────┐                 │
│    │   User   │────────▶│  Budget Tracker     │                 │
│    │ (Person) │◀────────│     System          │                 │
│    └──────────┘         └─────────────────────┘                 │
│         │                        │                               │
│         │ Uses web/CLI           │                               │
│         │ interface              │                               │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**System**: Budget Tracker System
**Purpose**: 予算管理と支出追跡を提供するシステム
**Users**: 個人ユーザー、チームメンバー

---

## 2. C4 Model - Container Diagram

```
┌────────────────────────────────────────────────────────────────────────┐
│                          Container Level                                │
├────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────┐     ┌────────────────────────────────────────────┐   │
│  │    User     │     │         Budget Tracker System               │   │
│  └──────┬──────┘     │  ┌──────────────────────────────────────┐  │   │
│         │            │  │           CLI Application             │  │   │
│         │            │  │         [Node.js / TypeScript]        │  │   │
│         │ Commands   │  └──────────────────┬───────────────────┘  │   │
│         └───────────▶│                     │                       │   │
│                      │                     ▼                       │   │
│                      │  ┌──────────────────────────────────────┐  │   │
│                      │  │         Core Library                  │  │   │
│                      │  │       [TypeScript Library]            │  │   │
│                      │  │                                       │  │   │
│                      │  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ │  │   │
│                      │  │  │ Domain  │ │  App    │ │ Infra   │ │  │   │
│                      │  │  │  Layer  │ │ Layer   │ │ Layer   │ │  │   │
│                      │  │  └─────────┘ └─────────┘ └─────────┘ │  │   │
│                      │  └──────────────────┬───────────────────┘  │   │
│                      │                     │                       │   │
│                      │                     ▼                       │   │
│                      │  ┌──────────────────────────────────────┐  │   │
│                      │  │         JSON File Storage            │  │   │
│                      │  │          [File System]               │  │   │
│                      │  └──────────────────────────────────────┘  │   │
│                      └────────────────────────────────────────────┘   │
└────────────────────────────────────────────────────────────────────────┘
```

| Container | Technology | Purpose |
|-----------|------------|---------|
| CLI Application | Node.js / TypeScript | ユーザーインターフェース |
| Core Library | TypeScript | ビジネスロジック（Library-First） |
| JSON File Storage | File System | データ永続化（v1.0） |

---

## 3. C4 Model - Component Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        Core Library Components                           │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                        Domain Layer                              │    │
│  │  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐   │    │
│  │  │   User     │ │  Category  │ │  Expense   │ │   Alert    │   │    │
│  │  │  Entity    │ │  Entity    │ │  Entity    │ │  Entity    │   │    │
│  │  └────────────┘ └────────────┘ └────────────┘ └────────────┘   │    │
│  │  ┌────────────┐ ┌────────────┐ ┌────────────┐                  │    │
│  │  │   Money    │ │DateRange   │ │BudgetStatus│                  │    │
│  │  │   (VO)     │ │   (VO)     │ │   (VO)     │                  │    │
│  │  └────────────┘ └────────────┘ └────────────┘                  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                      Application Layer                           │    │
│  │  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐   │    │
│  │  │   Auth     │ │  Category  │ │  Expense   │ │  Analysis  │   │    │
│  │  │  Service   │ │  Service   │ │  Service   │ │  Service   │   │    │
│  │  └────────────┘ └────────────┘ └────────────┘ └────────────┘   │    │
│  │  ┌────────────┐                                                 │    │
│  │  │   Alert    │                                                 │    │
│  │  │  Service   │                                                 │    │
│  │  └────────────┘                                                 │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                     Infrastructure Layer                         │    │
│  │  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐   │    │
│  │  │   User     │ │  Category  │ │  Expense   │ │   Alert    │   │    │
│  │  │Repository  │ │Repository  │ │Repository  │ │Repository  │   │    │
│  │  └────────────┘ └────────────┘ └────────────┘ └────────────┘   │    │
│  │  ┌────────────┐                                                 │    │
│  │  │   JSON     │                                                 │    │
│  │  │  Storage   │                                                 │    │
│  │  └────────────┘                                                 │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 4. 技術スタック

| Category | Technology | Rationale |
|----------|------------|-----------|
| Language | TypeScript 5.x | 型安全性、MUSUBIX標準 |
| Runtime | Node.js 20+ | LTS、ESM対応 |
| Testing | Vitest | 高速、ESM対応 |
| Storage | JSON Files | シンプル、v1.0向け |
| CLI Framework | Commander.js | 標準的なCLI構築 |

---

## 5. Domain Model

### 5.1 Entity Definitions

#### User Entity
```typescript
interface User {
  id: UserId;           // USR-XXXXXXXX
  email: Email;
  passwordHash: string;
  createdAt: Date;
  status: 'active' | 'archived';
}
```
**Traces to**: REQ-BT-040, REQ-BT-041

#### Category Entity
```typescript
interface Category {
  id: CategoryId;       // CAT-YYYYMMDD-NNN
  userId: UserId;
  name: string;
  description: string;
  monthlyLimit: Money;
  status: 'active' | 'archived';
  createdAt: Date;
  updatedAt: Date;
}
```
**Traces to**: REQ-BT-001, REQ-BT-002, REQ-BT-003, REQ-BT-004

#### Expense Entity
```typescript
interface Expense {
  id: ExpenseId;        // EXP-YYYYMMDD-NNN
  userId: UserId;
  categoryId: CategoryId;
  amount: Money;
  date: Date;
  description: string;
  status: 'active' | 'archived';
  createdAt: Date;
  updatedAt: Date;
}
```
**Traces to**: REQ-BT-010, REQ-BT-011, REQ-BT-012, REQ-BT-013

#### Alert Entity
```typescript
interface Alert {
  id: AlertId;          // ALT-YYYYMMDD-NNN
  userId: UserId;
  categoryId: CategoryId;
  type: 'warning' | 'exceeded';
  budgetPeriod: BudgetPeriod;
  status: 'unread' | 'read';
  createdAt: Date;
  readAt?: Date;
}
```
**Traces to**: REQ-BT-030, REQ-BT-031, REQ-BT-032, REQ-BT-033

### 5.2 Value Objects

#### Money Value Object
```typescript
class Money {
  private constructor(private readonly amount: number) {}
  
  static create(amount: number): Result<Money, ValidationError>;
  add(other: Money): Money;
  subtract(other: Money): Money;
  percentage(total: Money): number;
  toNumber(): number;
}
```
**Constraints**: 1 <= amount <= 999,999,999
**Traces to**: REQ-001 Section 2.1

#### BudgetPeriod Value Object
```typescript
class BudgetPeriod {
  private constructor(
    private readonly year: number,
    private readonly month: number
  ) {}
  
  static current(): BudgetPeriod;
  static fromDate(date: Date): BudgetPeriod;
  getStartDate(): Date;
  getEndDate(): Date;
  equals(other: BudgetPeriod): boolean;
}
```
**Traces to**: REQ-001 Section 2.2

#### BudgetStatus Value Object
```typescript
type BudgetStatus = 'normal' | 'warning' | 'exceeded';

function calculateBudgetStatus(spending: Money, limit: Money): BudgetStatus {
  const percentage = spending.percentage(limit);
  if (percentage >= 100) return 'exceeded';
  if (percentage >= 80) return 'warning';
  return 'normal';
}
```
**Traces to**: REQ-BT-022, REQ-BT-023

---

## 6. Service Design

### 6.1 AuthService
```typescript
interface AuthService {
  register(input: RegisterInput): Promise<Result<User, AuthError>>;
  login(input: LoginInput): Promise<Result<AccessToken, AuthError>>;
  logout(token: AccessToken): Promise<void>;
  validateToken(token: AccessToken): Promise<Result<UserId, AuthError>>;
}
```
**Traces to**: REQ-BT-040, REQ-BT-041, REQ-BT-042

### 6.2 CategoryService
```typescript
interface CategoryService {
  create(userId: UserId, input: CreateCategoryInput): Promise<Result<Category, DomainError>>;
  list(userId: UserId): Promise<CategoryWithSpending[]>;
  update(userId: UserId, id: CategoryId, input: UpdateCategoryInput): Promise<Result<Category, DomainError>>;
  archive(userId: UserId, id: CategoryId): Promise<Result<void, DomainError>>;
}
```
**Traces to**: REQ-BT-001, REQ-BT-002, REQ-BT-003, REQ-BT-004

### 6.3 ExpenseService
```typescript
interface ExpenseService {
  record(userId: UserId, input: RecordExpenseInput): Promise<Result<Expense, DomainError>>;
  list(userId: UserId, filter: ExpenseFilter): Promise<Expense[]>;
  update(userId: UserId, id: ExpenseId, input: UpdateExpenseInput): Promise<Result<Expense, DomainError>>;
  archive(userId: UserId, id: ExpenseId): Promise<Result<void, DomainError>>;
}
```
**Traces to**: REQ-BT-010, REQ-BT-011, REQ-BT-012, REQ-BT-013

### 6.4 AnalysisService
```typescript
interface AnalysisService {
  getMonthlySummary(userId: UserId, period: BudgetPeriod): Promise<MonthlySummary>;
  getCategoryAnalysis(userId: UserId, categoryId: CategoryId, period: BudgetPeriod): Promise<CategoryAnalysis>;
}
```
**Traces to**: REQ-BT-020, REQ-BT-021

### 6.5 AlertService
```typescript
interface AlertService {
  checkAndGenerateAlerts(userId: UserId, categoryId: CategoryId): Promise<Alert[]>;
  getUnreadAlerts(userId: UserId): Promise<Alert[]>;
  acknowledge(userId: UserId, alertId: AlertId): Promise<Result<void, DomainError>>;
}
```
**Traces to**: REQ-BT-030, REQ-BT-031, REQ-BT-032, REQ-BT-033

---

## 7. Repository Design

### 7.1 Repository Interfaces (Ports)
```typescript
interface UserRepository {
  save(user: User): Promise<void>;
  findById(id: UserId): Promise<User | null>;
  findByEmail(email: Email): Promise<User | null>;
}

interface CategoryRepository {
  save(category: Category): Promise<void>;
  findById(id: CategoryId): Promise<Category | null>;
  findByUserId(userId: UserId): Promise<Category[]>;
  findActiveByUserId(userId: UserId): Promise<Category[]>;
}

interface ExpenseRepository {
  save(expense: Expense): Promise<void>;
  findById(id: ExpenseId): Promise<Expense | null>;
  findByFilter(userId: UserId, filter: ExpenseFilter): Promise<Expense[]>;
  sumByCategory(categoryId: CategoryId, period: BudgetPeriod): Promise<Money>;
}

interface AlertRepository {
  save(alert: Alert): Promise<void>;
  findByUserAndPeriod(userId: UserId, period: BudgetPeriod): Promise<Alert[]>;
  findUnreadByUser(userId: UserId): Promise<Alert[]>;
  existsForCategoryAndType(categoryId: CategoryId, type: AlertType, period: BudgetPeriod): Promise<boolean>;
}
```

### 7.2 JSON File Storage Implementation
```
storage/
├── users.json
├── categories.json
├── expenses.json
└── alerts.json
```

---

## 8. CLI Design

### 8.1 Command Structure
```
budget-tracker
├── auth
│   ├── register
│   ├── login
│   └── logout
├── category
│   ├── create
│   ├── list
│   ├── update
│   └── archive
├── expense
│   ├── record
│   ├── list
│   ├── update
│   └── archive
├── analysis
│   ├── summary
│   └── category
└── alert
    ├── list
    └── read
```

### 8.2 CLI Examples
```bash
# カテゴリ作成
budget-tracker category create --name "食費" --limit 50000

# 支出記録
budget-tracker expense record --category "食費" --amount 1200 --description "ランチ"

# 月次サマリー
budget-tracker analysis summary --month 2026-01

# アラート確認
budget-tracker alert list --unread
```

---

## 9. Directory Structure

```
project-13-budget-tracker/
├── docs/
│   ├── requirements/
│   └── design/
├── src/
│   ├── domain/
│   │   ├── entities/
│   │   │   ├── user.ts
│   │   │   ├── category.ts
│   │   │   ├── expense.ts
│   │   │   └── alert.ts
│   │   ├── value-objects/
│   │   │   ├── money.ts
│   │   │   ├── budget-period.ts
│   │   │   └── budget-status.ts
│   │   └── repositories/
│   │       └── interfaces.ts
│   ├── application/
│   │   ├── auth-service.ts
│   │   ├── category-service.ts
│   │   ├── expense-service.ts
│   │   ├── analysis-service.ts
│   │   └── alert-service.ts
│   ├── infrastructure/
│   │   ├── json-storage.ts
│   │   └── repositories/
│   │       ├── user-repository.ts
│   │       ├── category-repository.ts
│   │       ├── expense-repository.ts
│   │       └── alert-repository.ts
│   └── cli/
│       ├── index.ts
│       └── commands/
│           ├── auth.ts
│           ├── category.ts
│           ├── expense.ts
│           ├── analysis.ts
│           └── alert.ts
├── tests/
│   ├── domain/
│   ├── application/
│   └── integration/
├── package.json
├── tsconfig.json
└── vitest.config.ts
```

---

## 10. Design Patterns Applied

| Pattern | Application | Rationale |
|---------|-------------|-----------|
| Repository | Data access abstraction | テスタビリティ、DBの差し替え可能 |
| Service Layer | Business logic orchestration | ドメインロジックの集約 |
| Value Object | Money, BudgetPeriod, BudgetStatus | イミュータブル、自己検証 |
| Result Type | Error handling | 例外より明示的なエラー処理 |
| Factory | Entity creation | ID生成、検証の一元化 |

**Traces to**: Constitution Article VII (Design Patterns)

---

## 11. Traceability Matrix

| 要件ID | 設計コンポーネント | 責務 |
|--------|-------------------|------|
| REQ-BT-040 | AuthService.register | ユーザー登録 |
| REQ-BT-041 | AuthService.login | ログイン処理 |
| REQ-BT-001 | CategoryService.create | カテゴリ作成 |
| REQ-BT-002 | CategoryService.list | カテゴリ一覧 |
| REQ-BT-010 | ExpenseService.record | 支出記録 |
| REQ-BT-020 | AnalysisService.getMonthlySummary | 月次サマリー |
| REQ-BT-022 | BudgetStatus.calculate | 警告状態判定 |
| REQ-BT-030 | AlertService.checkAndGenerateAlerts | アラート生成 |

---

**Document History**:
| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-04 | AI Architect | Initial design |
