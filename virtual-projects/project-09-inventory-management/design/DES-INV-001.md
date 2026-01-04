# 在庫管理システム設計書

## Document Information
- **Document ID**: DES-INV-001
- **Version**: 1.0.0
- **Status**: Draft
- **Created**: 2026-01-04
- **Requirements Reference**: REQ-INV-001

---

## 1. C4 Model - Level 1: System Context

### 1.1 System Context Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                      External Actors                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────┐     │
│  │  Warehouse   │     │   Manager    │     │    Admin     │     │
│  │  Operator    │     │              │     │              │     │
│  └──────┬───────┘     └──────┬───────┘     └──────┬───────┘     │
│         │                    │                    │              │
│         │    入出庫処理      │   レポート閲覧    │   設定管理   │
│         │                    │                    │              │
│         └────────────────────┼────────────────────┘              │
│                              │                                   │
│                              ▼                                   │
│              ┌───────────────────────────────┐                   │
│              │   Inventory Management        │                   │
│              │        System                 │                   │
│              │                               │                   │
│              │  - 商品管理                   │                   │
│              │  - 在庫管理                   │                   │
│              │  - 発注点管理                 │                   │
│              │  - レポート生成               │                   │
│              └───────────────────────────────┘                   │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Actor Definitions

| Actor | Role | Primary Use Cases |
|-------|------|-------------------|
| Warehouse Operator | 倉庫作業員 | 入庫処理、出庫処理、在庫照会 |
| Manager | 管理者 | レポート閲覧、発注点設定、在庫分析 |
| Admin | システム管理者 | ユーザー管理、システム設定、監査ログ閲覧 |

---

## 2. C4 Model - Level 2: Container Diagram

### 2.1 Container Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                   Inventory Management System                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    CLI Application                        │    │
│  │                    [TypeScript/Node.js]                   │    │
│  │                                                           │    │
│  │  Entry point for all inventory operations                 │    │
│  └─────────────────────────────┬─────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    Core Library                          │    │
│  │                    [TypeScript]                          │    │
│  │                                                           │    │
│  │  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌──────────┐ │    │
│  │  │  Product  │ │ Inventory │ │  Reorder  │ │  Report  │ │    │
│  │  │  Module   │ │  Module   │ │  Module   │ │  Module  │ │    │
│  │  └───────────┘ └───────────┘ └───────────┘ └──────────┘ │    │
│  │  ┌───────────┐ ┌───────────┐                           │    │
│  │  │   Auth    │ │   Audit   │                           │    │
│  │  │  Module   │ │  Module   │                           │    │
│  │  └───────────┘ └───────────┘                           │    │
│  └─────────────────────────────┬─────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    Data Store                            │    │
│  │                    [JSON Files / SQLite]                 │    │
│  │                                                           │    │
│  │  products.json | inventory.json | transactions.json      │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 Container Specifications

| Container | Technology | Responsibility | Requirements Trace |
|-----------|------------|----------------|-------------------|
| CLI Application | TypeScript/Node.js | ユーザーインターフェース、コマンド処理 | REQ-INV-PM-*, REQ-INV-IM-* |
| Core Library | TypeScript | ビジネスロジック、バリデーション | All REQ-INV-* |
| Data Store | JSON/SQLite | データ永続化、クエリ処理 | NFR-INV-DATA-* |

---

## 3. C4 Model - Level 3: Component Diagram

### 3.1 Core Library Components

```
┌─────────────────────────────────────────────────────────────────┐
│                        Core Library                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    Domain Layer                          │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │    Product    │  │   Inventory   │  │ Transaction │  │    │
│  │  │    Entity     │  │    Entity     │  │   Entity    │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │      SKU      │  │   Quantity    │  │    Money    │  │    │
│  │  │ Value Object  │  │ Value Object  │  │Value Object │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                   Service Layer                          │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │   Product     │  │  Inventory    │  │  Reorder    │  │    │
│  │  │   Service     │  │   Service     │  │  Service    │  │    │
│  │  │               │  │               │  │             │  │    │
│  │  │ REQ-INV-PM-*  │  │ REQ-INV-IM-*  │  │REQ-INV-RP-* │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  │  ┌───────────────┐  ┌───────────────┐                   │    │
│  │  │    Report     │  │     Auth      │                   │    │
│  │  │   Service     │  │   Service     │                   │    │
│  │  │               │  │               │                   │    │
│  │  │REQ-INV-REP-*  │  │REQ-INV-AUTH-* │                   │    │
│  │  └───────────────┘  └───────────────┘                   │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                │                                  │
│                                ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                 Repository Layer                         │    │
│  │  ┌───────────────┐  ┌───────────────┐  ┌─────────────┐  │    │
│  │  │   Product     │  │  Inventory    │  │ Transaction │  │    │
│  │  │  Repository   │  │  Repository   │  │ Repository  │  │    │
│  │  └───────────────┘  └───────────────┘  └─────────────┘  │    │
│  │  ┌───────────────┐  ┌───────────────┐                   │    │
│  │  │     User      │  │    Audit      │                   │    │
│  │  │  Repository   │  │  Repository   │                   │    │
│  │  └───────────────┘  └───────────────┘                   │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 Component Specifications

#### 3.2.1 Domain Entities

| Entity | Attributes | Methods | Requirements |
|--------|------------|---------|--------------|
| Product | id, sku, name, description, category, unitPrice, reorderPoint, status, createdAt, updatedAt | validate(), activate(), deactivate() | REQ-INV-PM-001~004 |
| Inventory | id, productId, quantity, location, lastUpdated | adjustQuantity(), checkAvailability() | REQ-INV-IM-001~004 |
| Transaction | id, productId, type, quantity, timestamp, userId, notes, batchNumber | validate() | REQ-INV-IM-001~002 |

#### 3.2.2 Value Objects

| Value Object | Structure | Validation Rules |
|-------------|-----------|------------------|
| SKU | `{ prefix: string, code: string }` | Format: `XXX-NNN`, unique |
| Quantity | `{ value: number }` | Non-negative integer |
| Money | `{ amount: number, currency: string }` | amount >= 0, currency: 3-letter code |

#### 3.2.3 Services

| Service | Responsibilities | Dependencies | Requirements |
|---------|-----------------|--------------|--------------|
| ProductService | 商品CRUD、検索、バリデーション | ProductRepository | REQ-INV-PM-* |
| InventoryService | 入出庫処理、在庫照会、数量調整 | InventoryRepository, TransactionRepository | REQ-INV-IM-* |
| ReorderService | 発注点監視、アラート生成、発注提案 | ProductRepository, InventoryRepository | REQ-INV-RP-* |
| ReportService | レポート生成、エクスポート | All Repositories | REQ-INV-REP-* |
| AuthService | 認証、認可、セッション管理 | UserRepository | REQ-INV-AUTH-* |
| AuditService | 監査ログ記録、履歴参照 | AuditRepository | NFR-INV-DATA-002 |

#### 3.2.4 Repositories

| Repository | Interface Methods | Storage |
|------------|-------------------|---------|
| ProductRepository | findById, findBySku, findByCategory, save, delete | products.json |
| InventoryRepository | findByProductId, save, adjustQuantity | inventory.json |
| TransactionRepository | findByProductId, findByDateRange, save | transactions.json |
| UserRepository | findByUsername, save, updatePassword | users.json |
| AuditRepository | log, findByDateRange | audit.json |

---

## 4. Design Patterns Applied

### 4.1 Pattern Usage

| Pattern | Applied To | Justification | Constitution Article |
|---------|-----------|---------------|---------------------|
| Repository | All data access | データアクセスの抽象化、テスト容易性 | VII |
| Service Layer | Business logic | ドメインロジックの分離 | VII |
| Value Object | SKU, Quantity, Money | 不変性と型安全性の確保 | VII |
| Factory | Entity creation | 複雑な生成ロジックのカプセル化 | VII |
| Strategy | Report generation | 異なるフォーマット（CSV/PDF）対応 | VII |

### 4.2 Status Transition Map (BP-DESIGN-001)

```typescript
// Product Status Transitions
const productStatusTransitions: Record<ProductStatus, ProductStatus[]> = {
  active: ['inactive', 'discontinued'],
  inactive: ['active', 'discontinued'],
  discontinued: [], // Terminal state
};

// Transaction Types
type TransactionType = 'inbound' | 'outbound' | 'adjustment' | 'return';
```

---

## 5. Interface Definitions

### 5.1 Entity Interfaces (BP-CODE-001: Entity Input DTO)

```typescript
// Product Entity
interface CreateProductInput {
  sku: SKU;
  name: string;
  description?: string;
  category: string;
  unitPrice: Money;
  reorderPoint: number;
}

interface Product {
  id: string;
  sku: SKU;
  name: string;
  description: string;
  category: string;
  unitPrice: Money;
  reorderPoint: number;
  status: ProductStatus;
  createdAt: Date;
  updatedAt: Date;
}

// Inventory Entity
interface Inventory {
  id: string;
  productId: string;
  quantity: Quantity;
  location: string;
  lastUpdated: Date;
}

// Transaction Entity
interface CreateTransactionInput {
  productId: string;
  type: TransactionType;
  quantity: number;
  notes?: string;
  batchNumber?: string;
}

interface Transaction {
  id: string;
  productId: string;
  type: TransactionType;
  quantity: number;
  timestamp: Date;
  userId: string;
  notes: string;
  batchNumber?: string;
}
```

### 5.2 Service Interfaces

```typescript
interface IProductService {
  createProduct(input: CreateProductInput): Promise<Product>;
  findById(id: string): Promise<Product | null>;
  findBySku(sku: string): Promise<Product | null>;
  search(query: string): Promise<Product[]>;
  updateProduct(id: string, updates: Partial<CreateProductInput>): Promise<Product>;
  deactivateProduct(id: string): Promise<void>;
}

interface IInventoryService {
  recordInbound(input: CreateTransactionInput): Promise<Transaction>;
  recordOutbound(input: CreateTransactionInput): Promise<Transaction>;
  getQuantity(productId: string): Promise<number>;
  adjustQuantity(productId: string, adjustment: number, reason: string): Promise<Transaction>;
}

interface IReorderService {
  getProductsBelowReorderPoint(): Promise<ReorderAlert[]>;
  updateReorderPoint(productId: string, newPoint: number): Promise<void>;
  generateReorderSuggestions(): Promise<ReorderSuggestion[]>;
}
```

### 5.3 Repository Interfaces (BP-DESIGN-002: Repository Async Pattern)

```typescript
interface IProductRepository {
  findById(id: string): Promise<Product | null>;
  findBySku(sku: string): Promise<Product | null>;
  findByCategory(category: string): Promise<Product[]>;
  findAll(): Promise<Product[]>;
  save(product: Product): Promise<Product>;
  delete(id: string): Promise<void>;
}

interface IInventoryRepository {
  findByProductId(productId: string): Promise<Inventory | null>;
  save(inventory: Inventory): Promise<Inventory>;
  adjustQuantity(productId: string, delta: number): Promise<Inventory>;
}

interface ITransactionRepository {
  findByProductId(productId: string): Promise<Transaction[]>;
  findByDateRange(start: Date, end: Date): Promise<Transaction[]>;
  save(transaction: Transaction): Promise<Transaction>;
}
```

---

## 6. Data Model

### 6.1 JSON Schema

```json
{
  "products": {
    "type": "array",
    "items": {
      "type": "object",
      "properties": {
        "id": { "type": "string", "pattern": "^PRD-\\d{8}-\\d{3}$" },
        "sku": { "type": "string", "pattern": "^[A-Z]{3}-\\d{3}$" },
        "name": { "type": "string", "minLength": 1, "maxLength": 100 },
        "status": { "enum": ["active", "inactive", "discontinued"] }
      },
      "required": ["id", "sku", "name", "status"]
    }
  }
}
```

### 6.2 ID Format (BP-CODE-002: Date-based ID Format)

| Entity | Format | Example |
|--------|--------|---------|
| Product | PRD-YYYYMMDD-NNN | PRD-20260104-001 |
| Transaction | TXN-YYYYMMDD-NNN | TXN-20260104-001 |
| User | USR-YYYYMMDD-NNN | USR-20260104-001 |

---

## 7. Error Handling

### 7.1 Error Types

```typescript
class InventoryError extends Error {
  constructor(
    public code: string,
    message: string,
    public details?: Record<string, unknown>
  ) {
    super(message);
    this.name = 'InventoryError';
  }
}

// Error Codes
const ErrorCodes = {
  PRODUCT_NOT_FOUND: 'INV-001',
  SKU_DUPLICATE: 'INV-002',
  INSUFFICIENT_STOCK: 'INV-003',
  INVALID_QUANTITY: 'INV-004',
  PRODUCT_HAS_TRANSACTIONS: 'INV-005',
  UNAUTHORIZED: 'AUTH-001',
  ACCOUNT_LOCKED: 'AUTH-002',
} as const;
```

---

## 8. Traceability Matrix

| Design Component | Requirements | Priority |
|-----------------|--------------|----------|
| ProductService | REQ-INV-PM-001, PM-002, PM-003, PM-004 | P0, P1 |
| InventoryService | REQ-INV-IM-001, IM-002, IM-003, IM-004 | P0 |
| ReorderService | REQ-INV-RP-001, RP-002, RP-003 | P1, P2 |
| ReportService | REQ-INV-REP-001, REP-002, REP-003 | P1 |
| AuthService | REQ-INV-AUTH-001, AUTH-002, AUTH-003 | P0 |
| Product Entity | REQ-INV-PM-001 | P0 |
| Inventory Entity | REQ-INV-IM-003 | P0 |
| Transaction Entity | REQ-INV-IM-001, IM-002 | P0 |

---

## 9. ADR (Architecture Decision Records)

### ADR-INV-001: JSON File Storage

**Context**: データ永続化方式の選択

**Decision**: 初期バージョンではJSONファイルを使用

**Rationale**:
- シンプルな実装で高速な開発
- 外部データベース依存なし
- 将来的にSQLiteやPostgreSQLへの移行が容易（Repository Pattern採用）

**Consequences**:
- (+) セットアップ不要
- (-) 大規模データには不向き
- (-) 同時アクセス制御が限定的

### ADR-INV-002: TypeScript with Strict Mode

**Context**: 開発言語の選択

**Decision**: TypeScript (strict mode) を使用

**Rationale**:
- 型安全性による実行時エラー削減
- IDEサポートによる開発効率向上
- MUSUBIXエコシステムとの統一

**Consequences**:
- (+) コンパイル時のエラー検出
- (+) ドキュメントとしての型定義
- (-) 初期学習コスト
