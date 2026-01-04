# Project-09 タスク分解書

## Document Information
- **Document ID**: TSK-INV-001
- **Version**: 1.0.0
- **Status**: Ready for Implementation
- **Created**: 2026-01-04
- **Design Reference**: DES-INV-001
- **Requirements Reference**: REQ-INV-001

---

## タスク概要

| カテゴリ | タスク数 | 見積時間 |
|---------|---------|---------|
| Domain Layer | 6 | 4h |
| Repository Layer | 5 | 3h |
| Service Layer | 6 | 6h |
| CLI Layer | 8 | 4h |
| Testing | 5 | 4h |
| **Total** | **30** | **21h** |

---

## Phase 1: Domain Layer (Foundation)

### TSK-INV-001: Value Objects実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-PM-001  
**Design**: DES-INV-001 Section 3.2.2

**Description**:
SKU, Quantity, Money の Value Object を実装する。

**Acceptance Criteria**:
- [ ] SKUはフォーマット検証（XXX-NNN）
- [ ] Quantityは非負整数のみ許可
- [ ] Moneyは金額と通貨コードを保持
- [ ] 全てimmutable（readonly）

**Files**:
- `src/domain/value-objects/sku.ts`
- `src/domain/value-objects/quantity.ts`
- `src/domain/value-objects/money.ts`
- `src/domain/value-objects/index.ts`

---

### TSK-INV-002: Product Entity実装
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: REQ-INV-PM-001, PM-003, PM-004  
**Design**: DES-INV-001 Section 3.2.1

**Description**:
Product エンティティを実装する。Input DTOパターン（BP-CODE-001）を適用。

**Acceptance Criteria**:
- [ ] CreateProductInput DTOを使用
- [ ] Date-based ID Format (PRD-YYYYMMDD-NNN)
- [ ] Status遷移のバリデーション
- [ ] 更新時のタイムスタンプ自動設定

**Files**:
- `src/domain/entities/product.ts`

---

### TSK-INV-003: Inventory Entity実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-IM-003  
**Design**: DES-INV-001 Section 3.2.1

**Description**:
Inventory エンティティを実装する。

**Acceptance Criteria**:
- [ ] 数量調整メソッド（adjustQuantity）
- [ ] 在庫確認メソッド（checkAvailability）
- [ ] 負の在庫を許可しない

**Files**:
- `src/domain/entities/inventory.ts`

---

### TSK-INV-004: Transaction Entity実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-IM-001, IM-002  
**Design**: DES-INV-001 Section 3.2.1

**Description**:
Transaction エンティティを実装する。

**Acceptance Criteria**:
- [ ] 4つの取引タイプ（inbound, outbound, adjustment, return）
- [ ] バッチ番号オプション対応
- [ ] タイムスタンプ自動設定

**Files**:
- `src/domain/entities/transaction.ts`

---

### TSK-INV-005: User Entity実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-AUTH-001, AUTH-002  
**Design**: DES-INV-001 Section 5.1

**Description**:
User エンティティを実装する。

**Acceptance Criteria**:
- [ ] 役割（Admin, Manager, Operator, Viewer）
- [ ] パスワードハッシュ化
- [ ] アカウントロック機能

**Files**:
- `src/domain/entities/user.ts`

---

### TSK-INV-006: Error Types定義
**Priority**: P0  
**Estimate**: 15min  
**Requirements**: All  
**Design**: DES-INV-001 Section 7

**Description**:
カスタムエラークラスとエラーコードを定義する。

**Acceptance Criteria**:
- [ ] InventoryError基底クラス
- [ ] エラーコード定数
- [ ] 詳細情報フィールド

**Files**:
- `src/domain/errors/inventory-error.ts`
- `src/domain/errors/error-codes.ts`

---

## Phase 2: Repository Layer

### TSK-INV-007: Repository Interface定義
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: NFR-INV-DATA-001  
**Design**: DES-INV-001 Section 5.3

**Description**:
全Repositoryのインターフェースを定義する（BP-DESIGN-002: Async Pattern）。

**Acceptance Criteria**:
- [ ] 全メソッドがPromiseを返す
- [ ] CRUD操作の標準化
- [ ] 検索条件の型定義

**Files**:
- `src/repositories/interfaces.ts`

---

### TSK-INV-008: ProductRepository実装
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: REQ-INV-PM-002  
**Design**: DES-INV-001 Section 3.2.4

**Description**:
JSONファイルベースのProductRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findById, findBySku, findByCategory, findAll
- [ ] save, delete
- [ ] 部分一致検索

**Files**:
- `src/repositories/product-repository.ts`

---

### TSK-INV-009: InventoryRepository実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-IM-003  
**Design**: DES-INV-001 Section 3.2.4

**Description**:
JSONファイルベースのInventoryRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findByProductId
- [ ] save, adjustQuantity
- [ ] 楽観的ロック対応

**Files**:
- `src/repositories/inventory-repository.ts`

---

### TSK-INV-010: TransactionRepository実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-IM-001, IM-002  
**Design**: DES-INV-001 Section 3.2.4

**Description**:
JSONファイルベースのTransactionRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findByProductId, findByDateRange
- [ ] save
- [ ] 日付範囲クエリ

**Files**:
- `src/repositories/transaction-repository.ts`

---

### TSK-INV-011: UserRepository & AuditRepository実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-AUTH-001, NFR-INV-DATA-002  
**Design**: DES-INV-001 Section 3.2.4

**Description**:
UserRepositoryとAuditRepositoryを実装する。

**Acceptance Criteria**:
- [ ] findByUsername
- [ ] 監査ログの追記専用保存
- [ ] 7年分のログ保持

**Files**:
- `src/repositories/user-repository.ts`
- `src/repositories/audit-repository.ts`

---

## Phase 3: Service Layer

### TSK-INV-012: ProductService実装
**Priority**: P0  
**Estimate**: 1h  
**Requirements**: REQ-INV-PM-001~004  
**Design**: DES-INV-001 Section 3.2.3

**Description**:
商品管理のビジネスロジックを実装する（BP-DESIGN-003: Service Layer with DI）。

**Acceptance Criteria**:
- [ ] createProduct - 商品登録
- [ ] findById, findBySku - 検索
- [ ] search - 部分一致検索（500ms以内）
- [ ] updateProduct - 更新（SKU変更不可）
- [ ] deactivateProduct - 非アクティブ化

**Files**:
- `src/services/product-service.ts`

---

### TSK-INV-013: InventoryService実装
**Priority**: P0  
**Estimate**: 1h  
**Requirements**: REQ-INV-IM-001~004  
**Design**: DES-INV-001 Section 3.2.3

**Description**:
在庫管理のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] recordInbound - 入庫処理
- [ ] recordOutbound - 出庫処理（在庫チェック付き）
- [ ] getQuantity - 在庫照会
- [ ] adjustQuantity - 棚卸調整

**Files**:
- `src/services/inventory-service.ts`

---

### TSK-INV-014: ReorderService実装
**Priority**: P1  
**Estimate**: 1h  
**Requirements**: REQ-INV-RP-001~003  
**Design**: DES-INV-001 Section 3.2.3

**Description**:
発注点管理のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] getProductsBelowReorderPoint - 発注点以下の商品リスト
- [ ] updateReorderPoint - 発注点更新
- [ ] generateReorderSuggestions - 発注提案（過去30日分析）

**Files**:
- `src/services/reorder-service.ts`

---

### TSK-INV-015: ReportService実装
**Priority**: P1  
**Estimate**: 1h  
**Requirements**: REQ-INV-REP-001~003  
**Design**: DES-INV-001 Section 3.2.3

**Description**:
レポート生成のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] generateInventorySummary - 在庫サマリー
- [ ] generateTransactionHistory - 取引履歴
- [ ] generateReorderReport - 発注点レポート
- [ ] exportToCsv, exportToPdf - エクスポート

**Files**:
- `src/services/report-service.ts`

---

### TSK-INV-016: AuthService実装
**Priority**: P0  
**Estimate**: 1h  
**Requirements**: REQ-INV-AUTH-001~003  
**Design**: DES-INV-001 Section 3.2.3

**Description**:
認証・認可のビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] authenticate - ログイン認証
- [ ] authorize - 権限チェック
- [ ] lockAccount - アカウントロック
- [ ] セッションタイムアウト（30分）

**Files**:
- `src/services/auth-service.ts`

---

### TSK-INV-017: AuditService実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: NFR-INV-DATA-002  
**Design**: DES-INV-001 Section 3.2.3

**Description**:
監査ログのビジネスロジックを実装する。

**Acceptance Criteria**:
- [ ] log - 監査ログ記録
- [ ] findByDateRange - 履歴参照
- [ ] 不変ログ（追記のみ）

**Files**:
- `src/services/audit-service.ts`

---

## Phase 4: CLI Layer

### TSK-INV-018: CLI基盤実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: All  
**Design**: DES-INV-001 Section 2.1

**Description**:
CLI基盤（Commander.js）をセットアップする。

**Acceptance Criteria**:
- [ ] コマンドパーサー設定
- [ ] ヘルプ・バージョン表示
- [ ] グローバルオプション

**Files**:
- `src/cli/index.ts`
- `src/cli/base.ts`

---

### TSK-INV-019: product コマンド実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-PM-001~004  

**Subcommands**:
- `product add` - 商品登録
- `product list` - 商品一覧
- `product search <query>` - 検索
- `product update <id>` - 更新
- `product deactivate <id>` - 非アクティブ化

**Files**:
- `src/cli/commands/product.ts`

---

### TSK-INV-020: inventory コマンド実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-IM-001~004  

**Subcommands**:
- `inventory inbound <productId> <quantity>` - 入庫
- `inventory outbound <productId> <quantity>` - 出庫
- `inventory status <productId>` - 在庫照会
- `inventory adjust <productId> <adjustment>` - 調整

**Files**:
- `src/cli/commands/inventory.ts`

---

### TSK-INV-021: reorder コマンド実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-INV-RP-001~003  

**Subcommands**:
- `reorder alerts` - 発注点アラート一覧
- `reorder set <productId> <point>` - 発注点設定
- `reorder suggest` - 発注提案

**Files**:
- `src/cli/commands/reorder.ts`

---

### TSK-INV-022: report コマンド実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-INV-REP-001~003  

**Subcommands**:
- `report inventory` - 在庫サマリー
- `report transactions --from <date> --to <date>` - 取引履歴
- `report reorder` - 発注点レポート

**Files**:
- `src/cli/commands/report.ts`

---

### TSK-INV-023: auth コマンド実装
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: REQ-INV-AUTH-001~003  

**Subcommands**:
- `auth login` - ログイン
- `auth logout` - ログアウト
- `auth whoami` - 現在ユーザー表示

**Files**:
- `src/cli/commands/auth.ts`

---

### TSK-INV-024: user コマンド実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-INV-AUTH-002  

**Subcommands**:
- `user add` - ユーザー追加（Admin only）
- `user list` - ユーザー一覧
- `user role <userId> <role>` - 役割変更
- `user unlock <userId>` - アカウントロック解除

**Files**:
- `src/cli/commands/user.ts`

---

### TSK-INV-025: 出力フォーマッター実装
**Priority**: P1  
**Estimate**: 30min  
**Requirements**: REQ-INV-REP-001~003  

**Description**:
テーブル表示、JSON出力、CSV出力のフォーマッターを実装する。

**Files**:
- `src/cli/formatters/table.ts`
- `src/cli/formatters/json.ts`
- `src/cli/formatters/csv.ts`

---

## Phase 5: Testing

### TSK-INV-026: Value Object テスト
**Priority**: P0  
**Estimate**: 30min  
**Requirements**: All BP-TEST-*  

**Test Cases**:
- SKU: 有効/無効フォーマット
- Quantity: 正/負/ゼロ
- Money: 金額バリデーション

**Files**:
- `tests/unit/domain/value-objects.test.ts`

---

### TSK-INV-027: Entity テスト
**Priority**: P0  
**Estimate**: 45min  
**Requirements**: BP-TEST-001, BP-TEST-002  

**Test Cases**:
- Product: 作成、更新、ステータス遷移
- Inventory: 数量調整、負在庫防止
- Transaction: 各タイプの検証

**Files**:
- `tests/unit/domain/entities.test.ts`

---

### TSK-INV-028: Service テスト
**Priority**: P0  
**Estimate**: 1h  
**Requirements**: BP-TEST-001, BP-TEST-002  

**Test Cases**:
- ProductService: CRUD操作、検索
- InventoryService: 入出庫、在庫チェック
- AuthService: 認証、認可、ロック

**Files**:
- `tests/unit/services/*.test.ts`

---

### TSK-INV-029: 統合テスト
**Priority**: P1  
**Estimate**: 1h  

**Test Cases**:
- 入庫→在庫確認→出庫フロー
- 発注点アラートフロー
- レポート生成フロー

**Files**:
- `tests/integration/*.test.ts`

---

### TSK-INV-030: E2Eテスト
**Priority**: P2  
**Estimate**: 45min  

**Test Cases**:
- CLIコマンドの実行
- 完全なワークフロー

**Files**:
- `tests/e2e/*.test.ts`

---

## 依存関係グラフ

```
TSK-001 (Value Objects)
    ↓
TSK-002~005 (Entities) ← TSK-006 (Errors)
    ↓
TSK-007 (Repository Interfaces)
    ↓
TSK-008~011 (Repositories)
    ↓
TSK-012~017 (Services)
    ↓
TSK-018~025 (CLI)
    ↓
TSK-026~030 (Tests)
```

---

## サマリー

| 優先度 | タスク数 | 見積時間 |
|--------|---------|---------|
| P0 | 20 | 14h |
| P1 | 8 | 5.5h |
| P2 | 2 | 1.5h |
| **Total** | **30** | **21h** |
