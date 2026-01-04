# 在庫管理システム要件定義書

## Document Information
- **Document ID**: REQ-INV-001
- **Version**: 1.0.0
- **Status**: Draft
- **Created**: 2026-01-04
- **Author**: MUSUBIX SDD Workflow

## 1. プロジェクト概要

### 1.1 目的
中小企業向けの在庫管理システムを構築し、商品の入出庫管理、在庫レベル監視、発注点管理を効率化する。

### 1.2 スコープ
- 商品マスタ管理
- 入庫・出庫処理
- 在庫数量管理
- 発注点アラート
- 在庫レポート生成

### 1.3 対象外
- 会計システム連携
- ECサイト連携
- バーコードスキャナ連携

---

## 2. 機能要件 (EARS形式)

### 2.1 商品管理 (Product Management)

#### REQ-INV-PM-001: 商品登録
**Ubiquitous**
> THE system SHALL allow users to register new products with SKU, name, description, category, unit price, and reorder point.

**Acceptance Criteria**:
- SKUは一意である
- 商品名は必須（1-100文字）
- 発注点は0以上の整数

#### REQ-INV-PM-002: 商品検索
**Event-driven**
> WHEN a user enters a search query, THE system SHALL display matching products filtered by SKU, name, or category within 500ms.

**Acceptance Criteria**:
- 部分一致検索をサポート
- 検索結果は最大100件まで表示
- ページネーション対応

#### REQ-INV-PM-003: 商品更新
**Event-driven**
> WHEN a user updates product information, THE system SHALL validate the changes and persist them with an audit trail.

**Acceptance Criteria**:
- 更新履歴を記録
- SKUの変更は不可

#### REQ-INV-PM-004: 商品削除防止
**Unwanted**
> THE system SHALL NOT allow deletion of products that have associated inventory records or transaction history.

**Acceptance Criteria**:
- 関連データがある場合はエラーメッセージを表示
- 代わりに「非アクティブ」ステータスを設定可能

---

### 2.2 在庫管理 (Inventory Management)

#### REQ-INV-IM-001: 入庫処理
**Event-driven**
> WHEN a user records an inbound shipment, THE system SHALL increase the inventory quantity and create a transaction record with timestamp, quantity, and source.

**Acceptance Criteria**:
- 入庫数量は正の整数
- 仕入先情報をオプションで記録
- バッチ番号/ロット番号対応

#### REQ-INV-IM-002: 出庫処理
**Event-driven**
> WHEN a user records an outbound shipment, THE system SHALL decrease the inventory quantity and create a transaction record with timestamp, quantity, and destination.

**Acceptance Criteria**:
- 出庫数量が現在庫を超えない
- 出荷先情報をオプションで記録

#### REQ-INV-IM-003: 在庫数量照会
**Ubiquitous**
> THE system SHALL maintain accurate real-time inventory quantities for all registered products.

**Acceptance Criteria**:
- 在庫数量はトランザクション履歴と整合
- 負の在庫は許可しない

#### REQ-INV-IM-004: 在庫不足防止
**Unwanted**
> THE system SHALL NOT allow outbound transactions that would result in negative inventory quantities.

**Acceptance Criteria**:
- 出庫前に在庫チェック
- 不足時はエラーメッセージを表示

---

### 2.3 発注点管理 (Reorder Point Management)

#### REQ-INV-RP-001: 発注点アラート
**State-driven**
> WHILE the inventory quantity of a product is at or below its reorder point, THE system SHALL display a visual alert on the dashboard and include the product in the reorder list.

**Acceptance Criteria**:
- アラートは即時表示
- 発注リストはエクスポート可能

#### REQ-INV-RP-002: 発注点更新
**Event-driven**
> WHEN a user updates the reorder point for a product, THE system SHALL recalculate alerts for that product immediately.

**Acceptance Criteria**:
- 発注点は0以上の整数
- 変更履歴を記録

#### REQ-INV-RP-003: 自動発注提案
**Optional**
> IF automatic reorder suggestions are enabled, THEN THE system SHALL generate purchase order recommendations based on reorder points and historical consumption patterns.

**Acceptance Criteria**:
- 過去30日の消費量を分析
- 推奨発注量を計算

---

### 2.4 レポート機能 (Reporting)

#### REQ-INV-REP-001: 在庫サマリーレポート
**Event-driven**
> WHEN a user requests an inventory summary report, THE system SHALL generate a report showing current quantities, values, and status for all products.

**Acceptance Criteria**:
- CSV/PDF形式でエクスポート可能
- フィルタリング・ソート対応

#### REQ-INV-REP-002: 取引履歴レポート
**Event-driven**
> WHEN a user requests a transaction history report, THE system SHALL display all inventory movements within the specified date range.

**Acceptance Criteria**:
- 日付範囲指定必須
- 商品別フィルタ対応

#### REQ-INV-REP-003: 発注点レポート
**Event-driven**
> WHEN a user requests a reorder point report, THE system SHALL list all products at or below their reorder points with recommended order quantities.

**Acceptance Criteria**:
- 優先度順にソート
- 発注履歴を参照

---

### 2.5 認証・認可 (Authentication & Authorization)

#### REQ-INV-AUTH-001: ユーザー認証
**Ubiquitous**
> THE system SHALL require users to authenticate with username and password before accessing any inventory functions.

**Acceptance Criteria**:
- パスワードはハッシュ化して保存
- セッションタイムアウト30分

#### REQ-INV-AUTH-002: 役割ベースアクセス制御
**State-driven**
> WHILE a user is logged in with a specific role, THE system SHALL restrict access to functions based on the user's assigned permissions.

**Acceptance Criteria**:
- 役割: Admin, Manager, Operator, Viewer
- Admin: 全機能アクセス可
- Manager: レポート・設定変更可
- Operator: 入出庫処理可
- Viewer: 閲覧のみ

#### REQ-INV-AUTH-003: 不正アクセス防止
**Unwanted**
> THE system SHALL NOT allow access to protected resources without valid authentication credentials.

**Acceptance Criteria**:
- 無効な認証情報で3回失敗後、アカウント一時ロック
- ロック解除は管理者のみ可能

---

## 3. 非機能要件

### 3.1 パフォーマンス (NFR-INV-PERF)

#### NFR-INV-PERF-001: 応答時間
> THE system SHALL respond to user queries within 500ms for 95% of requests under normal load.

#### NFR-INV-PERF-002: 同時ユーザー
> THE system SHALL support at least 50 concurrent users without performance degradation.

### 3.2 データ整合性 (NFR-INV-DATA)

#### NFR-INV-DATA-001: トランザクション整合性
> THE system SHALL ensure ACID compliance for all inventory transactions.

#### NFR-INV-DATA-002: 監査ログ
> THE system SHALL maintain an immutable audit log of all inventory changes for at least 7 years.

### 3.3 可用性 (NFR-INV-AVAIL)

#### NFR-INV-AVAIL-001: 稼働時間
> THE system SHALL maintain 99.5% uptime during business hours (8:00-20:00 JST).

---

## 4. ドメインモデル

### 4.1 エンティティ

| エンティティ | 説明 | 主要属性 |
|-------------|------|----------|
| Product | 商品 | id, sku, name, description, category, unitPrice, reorderPoint, status |
| Inventory | 在庫 | id, productId, quantity, location, lastUpdated |
| Transaction | 取引履歴 | id, productId, type, quantity, timestamp, userId, notes |
| Category | カテゴリ | id, name, description, parentId |

### 4.2 Value Objects

| Value Object | 説明 | 構成 |
|-------------|------|------|
| SKU | 商品コード | prefix, code (e.g., "PRD-001") |
| Quantity | 数量 | value (non-negative integer) |
| Money | 金額 | amount, currency |

### 4.3 ステータス遷移

```
Product Status:
  active → inactive → active (reactivation)
  active → discontinued (終売)

Transaction Type:
  inbound (入庫)
  outbound (出庫)
  adjustment (棚卸調整)
  return (返品)
```

---

## 5. トレーサビリティ

| 要件ID | 優先度 | 設計参照 |
|--------|--------|----------|
| REQ-INV-PM-001 | P0 | DES-INV-001 |
| REQ-INV-PM-002 | P1 | DES-INV-001 |
| REQ-INV-PM-003 | P1 | DES-INV-001 |
| REQ-INV-PM-004 | P0 | DES-INV-001 |
| REQ-INV-IM-001 | P0 | DES-INV-002 |
| REQ-INV-IM-002 | P0 | DES-INV-002 |
| REQ-INV-IM-003 | P0 | DES-INV-002 |
| REQ-INV-IM-004 | P0 | DES-INV-002 |
| REQ-INV-RP-001 | P1 | DES-INV-003 |
| REQ-INV-RP-002 | P1 | DES-INV-003 |
| REQ-INV-RP-003 | P2 | DES-INV-003 |
| REQ-INV-REP-001 | P1 | DES-INV-004 |
| REQ-INV-REP-002 | P1 | DES-INV-004 |
| REQ-INV-REP-003 | P1 | DES-INV-004 |
| REQ-INV-AUTH-001 | P0 | DES-INV-005 |
| REQ-INV-AUTH-002 | P0 | DES-INV-005 |
| REQ-INV-AUTH-003 | P0 | DES-INV-005 |

---

## 6. 用語集

| 用語 | 定義 |
|-----|------|
| SKU | Stock Keeping Unit - 商品管理単位 |
| 発注点 | Reorder Point - 発注を行う在庫水準 |
| 入庫 | Inbound - 在庫の増加 |
| 出庫 | Outbound - 在庫の減少 |
| 棚卸 | Physical Count - 実地在庫確認 |

---

## Appendix A: EARS パターン使用状況

| パターン | 使用数 | 要件ID |
|---------|--------|--------|
| Ubiquitous | 3 | REQ-INV-PM-001, REQ-INV-IM-003, REQ-INV-AUTH-001 |
| Event-driven | 8 | REQ-INV-PM-002, PM-003, IM-001, IM-002, RP-002, REP-001~003 |
| State-driven | 2 | REQ-INV-RP-001, REQ-INV-AUTH-002 |
| Unwanted | 3 | REQ-INV-PM-004, REQ-INV-IM-004, REQ-INV-AUTH-003 |
| Optional | 1 | REQ-INV-RP-003 |

**Total**: 17 機能要件 + 5 非機能要件 = 22 要件
