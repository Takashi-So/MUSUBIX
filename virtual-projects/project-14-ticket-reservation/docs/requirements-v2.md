# Project 14: Ticket Reservation System - Requirements Document v2.0

**プロジェクトID**: project-14-ticket-reservation  
**作成日**: 2026-01-04  
**更新日**: 2026-01-04  
**フェーズ**: Phase 1 - 要件定義（完了）  
**MUSUBIX Version**: 1.1.9

---

## 変更履歴

| バージョン | 日付 | 変更内容 |
|-----------|------|---------|
| 1.0 | 2026-01-04 | 初版作成 |
| 2.0 | 2026-01-04 | レビュー指摘対応（ISSUE-001,003,004） |

---

## 1. プロジェクト概要

### 1.1 目的
イベントやコンサートなどのチケット予約・購入を管理するシステムを提供する。
ユーザーはイベントを検索し、座席を選択して予約・購入できる。

### 1.2 スコープ
- イベント管理（登録・一覧・検索・座席生成）
- 座席管理（座席図・空席確認・価格設定）
- 予約管理（仮予約・確定・キャンセル）
- 基本的なCLI操作

### 1.3 対象外（Out of Scope）
- 決済処理（外部システム連携を想定）
- ユーザー認証（IDを直接指定）
- GUI/Web UI

---

## 2. 機能要件 (EARS Format)

### 2.1 イベント管理

**REQ-TR-001** (P0 - Ubiquitous) [Updated]
THE system SHALL create events with the following required fields: name (1-100 characters), venue (1-200 characters), dateTime, basePrice (100-1,000,000 JPY), and seat configuration (rows and seats per row).

**REQ-TR-002** (P0 - Event-driven)
WHEN a user searches for events, THE system SHALL return events matching the search criteria (name, venue, or date range).

**REQ-TR-003** (P1 - State-driven)
WHILE an event has status "active", THE system SHALL allow reservations for that event.

**REQ-TR-004** (P1 - Event-driven)
WHEN an event date passes, THE system SHALL automatically change the event status to "completed".

**REQ-TR-005** (P0 - Event-driven) [New]
WHEN an event is created, THE system SHALL automatically generate seats based on the seat configuration (rows × seats per row, up to 10,000 total seats).

### 2.2 座席管理

**REQ-TR-010** (P0 - Ubiquitous)
THE system SHALL manage seats with unique identifiers in format "ROW-NUM" (e.g., "A-1", "B-12").

**REQ-TR-011** (P0 - Ubiquitous)
THE system SHALL track seat status as one of: "available", "reserved", "sold", "unavailable".

**REQ-TR-012** (P0 - State-driven)
WHILE a seat has status "available", THE system SHALL allow the seat to be reserved.

**REQ-TR-013** (P1 - Unwanted)
THE system SHALL NOT allow reservation of a seat that is not in "available" status.

**REQ-TR-014** (P1 - Ubiquitous) [New]
THE system SHALL assign a price to each seat, defaulting to the event base price but allowing individual seat price overrides (100-1,000,000 JPY).

### 2.3 予約管理

**REQ-TR-020** (P0 - Event-driven)
WHEN a user creates a reservation, THE system SHALL generate a unique reservation ID in format "RSV-YYYYMMDD-NNN" and set status to "pending".

**REQ-TR-021** (P0 - Event-driven)
WHEN a reservation is created, THE system SHALL change the selected seats' status to "reserved".

**REQ-TR-022** (P0 - Optional)
IF a reservation is not confirmed within 15 minutes, THEN THE system SHALL automatically cancel the reservation and release the seats.

**REQ-TR-023** (P1 - Event-driven)
WHEN a user confirms a reservation, THE system SHALL change the reservation status to "confirmed" and seat status to "sold".

**REQ-TR-024** (P1 - Event-driven)
WHEN a user cancels a reservation with status "pending" or "confirmed", THE system SHALL change reservation status to "cancelled" and release the seats.

**REQ-TR-025** (P1 - Unwanted)
THE system SHALL NOT allow cancellation of reservations within 24 hours of the event start time.

**REQ-TR-026** (P0 - Unwanted) [New]
THE system SHALL NOT allow a single reservation to include more than 10 seats.

### 2.4 同時予約制御

**REQ-TR-030** (P0 - Event-driven)
WHEN multiple users attempt to reserve the same seat simultaneously, THE system SHALL allow only the first successful request and reject others.

**REQ-TR-031** (P1 - State-driven)
WHILE processing a seat reservation, THE system SHALL lock the seat to prevent concurrent modifications.

### 2.5 分析・レポート

**REQ-TR-040** (P2 - Event-driven)
WHEN a user requests event statistics, THE system SHALL return total seats, sold seats, reserved seats, and available seats count.

---

## 3. 非機能要件

### 3.1 パフォーマンス

**REQ-TR-NF-001** (P1)
THE system SHALL process seat availability check within 500ms for events with up to 10,000 seats.

### 3.2 データ整合性

**REQ-TR-NF-002** (P0)
THE system SHALL ensure seat status consistency through optimistic locking with version field.

### 3.3 永続化

**REQ-TR-NF-003** (P1)
THE system SHALL persist all data to local JSON files.

---

## 4. ドメインモデル

### 4.1 エンティティ

| エンティティ | 属性 | 説明 |
|------------|------|------|
| Event | id, name, venue, dateTime, basePrice, seatConfig, status, createdAt, updatedAt | イベント |
| Seat | id, eventId, seatCode, price, status, version | 座席 |
| Reservation | id, userId, eventId, seatIds, totalPrice, status, expiresAt, createdAt, updatedAt | 予約 |

### 4.2 値オブジェクト

| 値オブジェクト | 属性 | 説明 |
|--------------|------|------|
| SeatCode | row, number | 座席コード（例: A-1） |
| Price | amount | 価格（100-1,000,000 JPY） |
| SeatConfig | rows, seatsPerRow | 座席構成 |

### 4.3 ステータス遷移

**Event Status** (BP-DESIGN-001):
```typescript
const validEventTransitions = {
  draft: ['active'],
  active: ['completed', 'cancelled'],
  completed: [],
  cancelled: [],
};
```

**Seat Status** (BP-DESIGN-001):
```typescript
const validSeatTransitions = {
  available: ['reserved', 'unavailable'],
  reserved: ['available', 'sold'],
  sold: ['available'], // refund
  unavailable: ['available'],
};
```

**Reservation Status** (BP-DESIGN-001):
```typescript
const validReservationTransitions = {
  pending: ['confirmed', 'cancelled', 'expired'],
  confirmed: ['cancelled'],
  cancelled: [],
  expired: [],
};
```

---

## 5. 優先度定義

| 優先度 | 意味 | 要件数 |
|-------|------|-------|
| P0 | 必須（MVP） | 11 |
| P1 | 重要 | 8 |
| P2 | 任意 | 1 |
| **合計** | | **20** |

---

## 6. 用語集

| 用語 | 定義 |
|-----|------|
| Event | チケット販売対象のイベント（コンサート、映画等） |
| Seat | イベント会場の個別座席 |
| Reservation | ユーザーによる座席の予約（仮予約または確定） |
| Pending | 仮予約状態（15分以内に確定が必要） |
| Confirmed | 確定予約状態（購入完了） |
| SeatConfig | 会場の座席配置（行数×行あたり席数） |

---

## 7. 憲法準拠チェック

| 条項 | 準拠状況 |
|-----|---------|
| I. Library-First | ✅ 独立ライブラリとして設計 |
| II. CLI Interface | ✅ CLI要件を明記 |
| III. Test-First | ⏳ Phase 4で実施 |
| IV. EARS Format | ✅ 全20要件がEARS形式 |
| V. Traceability | ✅ 要件IDを付与 |
| VI. Project Memory | ✅ steering/参照 |
| VII. Design Patterns | ⏳ Phase 2で文書化 |
| VIII. Decision Records | ⏳ Phase 2で記録 |
| IX. Quality Gates | ✅ レビュー完了 |

---

**Document Version**: 2.0  
**Status**: Approved  
**Next**: Phase 2 - Architecture Design
