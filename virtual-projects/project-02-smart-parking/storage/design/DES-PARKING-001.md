# 設計書: Smart Parking Management System
# バージョン: 1.0.0
# 作成日: 2026-01-04
# ドメイン: parking
# 関連要件: REQ-PARKING-001

## 1. C4モデル

### Level 1: System Context

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           System Context                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│    ┌──────────┐         ┌─────────────────────────┐       ┌──────────┐  │
│    │ ドライバー│◄───────►│   Smart Parking         │◄─────►│  管理者  │  │
│    │  (User)  │入出庫/予約│  Management System     │ 設定  │ (Admin)  │  │
│    └──────────┘         └───────────┬─────────────┘       └──────────┘  │
│                                      │                                   │
│    外部システム:                     │                                   │
│    ┌──────────┐    ┌──────────┐  ┌──▼───────┐  ┌──────────┐            │
│    │ IoT      │    │ Payment  │  │ License  │  │ Signage  │            │
│    │ Sensors  │    │ Gateway  │  │ Plate    │  │ Display  │            │
│    │ (車両検知)│    │(決済処理)│  │ Reader   │  │(案内表示)│            │
│    └──────────┘    └──────────┘  └──────────┘  └──────────┘            │
└─────────────────────────────────────────────────────────────────────────┘
```

### Level 2: Container

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Container Diagram                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────┐      ┌────────────────┐      ┌────────────────┐     │
│  │  Driver App    │      │ Admin Portal   │      │ Kiosk Terminal │     │
│  │  (Mobile)      │      │ (React)        │      │ (Embedded)     │     │
│  └───────┬────────┘      └───────┬────────┘      └───────┬────────┘     │
│          │                       │                       │              │
│          └───────────────────────┼───────────────────────┘              │
│                                  │                                       │
│                          ┌───────▼───────┐                              │
│                          │  API Gateway  │                              │
│                          │   (Express)   │                              │
│                          └───────┬───────┘                              │
│                                  │                                       │
│    ┌─────────────────────────────┼─────────────────────────────┐        │
│    │                             │                             │        │
│    ▼                             ▼                             ▼        │
│  ┌──────────────┐      ┌──────────────┐      ┌──────────────┐          │
│  │ Space        │      │ Entry/Exit   │      │ Payment      │          │
│  │ Service      │      │ Service      │      │ Service      │          │
│  └──────┬───────┘      └──────┬───────┘      └──────┬───────┘          │
│         │                     │                     │                   │
│    ┌────▼────┐           ┌────▼────┐           ┌────▼────┐             │
│    │Space DB │           │Entry DB │           │Payment  │             │
│    │(Postgres)│          │         │           │   DB    │             │
│    └─────────┘           └─────────┘           └─────────┘             │
│                                                                          │
│  ┌──────────────┐      ┌──────────────┐      ┌──────────────┐          │
│  │ Fee          │      │ Reservation  │      │ IoT          │          │
│  │ Service      │      │ Service      │      │ Gateway      │          │
│  └──────────────┘      └──────────────┘      └──────────────┘          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Level 3: Component

#### 3.1 Space Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                      Space Service                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────┐    ┌─────────────────┐                     │
│  │ SpaceController │───►│ SpaceService    │                     │
│  │                 │    │                 │                     │
│  │ - register()    │    │ - create()      │                     │
│  │ - updateState() │    │ - updateState() │                     │
│  │ - getStats()    │    │ - findAvailable()│                    │
│  └─────────────────┘    └────────┬────────┘                     │
│                                  │                               │
│                    ┌─────────────┴─────────────┐                │
│                    │                           │                │
│           ┌────────▼────────┐        ┌─────────▼───────┐        │
│           │ SpaceRepository │        │ StatsAggregator │        │
│           │                 │        │                 │        │
│           │ - save()        │        │ - byType()      │        │
│           │ - findByState() │        │ - byFloor()     │        │
│           │ - updateState() │        │ - total()       │        │
│           └─────────────────┘        └─────────────────┘        │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.2 Entry/Exit Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                   Entry/Exit Service                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ EntryExitController │───►│ EntryExitService    │             │
│  │                     │    │                     │             │
│  │ - processEntry()    │    │ - recordEntry()     │             │
│  │ - processExit()     │    │ - recordExit()      │             │
│  │ - getRecord()       │    │ - findByPlate()     │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ EntryRepository │ │ PlateValidator  │ │ IdGenerator│ │
│           │                 │ │                 │ │           │ │
│           │ - save()        │ │ - validate()    │ │ - generate│ │
│           │ - findByPlate() │ │ - normalize()   │ │           │ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.3 Fee Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                      Fee Service                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ FeeController       │───►│ FeeService          │             │
│  │                     │    │                     │             │
│  │ - calculate()       │    │ - calculateFee()    │             │
│  │ - applyDiscount()   │    │ - applyDiscount()   │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ FeeCalculator   │ │ DiscountManager │ │ FeeTable  │ │
│           │                 │ │                 │ │           │ │
│           │ - calculate()   │ │ - validate()    │ │ - getRate│ │
│           │ - applyMax()    │ │ - apply()       │ │ - getMax()│ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.4 Payment Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                   Payment Service                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ PaymentController   │───►│ PaymentService      │             │
│  │                     │    │                     │             │
│  │ - processCash()     │    │ - payCash()         │             │
│  │ - processCard()     │    │ - payCard()         │             │
│  │ - prePay()          │    │ - prePay()          │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ PaymentRepo     │ │ PaymentGateway  │ │ StatusWF  │ │
│           │                 │ │                 │ │           │ │
│           │ - save()        │ │ - authorize()   │ │ - transit│ │
│           │ - findByEntry() │ │ - capture()     │ │           │ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. 設計パターン

| パターン | 適用箇所 | 理由 |
|----------|----------|------|
| **Repository** | 全Serviceのデータアクセス | データ永続化の抽象化 |
| **Service** | ビジネスロジック層 | ドメインロジックの集約 |
| **Factory** | IdGenerator | 一貫したID生成 |
| **Strategy** | PaymentGateway | 決済方式の切り替え |
| **State** | PaymentStatusWorkflow | 精算ステータス遷移 |
| **Observer** | IoTGateway | センサーイベント処理 |

---

## 3. トレーサビリティ

| 要件ID | 設計コンポーネント |
|--------|-------------------|
| REQ-SPACE-001 | SpaceService.create(), SpaceRepository.save() |
| REQ-SPACE-002 | SpaceService.updateState(), IoTGateway |
| REQ-SPACE-003 | StatsAggregator.byType(), StatsAggregator.byFloor() |
| REQ-ENTRY-001 | EntryExitService.recordEntry(), PlateValidator |
| REQ-ENTRY-002 | EntryExitService.recordExit(), FeeService |
| REQ-ENTRY-003 | EntryExitService.findByPlate() |
| REQ-FEE-001 | FeeCalculator.calculate(), FeeTable |
| REQ-FEE-002 | DiscountManager.validate(), DiscountManager.apply() |
| REQ-FEE-003 | FeeCalculator.applyMax() |
| REQ-PAY-001 | PaymentService.payCash() |
| REQ-PAY-002 | PaymentService.payCard(), PaymentGateway |
| REQ-PAY-003 | PaymentService.prePay(), StatusWorkflow |

---

## 4. データモデル

```typescript
// ParkingSpace Entity
interface ParkingSpace {
  id: string;                // SPACE-{floor}-{number}
  number: string;
  type: 'regular' | 'large' | 'motorcycle' | 'handicap';
  floor: number;
  area: string;
  state: 'empty' | 'occupied' | 'reserved' | 'maintenance';
  updatedAt: Date;
}

// EntryRecord Entity
interface EntryRecord {
  id: string;                // ENTRY-{timestamp}-{counter}
  licensePlate: string;
  vehicleType: 'regular' | 'large' | 'motorcycle';
  entryTime: Date;
  exitTime?: Date;
  spaceId?: string;
  status: 'active' | 'completed' | 'cancelled';
  createdAt: Date;
}

// Payment Entity
interface Payment {
  id: string;                // PAY-{timestamp}-{counter}
  entryId: string;
  amount: number;
  discountAmount: number;
  discountCode?: string;
  method: 'cash' | 'card' | 'qr';
  status: 'pending' | 'completed' | 'refunded';
  paidAt?: Date;
  createdAt: Date;
}

// FeeTable
interface FeeTable {
  freeMinutes: number;       // 最初の無料時間（分）
  ratePerUnit: number;       // 単位あたり料金
  unitMinutes: number;       // 料金単位（分）
  dailyMax: number;          // 24時間上限
}
```

---

## 5. レビュー履歴

| バージョン | 日付 | 変更内容 |
|------------|------|----------|
| 1.0.0 | 2026-01-04 | 初版作成 |
