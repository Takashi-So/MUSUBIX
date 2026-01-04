# DES-COWORK-001: コワーキングスペース予約システム設計書

## 1. C4モデル

### Level 1: System Context

```mermaid
flowchart TB
    subgraph Users["ユーザー"]
        Member[会員<br/>リモートワーカー]
        Admin[管理者<br/>スペースオーナー]
    end
    
    subgraph External["外部システム"]
        Payment[決済サービス<br/>Stripe]
        Calendar[カレンダー連携<br/>Google Calendar]
        Notification[通知サービス<br/>Firebase]
    end
    
    SpaceHub[SpaceHub System<br/>コワーキング予約]
    
    Member -->|予約・チェックイン| SpaceHub
    Admin -->|スペース管理| SpaceHub
    SpaceHub -->|決済処理| Payment
    SpaceHub -->|予定同期| Calendar
    SpaceHub -->|プッシュ通知| Notification
```

### Level 2: Container

```mermaid
flowchart TB
    subgraph SpaceHubSystem["SpaceHub System"]
        WebApp[Web Application<br/>React]
        MobileApp[Mobile App<br/>React Native]
        API[API Server<br/>Node.js/Express]
        DB[(Database<br/>PostgreSQL)]
        Cache[(Cache<br/>Redis)]
        Scheduler[Job Scheduler<br/>Bull]
    end
    
    WebApp --> API
    MobileApp --> API
    API --> DB
    API --> Cache
    API --> Scheduler
```

### Level 3: Component（API Server）

```mermaid
flowchart TB
    subgraph APIServer["API Server Components"]
        Router[Router]
        
        subgraph Controllers["Controllers"]
            SpaceCtrl[SpaceController]
            ReservationCtrl[ReservationController]
            CheckInCtrl[CheckInController]
            BillingCtrl[BillingController]
        end
        
        subgraph Services["Services"]
            SpaceSvc[SpaceService]
            ReservationSvc[ReservationService]
            CheckInSvc[CheckInService]
            BillingSvc[BillingService]
            TimeSlotSvc[TimeSlotService]
        end
        
        subgraph Repositories["Repositories"]
            SpaceRepo[SpaceRepository]
            ReservationRepo[ReservationRepository]
            UsageRepo[UsageRecordRepository]
        end
        
        Router --> Controllers
        Controllers --> Services
        Services --> Repositories
        ReservationSvc --> TimeSlotSvc
    end
```

## 2. ドメインモデル

```mermaid
classDiagram
    class Space {
        +string id
        +SpaceType type
        +string name
        +number capacity
        +Equipment[] equipment
        +number hourlyRate
        +boolean isActive
    }
    
    class Reservation {
        +string id
        +string userId
        +string spaceId
        +Date startTime
        +Date endTime
        +number attendees
        +ReservationStatus status
        +confirm()
        +checkIn()
        +complete()
        +cancel()
    }
    
    class CheckInRecord {
        +string id
        +string reservationId
        +Date checkedInAt
        +Date checkedOutAt
        +number actualMinutes
    }
    
    class UsageRecord {
        +string id
        +string reservationId
        +number reservedMinutes
        +number actualMinutes
        +number totalAmount
        +calculateAmount()
    }
    
    class TimeSlot {
        +Date startTime
        +Date endTime
        +boolean isAvailable
    }
    
    Space "1" --> "*" Reservation : has
    Reservation "1" --> "0..1" CheckInRecord : has
    Reservation "1" --> "1" UsageRecord : generates
```

## 3. 状態遷移（予約）

```mermaid
stateDiagram-v2
    [*] --> pending: 予約作成
    pending --> confirmed: 決済完了
    pending --> cancelled: キャンセル
    confirmed --> checked_in: チェックイン
    confirmed --> no_show: 15分経過
    confirmed --> cancelled: 2時間前までキャンセル
    checked_in --> completed: チェックアウト
    cancelled --> [*]
    no_show --> [*]
    completed --> [*]
```

## 4. 設計パターン適用

| パターン | 適用箇所 | 理由 |
|---------|---------|------|
| **Repository** | データアクセス | 永続化抽象化 |
| **State** | 予約ステータス | 複雑な状態遷移 |
| **Strategy** | 料金計算 | 料金体系の柔軟性 |
| **Factory** | ID生成 | 一意性保証 |
| **Observer** | 通知 | イベント駆動通知 |

## 5. TimeSlot計算ロジック

```typescript
interface ITimeSlotService {
  // 15分単位でスロットを生成
  generateSlots(date: Date, spaceId: string): TimeSlot[];
  
  // 空きスロットを検索
  findAvailableSlots(
    spaceId: string,
    date: Date,
    durationMinutes: number
  ): TimeSlot[];
  
  // 重複チェック（5分バッファ含む）
  hasConflict(
    spaceId: string,
    startTime: Date,
    endTime: Date,
    excludeReservationId?: string
  ): boolean;
}
```

## 6. 料金計算ロジック

```typescript
interface IBillingService {
  // 予約料金を計算
  calculateReservationFee(
    spaceId: string,
    startTime: Date,
    endTime: Date
  ): number;
  
  // キャンセル返金額を計算
  calculateRefund(
    reservationId: string,
    cancelTime: Date
  ): { amount: number; percentage: number };
  
  // 延長料金を計算
  calculateExtensionFee(
    reservationId: string,
    additionalMinutes: number
  ): number;
}
```

## 7. API設計

| Endpoint | Method | 説明 | 要件ID |
|----------|--------|------|--------|
| `/spaces` | GET | スペース検索 | REQ-COWORK-001-02 |
| `/spaces/:id/slots` | GET | 空きスロット取得 | REQ-COWORK-001-02 |
| `/reservations` | POST | 予約作成 | REQ-COWORK-001-03 |
| `/reservations/:id` | PUT | 予約変更 | REQ-COWORK-001-05 |
| `/reservations/:id/cancel` | PUT | 予約キャンセル | REQ-COWORK-001-06 |
| `/reservations/:id/check-in` | POST | チェックイン | REQ-COWORK-001-07 |
| `/reservations/:id/check-out` | POST | チェックアウト | REQ-COWORK-001-08 |
| `/users/:id/usage-history` | GET | 利用履歴 | REQ-COWORK-001-10 |

---
**作成日**: 2026-01-04  
**バージョン**: 1.0
