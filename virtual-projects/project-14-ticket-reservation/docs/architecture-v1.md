# Project 14: Ticket Reservation System - Architecture Design v1.0

**プロジェクトID**: project-14-ticket-reservation  
**作成日**: 2026-01-04  
**フェーズ**: Phase 2 - アーキテクチャ設計  
**MUSUBIX Version**: 1.1.9

---

## 1. C4 Model

### 1.1 Context Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                        System Context                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────┐         ┌──────────────────────┐                  │
│  │   User   │ ──────▶ │  Ticket Reservation  │                  │
│  │  (CLI)   │ ◀────── │       System         │                  │
│  └──────────┘         └──────────────────────┘                  │
│                               │                                  │
│                               ▼                                  │
│                       ┌──────────────┐                          │
│                       │  JSON Files  │                          │
│                       │  (Storage)   │                          │
│                       └──────────────┘                          │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Container Diagram

```
┌──────────────────────────────────────────────────────────────────┐
│                    Ticket Reservation System                      │
├──────────────────────────────────────────────────────────────────┤
│                                                                   │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                      CLI Application                         │ │
│  │                     (TypeScript/Node.js)                     │ │
│  └─────────────────────────────────────────────────────────────┘ │
│                              │                                    │
│                              ▼                                    │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                   Application Services                       │ │
│  │  ┌─────────────┐ ┌──────────────┐ ┌────────────────┐        │ │
│  │  │EventService │ │ SeatService  │ │ReservationSvc │         │ │
│  │  └─────────────┘ └──────────────┘ └────────────────┘        │ │
│  └─────────────────────────────────────────────────────────────┘ │
│                              │                                    │
│                              ▼                                    │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                      Domain Layer                            │ │
│  │  ┌────────┐  ┌──────────┐  ┌─────────────────────────────┐  │ │
│  │  │ Event  │  │   Seat   │  │       Reservation           │  │ │
│  │  └────────┘  └──────────┘  └─────────────────────────────┘  │ │
│  │  ┌─────────────────────────────────────────────────────────┐│ │
│  │  │  Value Objects: SeatCode, Price, SeatConfig            ││ │
│  │  └─────────────────────────────────────────────────────────┘│ │
│  └─────────────────────────────────────────────────────────────┘ │
│                              │                                    │
│                              ▼                                    │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                  Infrastructure Layer                        │ │
│  │  ┌─────────────────────────────────────────────────────────┐│ │
│  │  │              JSON File Repositories                      ││ │
│  │  └─────────────────────────────────────────────────────────┘│ │
│  └─────────────────────────────────────────────────────────────┘ │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

### 1.3 Component Diagram

```
┌───────────────────────────────────────────────────────────────────────┐
│                          Domain Layer                                  │
├───────────────────────────────────────────────────────────────────────┤
│                                                                        │
│  Value Objects:                                                        │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────────┐       │
│  │    SeatCode    │  │     Price      │  │    SeatConfig      │       │
│  │  - row: string │  │ - amount: int  │  │ - rows: int        │       │
│  │  - number: int │  │                │  │ - seatsPerRow: int │       │
│  └────────────────┘  └────────────────┘  └────────────────────┘       │
│                                                                        │
│  Entities:                                                             │
│  ┌────────────────────────────────────────────────────────────────┐   │
│  │                           Event                                 │   │
│  │  - id: EventId (EVT-YYYYMMDD-NNN)                              │   │
│  │  - name: string                                                 │   │
│  │  - venue: string                                                │   │
│  │  - dateTime: Date                                               │   │
│  │  - basePrice: Price                                             │   │
│  │  - seatConfig: SeatConfig                                       │   │
│  │  - status: draft | active | completed | cancelled              │   │
│  └────────────────────────────────────────────────────────────────┘   │
│                                                                        │
│  ┌────────────────────────────────────────────────────────────────┐   │
│  │                            Seat                                 │   │
│  │  - id: SeatId (SEAT-{eventId}-{seatCode})                      │   │
│  │  - eventId: EventId                                             │   │
│  │  - seatCode: SeatCode                                           │   │
│  │  - price: Price                                                 │   │
│  │  - status: available | reserved | sold | unavailable           │   │
│  │  - version: number (optimistic locking)                        │   │
│  └────────────────────────────────────────────────────────────────┘   │
│                                                                        │
│  ┌────────────────────────────────────────────────────────────────┐   │
│  │                        Reservation                              │   │
│  │  - id: ReservationId (RSV-YYYYMMDD-NNN)                        │   │
│  │  - userId: UserId                                               │   │
│  │  - eventId: EventId                                             │   │
│  │  - seatIds: SeatId[] (max 10)                                  │   │
│  │  - totalPrice: Price                                            │   │
│  │  - status: pending | confirmed | cancelled | expired           │   │
│  │  - expiresAt: Date (pending only, +15min)                      │   │
│  └────────────────────────────────────────────────────────────────┘   │
│                                                                        │
└───────────────────────────────────────────────────────────────────────┘
```

---

## 2. 設計パターン適用

### 2.1 適用パターン一覧

| パターン | 適用箇所 | 要件トレース |
|---------|---------|-------------|
| BP-CODE-001 (Entity Input DTO) | createEvent(), createReservation() | REQ-TR-001, 020 |
| BP-CODE-002 (Date-based ID) | EventId, ReservationId | REQ-TR-001, 020 |
| BP-CODE-003 (Value Objects) | SeatCode, Price, SeatConfig | REQ-TR-010, 014 |
| BP-DESIGN-001 (Status Transition Map) | Event, Seat, Reservation | REQ-TR-003, 011, 021 |
| BP-DESIGN-002 (Repository Async) | All repositories | REQ-TR-NF-003 |
| BP-DESIGN-003 (Service Layer) | EventService, SeatService, ReservationService | All |
| BP-DESIGN-004 (Optimistic Locking) | Seat.version | REQ-TR-NF-002 |
| BP-TEST-001 (Counter Reset) | resetEventCounter(), etc. | Test isolation |

### 2.2 Status Transition Maps (BP-DESIGN-001)

```typescript
// Event Status Transitions
const validEventTransitions: Record<EventStatus, EventStatus[]> = {
  draft: ['active'],
  active: ['completed', 'cancelled'],
  completed: [],
  cancelled: [],
};

// Seat Status Transitions
const validSeatTransitions: Record<SeatStatus, SeatStatus[]> = {
  available: ['reserved', 'unavailable'],
  reserved: ['available', 'sold'],
  sold: ['available'], // refund case
  unavailable: ['available'],
};

// Reservation Status Transitions
const validReservationTransitions: Record<ReservationStatus, ReservationStatus[]> = {
  pending: ['confirmed', 'cancelled', 'expired'],
  confirmed: ['cancelled'],
  cancelled: [],
  expired: [],
};
```

---

## 3. ディレクトリ構成

```
project-14-ticket-reservation/
├── package.json
├── tsconfig.json
├── vitest.config.ts
├── docs/
│   ├── requirements-v2.md
│   └── architecture-v1.md
├── src/
│   ├── domain/
│   │   ├── value-objects/
│   │   │   ├── seat-code.ts        # SeatCode VO
│   │   │   ├── price.ts            # Price VO
│   │   │   └── seat-config.ts      # SeatConfig VO
│   │   ├── entities/
│   │   │   ├── event.ts            # Event Entity
│   │   │   ├── seat.ts             # Seat Entity
│   │   │   └── reservation.ts      # Reservation Entity
│   │   └── repositories/
│   │       └── interfaces.ts       # Repository Interfaces
│   ├── application/
│   │   ├── event-service.ts        # Event management
│   │   ├── seat-service.ts         # Seat management
│   │   └── reservation-service.ts  # Reservation management
│   ├── infrastructure/
│   │   └── storage/
│   │       └── json-repositories.ts
│   ├── shared/
│   │   └── result.ts               # Result type
│   └── cli/
│       └── index.ts                # CLI entry point
└── tests/
    ├── domain/
    │   ├── value-objects/
    │   └── entities/
    └── application/
```

---

## 4. 主要インターフェース

### 4.1 Service Input DTOs (BP-CODE-001)

```typescript
// Event Creation Input
interface CreateEventInput {
  name: string;
  venue: string;
  dateTime: string; // ISO format
  basePrice: number;
  rows: number;
  seatsPerRow: number;
}

// Reservation Creation Input
interface CreateReservationInput {
  userId: string;
  eventId: string;
  seatCodes: string[]; // ["A-1", "A-2"]
}

// Reservation Confirmation Input
interface ConfirmReservationInput {
  reservationId: string;
  userId: string;
}
```

### 4.2 Repository Interfaces

```typescript
interface EventRepository {
  save(event: Event): Promise<void>;
  findById(id: EventId): Promise<Event | null>;
  findByStatus(status: EventStatus): Promise<Event[]>;
  search(criteria: EventSearchCriteria): Promise<Event[]>;
}

interface SeatRepository {
  save(seat: Seat): Promise<void>;
  saveAll(seats: Seat[]): Promise<void>;
  findById(id: SeatId): Promise<Seat | null>;
  findByEventId(eventId: EventId): Promise<Seat[]>;
  findAvailableByEventId(eventId: EventId): Promise<Seat[]>;
}

interface ReservationRepository {
  save(reservation: Reservation): Promise<void>;
  findById(id: ReservationId): Promise<Reservation | null>;
  findByUserId(userId: UserId): Promise<Reservation[]>;
  findPendingExpired(now: Date): Promise<Reservation[]>;
}
```

---

## 5. 同時予約制御 (REQ-TR-030, 031)

### 5.1 楽観的ロック実装

```typescript
async function reserveSeats(seatIds: SeatId[]): Promise<Result<void, DomainError>> {
  // 1. Load seats with current versions
  const seats = await seatRepository.findByIds(seatIds);
  
  // 2. Check all available
  for (const seat of seats) {
    if (seat.status !== 'available') {
      return err(new DomainError(`Seat ${seat.seatCode} is not available`));
    }
  }
  
  // 3. Update with version check (optimistic lock)
  for (const seat of seats) {
    const updated = { ...seat, status: 'reserved', version: seat.version + 1 };
    try {
      await seatRepository.save(updated); // Throws if version mismatch
    } catch (e) {
      // Rollback already reserved seats
      return err(new DomainError('Concurrent modification detected'));
    }
  }
  
  return ok(undefined);
}
```

---

## 6. 要件トレーサビリティ

| 要件ID | 設計コンポーネント |
|--------|-------------------|
| REQ-TR-001 | Event Entity, CreateEventInput |
| REQ-TR-002 | EventService.search() |
| REQ-TR-003 | Event.status, validEventTransitions |
| REQ-TR-005 | EventService.create() → generateSeats() |
| REQ-TR-010 | SeatCode VO |
| REQ-TR-011 | Seat.status, validSeatTransitions |
| REQ-TR-014 | Seat.price, Price VO |
| REQ-TR-020 | Reservation Entity, generateReservationId() |
| REQ-TR-021 | ReservationService.create() |
| REQ-TR-022 | ReservationService.expirePending() |
| REQ-TR-026 | CreateReservationInput validation |
| REQ-TR-030 | Optimistic locking |
| REQ-TR-NF-002 | Seat.version |

---

## 7. ADR (Architecture Decision Records)

### ADR-001: 楽観的ロック採用

**コンテキスト**: 複数ユーザーが同時に同じ座席を予約しようとする場合の競合制御が必要

**決定**: バージョンフィールドによる楽観的ロックを採用

**理由**:
- JSONファイルストレージでは悲観的ロックが困難
- 座席予約は短時間で完了するため競合頻度は低い
- 競合時はユーザーに再試行を促す

---

**Document Version**: 1.0  
**Status**: Approved  
**Next**: Phase 3 - Task Decomposition
