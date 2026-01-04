# 設計書: Pet Clinic Reservation System
# バージョン: 1.0.0
# 作成日: 2026-01-04
# ドメイン: veterinary
# 関連要件: REQ-PETCLINIC-001

## 1. C4モデル

### Level 1: System Context

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           System Context                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│    ┌──────────┐         ┌─────────────────────────┐       ┌──────────┐  │
│    │  飼い主  │◄───────►│  Pet Clinic Reservation │◄─────►│  獣医師  │  │
│    │  (User)  │ 予約管理 │        System          │診療記録│  (Vet)   │  │
│    └──────────┘         └───────────┬─────────────┘       └──────────┘  │
│                                      │                                   │
│                                      │                                   │
│                              ┌───────▼───────┐                          │
│                              │   管理者      │                          │
│                              │  (Admin)      │                          │
│                              └───────────────┘                          │
│                                                                          │
│    外部システム:                                                         │
│    ┌──────────┐         ┌──────────┐         ┌──────────┐              │
│    │  Email   │         │   Push   │         │ Payment  │              │
│    │  Service │         │  Service │         │ Gateway  │              │
│    └──────────┘         └──────────┘         └──────────┘              │
└─────────────────────────────────────────────────────────────────────────┘
```

### Level 2: Container

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Container Diagram                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌────────────────┐      ┌────────────────┐      ┌────────────────┐     │
│  │  Web Frontend  │      │ Mobile App     │      │ Admin Portal   │     │
│  │  (React)       │      │ (React Native) │      │ (React)        │     │
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
│  │ Pet Service  │      │ Reservation  │      │ Medical      │          │
│  │              │      │ Service      │      │ Service      │          │
│  └──────┬───────┘      └──────┬───────┘      └──────┬───────┘          │
│         │                     │                     │                   │
│    ┌────▼────┐           ┌────▼────┐           ┌────▼────┐             │
│    │ Pet DB  │           │Reserve  │           │Medical  │             │
│    │(Postgres)│          │   DB    │           │   DB    │             │
│    └─────────┘           └─────────┘           └─────────┘             │
│                                                                          │
│  ┌──────────────┐      ┌──────────────┐      ┌──────────────┐          │
│  │ Auth Service │      │ Notification │      │ Schedule     │          │
│  │              │      │ Service      │      │ Service      │          │
│  └──────────────┘      └──────────────┘      └──────────────┘          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Level 3: Component

#### 3.1 Pet Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                      Pet Service                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────┐    ┌─────────────────┐                     │
│  │ PetController   │───►│ PetService      │                     │
│  │                 │    │                 │                     │
│  │ - createPet()   │    │ - register()    │                     │
│  │ - updatePet()   │    │ - update()      │                     │
│  │ - listPets()    │    │ - findByOwner() │                     │
│  │ - getPet()      │    │ - findById()    │                     │
│  └─────────────────┘    └────────┬────────┘                     │
│                                  │                               │
│                         ┌────────▼────────┐                     │
│                         │ PetRepository   │                     │
│                         │                 │                     │
│                         │ - save()        │                     │
│                         │ - update()      │                     │
│                         │ - findByOwner() │                     │
│                         │ - findById()    │                     │
│                         └────────┬────────┘                     │
│                                  │                               │
│                         ┌────────▼────────┐                     │
│                         │ PetHistoryRepo  │                     │
│                         │                 │                     │
│                         │ - saveSnapshot()│                     │
│                         │ - getHistory()  │                     │
│                         └─────────────────┘                     │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.2 Reservation Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                   Reservation Service                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ ReservationController│───►│ ReservationService  │             │
│  │                     │    │                     │             │
│  │ - create()          │    │ - book()            │             │
│  │ - update()          │    │ - reschedule()      │             │
│  │ - cancel()          │    │ - cancel()          │             │
│  │ - list()            │    │ - findByPet()       │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ AvailabilityChk │ │ ReservationRepo │ │ StatusWF  │ │
│           │                 │ │                 │ │           │ │
│           │ - checkSlot()   │ │ - save()        │ │ - transit│ │
│           │ - getAvailable()│ │ - update()      │ │           │ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
│                                                                  │
│           ┌─────────────────┐                                   │
│           │ DuplicateChecker│                                   │
│           │                 │                                   │
│           │ - checkDupe()   │                                   │
│           └─────────────────┘                                   │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.3 Medical Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                     Medical Service                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ MedicalController   │───►│ MedicalService      │             │
│  │                     │    │                     │             │
│  │ - createRecord()    │    │ - recordVisit()     │             │
│  │ - getHistory()      │    │ - getHistory()      │             │
│  │ - recordVaccine()   │    │ - recordVaccine()   │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ MedicalRecordRepo│ │ VaccineScheduler│ │ IdGenerator│ │
│           │                 │ │                 │ │           │ │
│           │ - save()        │ │ - calcNextDate()│ │ - generate│ │
│           │ - findByPet()   │ │ - setReminder() │ │           │ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.4 Schedule Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                    Schedule Service                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ ScheduleController  │───►│ ScheduleService     │             │
│  │                     │    │                     │             │
│  │ - setSchedule()     │    │ - setWorkHours()    │             │
│  │ - getSlots()        │    │ - getAvailSlots()   │             │
│  │ - blockDay()        │    │ - blockHoliday()    │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ ScheduleRepo    │ │ SlotGenerator   │ │ BlockRepo │ │
│           │                 │ │                 │ │           │ │
│           │ - save()        │ │ - generate()    │ │ - save()  │ │
│           │ - findByVet()   │ │ - inTimeRange() │ │ - list()  │ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.5 Notification Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                   Notification Service                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ NotificationController───►│ NotificationService │             │
│  │                     │    │                     │             │
│  │ - sendReminder()    │    │ - scheduleReminder()│             │
│  │ - sendUrgent()      │    │ - sendImmediate()   │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ EmailSender     │ │ PushSender      │ │ JobScheduler│
│           │                 │ │                 │ │           │ │
│           │ - send()        │ │ - send()        │ │ - schedule│ │
│           │ - template()    │ │ - broadcast()   │ │ - cancel()│ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.6 Auth Service Components

```
┌─────────────────────────────────────────────────────────────────┐
│                      Auth Service                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │ AuthController      │───►│ AuthService         │             │
│  │                     │    │                     │             │
│  │ - login()           │    │ - authenticate()    │             │
│  │ - verifyMFA()       │    │ - verifyTOTP()      │             │
│  │ - logout()          │    │ - invalidate()      │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                        │                         │
│                    ┌───────────────────┼───────────────────┐     │
│                    │                   │                   │     │
│           ┌────────▼────────┐ ┌────────▼────────┐ ┌───────▼───┐ │
│           │ UserRepository  │ │ TokenManager    │ │TOTPVerifier│ │
│           │                 │ │                 │ │           │ │
│           │ - findByEmail() │ │ - generate()    │ │ - verify()│ │
│           │ - save()        │ │ - validate()    │ │ - setup() │ │
│           └─────────────────┘ └─────────────────┘ └───────────┘ │
│                                                                  │
│           ┌─────────────────┐                                   │
│           │ PasswordHasher  │                                   │
│           │                 │                                   │
│           │ - hash()        │                                   │
│           │ - verify()      │                                   │
│           └─────────────────┘                                   │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. 設計パターン

| パターン | 適用箇所 | 理由 |
|----------|----------|------|
| **Repository** | 全Serviceのデータアクセス | データ永続化の抽象化、テスタビリティ向上 |
| **Service** | ビジネスロジック層 | ドメインロジックの集約 |
| **Factory** | IdGenerator | 一貫したID生成ロジック |
| **Strategy** | 認証方式（Password/TOTP） | 認証方式の切り替え可能性 |
| **State** | StatusWorkflow | 予約ステータス遷移の管理 |
| **Observer** | NotificationService | イベント駆動通知 |
| **Template Method** | EmailSender | メールテンプレート処理 |

---

## 3. トレーサビリティ

### 3.1 要件 → 設計マッピング

| 要件ID | 設計コンポーネント |
|--------|-------------------|
| REQ-PET-001 | PetService.register(), PetRepository.save() |
| REQ-PET-002 | PetService.update(), PetHistoryRepo.saveSnapshot() |
| REQ-PET-003 | PetService.findByOwner(), PetController.listPets() |
| REQ-RESERVE-001 | ReservationService.book(), AvailabilityChecker, DuplicateChecker |
| REQ-RESERVE-002 | ReservationService.reschedule(), StatusWorkflow |
| REQ-RESERVE-003 | ReservationService.cancel(), StatusWorkflow |
| REQ-RESERVE-004 | DuplicateChecker.checkDupe() |
| REQ-VET-001 | ScheduleService.setWorkHours(), ScheduleRepo |
| REQ-VET-002 | ScheduleService.getAvailSlots(), SlotGenerator |
| REQ-VET-003 | ScheduleService.blockHoliday(), BlockRepo |
| REQ-MEDICAL-001 | MedicalService.recordVisit(), MedicalRecordRepo |
| REQ-MEDICAL-002 | MedicalService.getHistory(), MedicalRecordRepo |
| REQ-MEDICAL-003 | VaccineScheduler.calcNextDate(), VaccineScheduler.setReminder() |
| REQ-NOTIFY-001 | NotificationService.scheduleReminder(), JobScheduler |
| REQ-NOTIFY-002 | NotificationService.scheduleReminder(), JobScheduler |
| REQ-NOTIFY-003 | NotificationService.sendImmediate(), PushSender |
| REQ-NFR-003 | AuthService, TOTPVerifier |
| REQ-NFR-004 | PasswordHasher, Database encryption at rest |
| REQ-NFR-005 | TokenManager.validate(), JWT middleware |

---

## 4. データモデル

### 4.1 エンティティ

```typescript
// Pet Entity
interface Pet {
  id: string;              // PET-{timestamp}-{counter}
  ownerId: string;
  name: string;
  species: 'dog' | 'cat' | 'bird' | 'other';
  breed: string;
  birthDate: Date;
  weight: number;
  allergies: string[];
  createdAt: Date;
  updatedAt: Date;
}

// Reservation Entity
interface Reservation {
  id: string;              // RES-{timestamp}-{counter}
  petId: string;
  vetId: string;
  startTime: Date;
  endTime: Date;
  type: 'checkup' | 'vaccination' | 'surgery' | 'emergency';
  status: 'pending' | 'confirmed' | 'rescheduled' | 'completed' | 'cancelled' | 'cancelled_with_fee';
  createdAt: Date;
  updatedAt: Date;
}

// MedicalRecord Entity
interface MedicalRecord {
  id: string;              // MED-{timestamp}-{counter}
  petId: string;
  reservationId: string;
  vetId: string;
  symptoms: string;
  diagnosis: string;
  treatment: string;
  prescriptions: Prescription[];
  nextVisitRecommendation: Date | null;
  isUrgent: boolean;
  createdAt: Date;
}

// VetSchedule Entity
interface VetSchedule {
  id: string;
  vetId: string;
  dayOfWeek: 0 | 1 | 2 | 3 | 4 | 5 | 6;
  startTime: string;       // HH:mm format
  endTime: string;
  breakStart: string | null;
  breakEnd: string | null;
}
```

---

## 5. API設計

### 5.1 RESTful Endpoints

| Method | Endpoint | 説明 | 関連要件 |
|--------|----------|------|----------|
| POST | /api/pets | ペット登録 | REQ-PET-001 |
| PUT | /api/pets/:id | ペット更新 | REQ-PET-002 |
| GET | /api/pets | ペット一覧 | REQ-PET-003 |
| POST | /api/reservations | 予約作成 | REQ-RESERVE-001 |
| PUT | /api/reservations/:id | 予約変更 | REQ-RESERVE-002 |
| DELETE | /api/reservations/:id | 予約キャンセル | REQ-RESERVE-003 |
| GET | /api/vets/:id/slots | 空き枠取得 | REQ-VET-002 |
| POST | /api/vets/:id/schedule | スケジュール設定 | REQ-VET-001 |
| POST | /api/medical-records | 診療記録作成 | REQ-MEDICAL-001 |
| GET | /api/pets/:id/medical-history | 診療履歴 | REQ-MEDICAL-002 |

---

## 6. レビュー履歴

| バージョン | 日付 | 変更内容 |
|------------|------|----------|
| 1.0.0 | 2026-01-04 | 初版作成 |
