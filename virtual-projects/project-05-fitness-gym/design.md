# Design Document: FitGym Pro

## 1. C4 Context Diagram

```
+-------------------+
|      Member       |
|     (Person)      |
+-------------------+
         |
         | uses
         v
+-------------------+
|   FitGym Pro      |
|    (System)       |
+-------------------+
         |
    +----+----+----+
    |    |    |    |
    v    v    v    v
+------+ +------+ +------+ +------+
|Payment| |Email | |Card  | |Mobile|
|Gateway| |Service| |Reader| |App  |
+------+ +------+ +------+ +------+
```

## 2. C4 Container Diagram

| Container | Technology | Description |
|-----------|------------|-------------|
| Web App | React + TypeScript | Member/Staff Portal |
| Mobile App | React Native | Member Mobile App |
| API Server | Node.js + Express | REST API Backend |
| Database | PostgreSQL | Primary Data Store |
| Cache | Redis | Session & Real-time Data |
| Message Queue | RabbitMQ | Async Processing |

## 3. C4 Component Diagram

### 3.1 Core Components

| ID | Name | Type | Description | Traces To |
|----|------|------|-------------|-----------|
| DES-GYM-001 | MemberService | service | 会員登録・認証・プロフィール管理 | REQ-GYM-001, REQ-GYM-002, REQ-GYM-003 |
| DES-GYM-002 | MembershipService | service | 会員プラン・契約・更新管理 | REQ-GYM-003, REQ-GYM-004, REQ-GYM-015 |
| DES-GYM-003 | BookingService | service | クラス・PT予約・キャンセル管理 | REQ-GYM-005, REQ-GYM-006, REQ-GYM-007 |
| DES-GYM-004 | TrainerService | service | トレーナー登録・スケジュール管理 | REQ-GYM-009, REQ-GYM-010, REQ-GYM-011 |
| DES-GYM-005 | EquipmentService | service | 設備予約・メンテナンス管理 | REQ-GYM-012, REQ-GYM-013, REQ-GYM-014 |
| DES-GYM-006 | PaymentService | service | 決済処理・自動課金・履歴管理 | REQ-GYM-015, REQ-GYM-016, REQ-GYM-017 |
| DES-GYM-007 | NotificationService | service | リマインダー・アラート配信 | REQ-GYM-008, REQ-GYM-017 |
| DES-GYM-008 | ReportService | service | 利用統計・収益レポート生成 | REQ-GYM-018, REQ-GYM-019, REQ-GYM-020 |

### 3.2 Supporting Components

| ID | Name | Type | Description |
|----|------|------|-------------|
| DES-GYM-009 | AuthService | service | JWT認証・MFA・セッション管理 |
| DES-GYM-010 | AccessControlService | service | 入退館管理・カードリーダー連携 |
| DES-GYM-011 | ScheduleService | service | スケジュール・カレンダー管理 |
| DES-GYM-012 | OccupancyService | service | 混雑状況リアルタイム監視 |

### 3.3 Data Models

| Entity | Attributes | Relations |
|--------|------------|-----------|
| Member | id, name, email, phone, emergencyContact, status | has MembershipPlan, has Bookings |
| MembershipPlan | id, name, price, sessions, duration, features | belongs to Member |
| Booking | id, type, dateTime, status, memberId, trainerId | belongs to Member, Trainer, Class |
| Trainer | id, name, certifications, specializations, schedule | has Bookings, has Performance |
| FitnessClass | id, name, instructor, capacity, schedule, room | has Bookings |
| Equipment | id, name, type, status, lastMaintenance | has Reservations |
| Payment | id, amount, date, method, status, memberId | belongs to Member |

### 3.4 Component Relationships

```
┌─────────────────────────────────────────────────────────────┐
│                        API Gateway                          │
└─────────────────────────────────────────────────────────────┘
                              │
          ┌───────────────────┼───────────────────┐
          │                   │                   │
          ▼                   ▼                   ▼
    ┌───────────┐      ┌───────────┐      ┌───────────┐
    │  Member   │      │  Booking  │      │  Trainer  │
    │  Service  │◄────►│  Service  │◄────►│  Service  │
    └───────────┘      └───────────┘      └───────────┘
          │                   │                   │
          ▼                   ▼                   ▼
    ┌───────────┐      ┌───────────┐      ┌───────────┐
    │Membership │      │ Schedule  │      │Performance│
    │  Service  │      │  Service  │      │  Service  │
    └───────────┘      └───────────┘      └───────────┘
          │                   │
          └─────────┬─────────┘
                    ▼
             ┌───────────┐      ┌───────────┐
             │  Payment  │◄────►│Notification│
             │  Service  │      │  Service   │
             └───────────┘      └───────────┘
```

## 4. Design Patterns Applied

| Pattern | Applied To | Rationale |
|---------|-----------|-----------|
| Repository | All Services | Data access abstraction |
| Factory | BookingService | Different booking types creation |
| Observer | NotificationService | Event-driven notifications |
| Strategy | PaymentService | Multiple payment methods |
| State | MembershipService | Membership status transitions |

## 5. API Design

### 5.1 Member APIs

| Method | Endpoint | Description |
|--------|----------|-------------|
| POST | /api/members | Register new member |
| GET | /api/members/:id | Get member profile |
| PUT | /api/members/:id | Update member info |
| POST | /api/members/:id/checkin | Member check-in |

### 5.2 Booking APIs

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | /api/classes | List available classes |
| POST | /api/bookings | Create booking |
| DELETE | /api/bookings/:id | Cancel booking |
| GET | /api/bookings/member/:id | Member's bookings |

### 5.3 Trainer APIs

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | /api/trainers | List trainers |
| GET | /api/trainers/:id/availability | Get availability |
| POST | /api/trainers/:id/sessions | Book PT session |

## 6. Security Design

| Aspect | Implementation |
|--------|----------------|
| Authentication | JWT + Refresh Token |
| Authorization | RBAC (Member, Trainer, Staff, Admin) |
| Data Encryption | AES-256 at rest, TLS 1.3 in transit |
| API Security | Rate limiting, Input validation, CORS |

## 7. Traceability Matrix

| Requirement | Design Component | Status |
|-------------|------------------|--------|
| REQ-GYM-001 | DES-GYM-001 MemberService | ✓ |
| REQ-GYM-002 | DES-GYM-001, DES-GYM-010 | ✓ |
| REQ-GYM-003 | DES-GYM-002 MembershipService | ✓ |
| REQ-GYM-004 | DES-GYM-002, DES-GYM-009 | ✓ |
| REQ-GYM-005 | DES-GYM-003 BookingService | ✓ |
| REQ-GYM-006 | DES-GYM-003, DES-GYM-004 | ✓ |
| REQ-GYM-007 | DES-GYM-003, DES-GYM-006 | ✓ |
| REQ-GYM-008 | DES-GYM-007 NotificationService | ✓ |
| REQ-GYM-009 | DES-GYM-004 TrainerService | ✓ |
| REQ-GYM-010 | DES-GYM-004, DES-GYM-011 | ✓ |
| REQ-GYM-011 | DES-GYM-004 | ✓ |
| REQ-GYM-012 | DES-GYM-005 EquipmentService | ✓ |
| REQ-GYM-013 | DES-GYM-005 | ✓ |
| REQ-GYM-014 | DES-GYM-012 OccupancyService | ✓ |
| REQ-GYM-015 | DES-GYM-006 PaymentService | ✓ |
| REQ-GYM-016 | DES-GYM-006 | ✓ |
| REQ-GYM-017 | DES-GYM-006, DES-GYM-007 | ✓ |
| REQ-GYM-018 | DES-GYM-008 ReportService | ✓ |
| REQ-GYM-019 | DES-GYM-008 | ✓ |
| REQ-GYM-020 | DES-GYM-008 | ✓ |

---
*Generated by MUSUBIX SDD Workflow*
*Version: 1.1.3*
*Date: 2026-01-04*
