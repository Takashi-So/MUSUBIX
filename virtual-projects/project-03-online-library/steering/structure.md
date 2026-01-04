# Online Library Management System - Architecture Structure

## レイヤー構造

```
┌─────────────────────────────────────────────────────┐
│                   Presentation Layer                │
│  (REST API / GraphQL / Web UI)                      │
├─────────────────────────────────────────────────────┤
│                   Application Layer                 │
│  (Use Cases / Application Services)                 │
├─────────────────────────────────────────────────────┤
│                    Domain Layer                     │
│  (Entities / Value Objects / Domain Services)       │
├─────────────────────────────────────────────────────┤
│                Infrastructure Layer                 │
│  (Repositories / External Services / Persistence)   │
└─────────────────────────────────────────────────────┘
```

## ドメインモデル

### 集約（Aggregates）

1. **Book Aggregate**
   - Book（Entity）
   - ISBN（Value Object）
   - BookCopy（Entity）

2. **Member Aggregate**
   - Member（Entity）
   - MembershipCard（Value Object）
   - LoanHistory（Value Object）

3. **Loan Aggregate**
   - Loan（Entity）
   - LoanPeriod（Value Object）
   - Fine（Value Object）

4. **Reservation Aggregate**
   - Reservation（Entity）
   - ReservationQueue（Value Object）

## ディレクトリ構造

```
src/
├── domain/
│   ├── book/
│   │   ├── Book.ts
│   │   ├── BookCopy.ts
│   │   ├── ISBN.ts
│   │   └── BookRepository.ts
│   ├── member/
│   │   ├── Member.ts
│   │   ├── MembershipCard.ts
│   │   └── MemberRepository.ts
│   ├── loan/
│   │   ├── Loan.ts
│   │   ├── LoanPeriod.ts
│   │   ├── Fine.ts
│   │   └── LoanService.ts
│   └── reservation/
│       ├── Reservation.ts
│       └── ReservationQueue.ts
├── application/
│   ├── BookService.ts
│   ├── MemberService.ts
│   ├── LoanApplicationService.ts
│   └── ReservationService.ts
├── infrastructure/
│   ├── repositories/
│   └── external/
└── presentation/
    └── api/
```

## 設計パターン

| パターン | 適用箇所 | 目的 |
|---------|---------|------|
| Repository | 各集約のデータアクセス | 永続化の抽象化 |
| Factory | BookFactory, MemberFactory | 複雑なオブジェクト生成 |
| Domain Service | LoanService | 集約を跨ぐビジネスロジック |
| Strategy | NotificationStrategy | 通知方式の切り替え |
| Observer | LoanEventListener | イベント駆動処理 |

---

**生成日**: 2026-01-04
