# 設計書: Online Library Management System
# バージョン: 1.0.0
# 作成日: 2026-01-04
# ドメイン: library
# 設計方式: C4 Model

## 1. C4 Context Diagram（コンテキスト図）

```
┌─────────────────────────────────────────────────────────────────┐
│                     External Actors                              │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────┐   ┌──────────┐   ┌──────────┐                    │
│  │  会員     │   │ 図書館員  │   │ 管理者    │                    │
│  │ (Member) │   │(Librarian)│   │ (Admin)  │                    │
│  └────┬─────┘   └────┬─────┘   └────┬─────┘                    │
│       │              │              │                           │
└───────┼──────────────┼──────────────┼───────────────────────────┘
        │              │              │
        ▼              ▼              ▼
┌─────────────────────────────────────────────────────────────────┐
│                                                                  │
│           Online Library Management System                       │
│                                                                  │
│  - 蔵書管理      - 貸出管理        - 統計機能                    │
│  - 会員管理      - 予約管理        - 通知機能                    │
│                                                                  │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│                     External Systems                             │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────┐   ┌──────────┐   ┌──────────┐                    │
│  │Email     │   │ Search   │   │ Auth     │                    │
│  │Service   │   │ Engine   │   │ Provider │                    │
│  └──────────┘   └──────────┘   └──────────┘                    │
└─────────────────────────────────────────────────────────────────┘
```

### 1.1 アクター定義

| アクター | 説明 | 主な操作 |
|---------|------|---------|
| 会員（Member） | 図書館の登録会員 | 検索、予約、貸出履歴確認 |
| 図書館員（Librarian） | 図書館のスタッフ | 貸出・返却処理、蔵書管理 |
| 管理者（Admin） | システム管理者 | 統計確認、設定変更、ユーザー管理 |

### 1.2 外部システム

| システム | 説明 | 連携方法 |
|---------|------|---------|
| Email Service | メール送信サービス | SMTP / API |
| Search Engine | 全文検索エンジン（Elasticsearch） | REST API |
| Auth Provider | 認証プロバイダ | OAuth2 / JWT |

---

## 2. C4 Container Diagram（コンテナ図）

```
┌─────────────────────────────────────────────────────────────────┐
│                Online Library Management System                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────┐     ┌─────────────────┐                   │
│  │   Web Client    │     │  Mobile Client  │                   │
│  │   (React SPA)   │     │  (React Native) │                   │
│  └────────┬────────┘     └────────┬────────┘                   │
│           │                       │                             │
│           └───────────┬───────────┘                             │
│                       ▼                                         │
│           ┌───────────────────────┐                             │
│           │      API Gateway      │                             │
│           │       (Hono)          │                             │
│           └───────────┬───────────┘                             │
│                       │                                         │
│    ┌──────────────────┼──────────────────┐                     │
│    │                  │                  │                     │
│    ▼                  ▼                  ▼                     │
│  ┌────────┐    ┌────────────┐    ┌────────────┐               │
│  │ Book   │    │   Loan     │    │Notification│               │
│  │Service │    │  Service   │    │  Service   │               │
│  └───┬────┘    └─────┬──────┘    └─────┬──────┘               │
│      │               │                 │                       │
│      └───────────────┼─────────────────┘                       │
│                      ▼                                         │
│              ┌───────────────┐                                 │
│              │   PostgreSQL  │                                 │
│              │   (Primary)   │                                 │
│              └───────────────┘                                 │
│                                                                │
│  ┌────────────┐      ┌────────────┐                           │
│  │   Redis    │      │Elasticsearch│                           │
│  │  (Cache)   │      │  (Search)   │                           │
│  └────────────┘      └────────────┘                           │
│                                                                │
└─────────────────────────────────────────────────────────────────┘
```

### 2.1 コンテナ定義

| コンテナ | 技術 | 責務 |
|---------|------|------|
| API Gateway | Hono (Node.js) | リクエストルーティング、認証、レート制限 |
| Book Service | TypeScript | 蔵書管理、書籍CRUD |
| Loan Service | TypeScript | 貸出・返却・予約管理 |
| Notification Service | TypeScript | 通知送信（メール、プッシュ） |
| PostgreSQL | PostgreSQL 15 | 永続データストレージ |
| Redis | Redis 7 | セッション、キャッシュ、予約キュー |
| Elasticsearch | Elasticsearch 8 | 全文検索インデックス |

---

## 3. C4 Component Diagram（コンポーネント図）

### 3.1 Book Service コンポーネント

```
┌─────────────────────────────────────────────────────────────────┐
│                        Book Service                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌────────────────┐     ┌────────────────┐                     │
│  │ BookController │────▶│ BookAppService │                     │
│  └────────────────┘     └───────┬────────┘                     │
│                                 │                               │
│                    ┌────────────┼────────────┐                 │
│                    ▼            ▼            ▼                 │
│             ┌──────────┐ ┌──────────┐ ┌──────────┐            │
│             │   Book   │ │BookCopy  │ │  ISBN    │            │
│             │  Entity  │ │  Entity  │ │ValueObj  │            │
│             └────┬─────┘ └────┬─────┘ └──────────┘            │
│                  │            │                                │
│                  ▼            ▼                                │
│             ┌──────────────────────────┐                       │
│             │     BookRepository       │                       │
│             └──────────────────────────┘                       │
│                          │                                     │
└──────────────────────────┼─────────────────────────────────────┘
                           ▼
                    [PostgreSQL]
```

#### コンポーネント詳細

| コンポーネント | パターン | 責務 | トレース |
|--------------|---------|------|---------|
| BookController | Controller | HTTPリクエスト処理 | REQ-BOOK-001〜005 |
| BookAppService | Application Service | ユースケース実装 | REQ-BOOK-001〜005 |
| Book | Entity (Aggregate Root) | 書籍ドメインモデル | REQ-BOOK-001 |
| BookCopy | Entity | 蔵書コピー管理 | REQ-BOOK-004 |
| ISBN | Value Object | ISBN検証 | REQ-BOOK-001 |
| BookRepository | Repository | データアクセス抽象化 | - |

### 3.2 Loan Service コンポーネント

```
┌─────────────────────────────────────────────────────────────────┐
│                        Loan Service                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌────────────────┐     ┌────────────────┐                     │
│  │LoanController  │────▶│LoanAppService  │                     │
│  └────────────────┘     └───────┬────────┘                     │
│                                 │                               │
│          ┌──────────────────────┼──────────────────────┐       │
│          ▼                      ▼                      ▼       │
│   ┌──────────┐          ┌──────────────┐       ┌──────────┐   │
│   │   Loan   │          │ LoanService  │       │Reservation│   │
│   │  Entity  │          │(Domain Svc)  │       │  Entity   │   │
│   └────┬─────┘          └──────────────┘       └────┬─────┘   │
│        │                        │                   │          │
│        ▼                        ▼                   ▼          │
│   ┌──────────┐          ┌──────────────┐    ┌──────────────┐  │
│   │LoanRepo  │          │ MemberRepo   │    │ReservationQ  │  │
│   └──────────┘          └──────────────┘    └──────────────┘  │
│        │                        │                   │          │
└────────┼────────────────────────┼───────────────────┼──────────┘
         ▼                        ▼                   ▼
   [PostgreSQL]             [PostgreSQL]          [Redis]
```

#### コンポーネント詳細

| コンポーネント | パターン | 責務 | トレース |
|--------------|---------|------|---------|
| LoanController | Controller | HTTPリクエスト処理 | REQ-LOAN-001〜006, REQ-RESERVE-001〜005 |
| LoanAppService | Application Service | 貸出ユースケース | REQ-LOAN-001〜006 |
| Loan | Entity (Aggregate Root) | 貸出ドメインモデル | REQ-LOAN-001 |
| LoanService | Domain Service | 貸出ビジネスロジック | REQ-LOAN-001〜003 |
| Reservation | Entity | 予約ドメインモデル | REQ-RESERVE-001 |
| ReservationQueue | Value Object | 予約順番管理 | REQ-RESERVE-001, 004 |
| LoanRepository | Repository | 貸出データアクセス | - |
| MemberRepository | Repository | 会員データアクセス | REQ-MEMBER-004, 005 |

### 3.3 Member Service コンポーネント

```
┌─────────────────────────────────────────────────────────────────┐
│                       Member Service                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌────────────────┐     ┌────────────────┐                     │
│  │MemberController│────▶│MemberAppService│                     │
│  └────────────────┘     └───────┬────────┘                     │
│                                 │                               │
│                    ┌────────────┼────────────┐                 │
│                    ▼            ▼            ▼                 │
│             ┌──────────┐ ┌──────────────┐ ┌──────────┐        │
│             │  Member  │ │MembershipCard│ │  Penalty │        │
│             │  Entity  │ │  ValueObj    │ │  Entity  │        │
│             └────┬─────┘ └──────────────┘ └────┬─────┘        │
│                  │                             │               │
│                  ▼                             ▼               │
│             ┌────────────────────────────────────┐            │
│             │         MemberRepository           │            │
│             └────────────────────────────────────┘            │
│                          │                                     │
└──────────────────────────┼─────────────────────────────────────┘
                           ▼
                    [PostgreSQL]
```

#### コンポーネント詳細

| コンポーネント | パターン | 責務 | トレース |
|--------------|---------|------|---------|
| MemberController | Controller | HTTPリクエスト処理 | REQ-MEMBER-001〜005 |
| MemberAppService | Application Service | 会員ユースケース | REQ-MEMBER-001〜003 |
| Member | Entity (Aggregate Root) | 会員ドメインモデル | REQ-MEMBER-001 |
| MembershipCard | Value Object | 会員証情報 | REQ-MEMBER-004 |
| Penalty | Entity | ペナルティ管理 | REQ-MEMBER-005 |
| MemberRepository | Repository | 会員データアクセス | - |

---

## 4. 設計パターン

### 4.1 適用パターン一覧

| パターン | 適用箇所 | 目的 | トレース |
|---------|---------|------|---------|
| Repository | 各Aggregate | データアクセス抽象化 | Article VII |
| Factory | BookFactory, MemberFactory | 複雑なオブジェクト生成 | Article VII |
| Domain Service | LoanService | 集約を跨ぐビジネスロジック | REQ-LOAN-001 |
| Strategy | NotificationStrategy | 通知方式の切り替え | REQ-NOTIFY-001, 002 |
| Observer | LoanEventListener | イベント駆動処理 | REQ-LOAN-004, 005 |
| Value Object | ISBN, MembershipCard | 不変の値表現 | DDD |
| Aggregate | Book, Member, Loan | 整合性境界 | DDD |

### 4.2 パターン適用詳細

#### Repository パターン
```typescript
interface BookRepository {
  findById(id: BookId): Promise<Book | null>;
  findByISBN(isbn: ISBN): Promise<Book | null>;
  save(book: Book): Promise<void>;
  delete(id: BookId): Promise<void>;
  search(query: SearchQuery): Promise<Book[]>;
}
```

#### Factory パターン
```typescript
class BookFactory {
  static create(params: CreateBookParams): Book {
    const isbn = new ISBN(params.isbn);
    return new Book(
      BookId.generate(),
      isbn,
      params.title,
      params.author,
      params.publisher,
      params.publishYear,
      params.category,
      params.shelfLocation
    );
  }
}
```

#### Strategy パターン（通知）
```typescript
interface NotificationStrategy {
  send(notification: Notification): Promise<void>;
}

class EmailNotificationStrategy implements NotificationStrategy { }
class PushNotificationStrategy implements NotificationStrategy { }
```

---

## 5. データモデル

### 5.1 エンティティ関連図

```
┌────────────────┐     ┌────────────────┐     ┌────────────────┐
│     Book       │     │    BookCopy    │     │     Loan       │
├────────────────┤     ├────────────────┤     ├────────────────┤
│ id: BookId     │◀───▶│ id: CopyId     │◀───▶│ id: LoanId     │
│ isbn: ISBN     │ 1:N │ bookId: BookId │ 1:1 │ copyId: CopyId │
│ title: string  │     │ status: Status │     │ memberId       │
│ author: string │     │ shelfLocation  │     │ loanDate       │
│ publisher      │     │ acquiredAt     │     │ dueDate        │
│ publishYear    │     │ retiredAt?     │     │ returnedAt?    │
│ category       │     └────────────────┘     │ status         │
└────────────────┘                            └────────────────┘
                                                      │
                                                      │ N:1
                                                      ▼
┌────────────────┐     ┌────────────────┐     ┌────────────────┐
│   Reservation  │     │    Member      │     │    Penalty     │
├────────────────┤     ├────────────────┤     ├────────────────┤
│ id: ResId      │     │ id: MemberId   │◀───▶│ id: PenaltyId  │
│ bookId: BookId │◀───▶│ name: string   │ 1:N │ memberId       │
│ memberId       │ N:1 │ email: string  │     │ reason         │
│ position       │     │ phone: string  │     │ startDate      │
│ createdAt      │     │ memberType     │     │ endDate        │
│ status         │     │ status         │     │ status         │
│ readyAt?       │     │ createdAt      │     └────────────────┘
└────────────────┘     └────────────────┘
```

### 5.2 ステータス遷移

#### BookCopy Status
```
available → on_loan → available
    │           │
    ▼           ▼
reserved    overdue → available
    │
    ▼
maintenance → available
    │
    ▼
retired (終了状態)
```

#### Loan Status
```
active → returned
   │
   ▼
overdue → returned
```

#### Reservation Status
```
waiting → ready → completed
    │       │
    ▼       ▼
cancelled cancelled
```

---

## 6. トレーサビリティマトリクス（設計↔要件）

| 設計要素 | 関連要件 | 検証方法 |
|---------|---------|---------|
| Book Entity | REQ-BOOK-001, 002, 003 | Unit Test |
| BookCopy Entity | REQ-BOOK-004, 005 | Unit Test |
| BookRepository | REQ-BOOK-001〜005 | Integration Test |
| Member Entity | REQ-MEMBER-001, 002, 003 | Unit Test |
| MembershipCard VO | REQ-MEMBER-004 | Unit Test |
| Penalty Entity | REQ-MEMBER-005 | Unit Test |
| Loan Entity | REQ-LOAN-001, 002, 003 | Unit Test |
| LoanService | REQ-LOAN-001〜006 | Unit Test |
| Reservation Entity | REQ-RESERVE-001〜005 | Unit Test |
| ReservationQueue | REQ-RESERVE-001, 004 | Unit Test |
| NotificationStrategy | REQ-NOTIFY-001, 002 | Unit Test |
| LoanEventListener | REQ-LOAN-004, 005 | Integration Test |

---

## 7. API設計

### 7.1 RESTful エンドポイント

| メソッド | パス | 説明 | 要件 |
|---------|------|------|------|
| POST | /api/books | 書籍登録 | REQ-BOOK-001 |
| GET | /api/books | 書籍検索 | REQ-BOOK-002 |
| GET | /api/books/:id | 書籍詳細 | REQ-BOOK-003 |
| POST | /api/books/:id/copies | コピー追加 | REQ-BOOK-004 |
| DELETE | /api/books/:id/copies/:copyId | コピー廃棄 | REQ-BOOK-005 |
| POST | /api/members | 会員登録 | REQ-MEMBER-001 |
| PUT | /api/members/:id | 会員更新 | REQ-MEMBER-002 |
| POST | /api/loans | 貸出処理 | REQ-LOAN-001 |
| POST | /api/loans/:id/return | 返却処理 | REQ-LOAN-002 |
| POST | /api/loans/:id/extend | 延長 | REQ-LOAN-003 |
| POST | /api/reservations | 予約登録 | REQ-RESERVE-001 |
| DELETE | /api/reservations/:id | 予約キャンセル | REQ-RESERVE-002 |

---

## 8. 変更履歴

| バージョン | 日付 | 変更者 | 変更内容 |
|-----------|------|--------|---------|
| 1.0.0 | 2026-01-04 | AI Agent | 初版作成（C4 Context/Container/Component） |

---

**生成日**: 2026-01-04
**設計方式**: C4 Model
**SOLID準拠**: Yes
