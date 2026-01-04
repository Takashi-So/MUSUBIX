# 要件定義書: Online Library Management System
# バージョン: 1.1.0 (レビュー後修正版)
# 作成日: 2026-01-04
# 更新日: 2026-01-04
# ドメイン: library

## 1. プロジェクト概要

### 1.1 目的
オンライン図書館システムにより、蔵書管理、会員管理、貸出・返却・予約を効率化し、図書館員と会員双方の利便性を向上させる。

### 1.2 スコープ
- 蔵書管理（書籍の登録・更新・廃棄・検索）
- 会員管理（登録・更新・停止）
- 貸出管理（貸出・返却・延長・延滞管理）
- 予約管理（予約・キャンセル・順番管理）
- 通知機能（返却期限・予約通知）
- 統計機能（貸出統計・人気書籍）

---

## 2. 機能要件（EARS形式）

### 2.1 蔵書管理機能

#### REQ-BOOK-001: 書籍登録
**[Ubiquitous]**
THE システム SHALL 書籍情報（ISBN-13形式、タイトル最大500文字、著者名、出版社名、出版年4桁、カテゴリコード、所在棚番号）を入力フォームから受け取り、各フィールドのバリデーション（必須チェック、形式チェック）を実行し、成功時はデータベースへ永続化して書籍ID（BOOK-YYYYMMDD-NNN形式）を返却する

#### REQ-BOOK-002: 書籍検索
**[Event-driven]**
WHEN ユーザーが検索キーワードを入力して検索ボタンをクリックする
THE システム SHALL タイトル、著者、ISBN、カテゴリを対象に部分一致検索を実行し、関連度順で結果を表示する

#### REQ-BOOK-003: 書籍詳細表示
**[State-driven]**
WHILE ユーザーが書籍詳細画面を表示している
THE システム SHALL 当該書籍の全情報（基本情報、在庫状況、予約状況、貸出履歴サマリー）をリアルタイムで取得し表示する

#### REQ-BOOK-004: 書籍コピー管理
**[Ubiquitous]**
THE システム SHALL 同一ISBN書籍に対して複数の物理コピー（蔵書番号）を管理し、各コピーのステータス（available, on_loan, reserved, maintenance, retired）を個別に追跡する

#### REQ-BOOK-005: 書籍廃棄
**[Optional]**
IF 書籍コピーが廃棄対象として登録された場合
THEN THE システム SHALL 該当コピーに未返却の貸出がないことを確認（確認結果を画面表示）し、未返却がなければステータスを「retired」に変更、廃棄日時を記録、貸出対象リストから除外し、処理完了メッセージ（コピーID、廃棄日時）を返却する

### 2.2 会員管理機能

#### REQ-MEMBER-001: 会員登録
**[Event-driven]**
WHEN 新規会員が登録フォームを送信する
THE システム SHALL 会員情報（氏名、住所、電話番号、メールアドレス、生年月日）のバリデーションを実行し、会員番号を自動採番して会員レコードを作成する

#### REQ-MEMBER-002: 会員情報更新
**[Event-driven]**
WHEN 会員が自身の情報を更新して保存する
THE システム SHALL 変更前データを履歴テーブルに記録し、会員情報を更新する

#### REQ-MEMBER-003: 会員停止
**[Optional]**
IF 会員が180日以上貸出・予約活動を行っていない場合
THEN THE システム SHALL 会員ステータスを「inactive」に変更し、再活性化にはカウンターでの手続きを必要とする

#### REQ-MEMBER-004: 貸出上限管理
**[Ubiquitous]**
THE システム SHALL 会員種別ごとの貸出上限（一般会員:5冊、学生会員:10冊、シニア会員:7冊）を管理し、上限に達した会員の新規貸出を制限する

#### REQ-MEMBER-005: ペナルティ管理
**[Unwanted]**
THE システム SHALL NOT 延滞ペナルティ期間中（延滞日数×2日間）の会員に対して新規貸出を許可する

### 2.3 貸出管理機能

#### REQ-LOAN-001: 貸出処理
**[Event-driven]**
WHEN 図書館員が会員番号と蔵書番号を入力して貸出ボタンをクリックする
THE システム SHALL 会員の貸出資格（ペナルティなし、上限未達）と書籍の貸出可否（available状態）を確認し、条件を満たす場合に貸出レコードを作成して返却期限日を設定する

#### REQ-LOAN-002: 返却処理
**[Event-driven]**
WHEN 図書館員が蔵書番号を入力して返却ボタンをクリックする
THE システム SHALL 貸出レコードに返却日時を記録し、書籍ステータスを「available」に更新し、予約者がいる場合は予約ステータスを「ready」に変更する

#### REQ-LOAN-003: 貸出延長
**[Optional]**
IF 会員が返却期限前に延長をリクエストし、かつ当該書籍に予約がない場合
THEN THE システム SHALL 返却期限を14日間延長し、延長回数（最大2回）を記録する

#### REQ-LOAN-004: 延滞検出
**[Event-driven]**
WHEN 返却期限日の翌日午前0時になる
THE システム SHALL 未返却の貸出を「overdue」ステータスに更新し、延滞日数のカウントを開始する

#### REQ-LOAN-005: 延滞通知
**[Event-driven]**
WHEN 貸出が延滞状態になる
THE システム SHALL 会員のメールアドレスに延滞通知（書籍名、延滞日数、ペナルティ情報）を送信し、以降3日ごとにリマインダーを送信する

#### REQ-LOAN-006: 貸出禁止
**[Unwanted]**
THE システム SHALL NOT available以外のステータスの書籍コピーに対する貸出処理を許可する（エラーコードERR-LOAN-001を返却）

### 2.4 予約管理機能

#### REQ-RESERVE-001: 予約登録
**[Event-driven]**
WHEN 会員が貸出中の書籍に対して予約ボタンをクリックする
THE システム SHALL 予約キューの末尾に予約レコードを追加し、予約番号と推定待ち時間を表示する

#### REQ-RESERVE-002: 予約キャンセル
**[Event-driven]**
WHEN 会員が予約キャンセルボタンをクリックする
THE システム SHALL 予約レコードを削除し、後続の予約順番を繰り上げる

#### REQ-RESERVE-003: 予約取置通知
**[Event-driven]**
WHEN 予約書籍が返却され、予約ステータスが「ready」に変更される
THE システム SHALL 予約会員にメールで取置通知（書籍名、取置期限7日間、受取場所）を送信する

#### REQ-RESERVE-004: 予約期限切れ
**[Event-driven]**
WHEN 取置期限（7日間）が経過する
THE システム SHALL 予約をキャンセルし、次の予約者に通知するか、予約者がいなければ書籍を「available」に戻す

#### REQ-RESERVE-005: 予約上限
**[Unwanted]**
THE システム SHALL NOT 同一会員IDと同一ISBN（書籍）の組み合わせで2件以上の予約レコード作成を許可する（エラーコードERR-RESERVE-DUP、メッセージ「既にこの書籍を予約中です」を返却）

### 2.5 通知機能

#### REQ-NOTIFY-001: 返却期限リマインダー
**[Event-driven]**
WHEN 返却期限の3日前になる
THE システム SHALL 会員のメールアドレスに返却リマインダー（書籍名、返却期限日）を送信する

#### REQ-NOTIFY-002: 新着書籍通知
**[Optional]**
IF 会員がお気に入りカテゴリを登録している場合
THEN THE システム SHALL 該当カテゴリの新着書籍登録時に週次ダイジェストメールを送信する

### 2.6 統計機能

#### REQ-STATS-001: 貸出統計
**[Ubiquitous]**
THE システム SHALL 日次・週次・月次の貸出件数、返却件数、延滞件数をダッシュボードに表示する

#### REQ-STATS-002: 人気書籍ランキング
**[Event-driven]**
WHEN 管理者がランキング画面を表示する
THE システム SHALL 指定期間内の貸出回数に基づく書籍ランキングを上位20件表示する

---

## 3. 非機能要件

### 3.1 パフォーマンス

#### REQ-NFR-001: レスポンス時間
**[Ubiquitous]**
THE システム SHALL 全てのAPI呼び出しに対して95パーセンタイルで2秒以内にレスポンスを返却する

#### REQ-NFR-002: 検索レスポンス
**[Ubiquitous]**
THE システム SHALL 10万件の蔵書データに対する全文検索を500ミリ秒以内に完了する

### 3.2 セキュリティ

#### REQ-NFR-003: 認証
**[Ubiquitous]**
THE システム SHALL JWTベースの認証を実装し、トークン有効期限を24時間とする

#### REQ-NFR-004: 認可
**[Ubiquitous]**
THE システム SHALL ロールベースアクセス制御（RBAC）を実装し、会員・図書館員・管理者の3ロールを区別する

#### REQ-NFR-005: データ保護
**[Ubiquitous]**
THE システム SHALL 会員の個人情報（住所、電話番号）をAES-256で暗号化して保存する

### 3.3 可用性

#### REQ-NFR-006: 稼働率
**[Ubiquitous]**
THE システム SHALL 月間稼働率99.5%以上を維持する

---

## 4. トレーサビリティマトリクス

| 要件ID | カテゴリ | EARSパターン | 優先度 | ステータス |
|--------|----------|--------------|--------|------------|
| REQ-BOOK-001 | 蔵書管理 | Ubiquitous | P0 | Draft |
| REQ-BOOK-002 | 蔵書管理 | Event-driven | P0 | Draft |
| REQ-BOOK-003 | 蔵書管理 | State-driven | P1 | Draft |
| REQ-BOOK-004 | 蔵書管理 | Ubiquitous | P0 | Draft |
| REQ-BOOK-005 | 蔵書管理 | Optional | P2 | Draft |
| REQ-MEMBER-001 | 会員管理 | Event-driven | P0 | Draft |
| REQ-MEMBER-002 | 会員管理 | Event-driven | P1 | Draft |
| REQ-MEMBER-003 | 会員管理 | Optional | P2 | Draft |
| REQ-MEMBER-004 | 会員管理 | Ubiquitous | P0 | Draft |
| REQ-MEMBER-005 | 会員管理 | Unwanted | P0 | Draft |
| REQ-LOAN-001 | 貸出管理 | Event-driven | P0 | Draft |
| REQ-LOAN-002 | 貸出管理 | Event-driven | P0 | Draft |
| REQ-LOAN-003 | 貸出管理 | Optional | P1 | Draft |
| REQ-LOAN-004 | 貸出管理 | Event-driven | P0 | Draft |
| REQ-LOAN-005 | 貸出管理 | Event-driven | P1 | Draft |
| REQ-LOAN-006 | 貸出管理 | Unwanted | P0 | Draft |
| REQ-RESERVE-001 | 予約管理 | Event-driven | P0 | Draft |
| REQ-RESERVE-002 | 予約管理 | Event-driven | P1 | Draft |
| REQ-RESERVE-003 | 予約管理 | Event-driven | P0 | Draft |
| REQ-RESERVE-004 | 予約管理 | Event-driven | P1 | Draft |
| REQ-RESERVE-005 | 予約管理 | Unwanted | P0 | Draft |
| REQ-NOTIFY-001 | 通知 | Event-driven | P1 | Draft |
| REQ-NOTIFY-002 | 通知 | Optional | P2 | Draft |
| REQ-STATS-001 | 統計 | Ubiquitous | P1 | Draft |
| REQ-STATS-002 | 統計 | Event-driven | P2 | Draft |
| REQ-NFR-001 | 非機能 | Ubiquitous | P0 | Draft |
| REQ-NFR-002 | 非機能 | Ubiquitous | P1 | Draft |
| REQ-NFR-003 | 非機能 | Ubiquitous | P0 | Draft |
| REQ-NFR-004 | 非機能 | Ubiquitous | P0 | Draft |
| REQ-NFR-005 | 非機能 | Ubiquitous | P0 | Draft |
| REQ-NFR-006 | 非機能 | Ubiquitous | P1 | Draft |

---

## 5. 変更履歴

| バージョン | 日付 | 変更者 | 変更内容 |
|-----------|------|--------|---------|
| 1.0.0 | 2026-01-04 | AI Agent | 初版作成 |
| 1.1.0 | 2026-01-04 | AI Agent | EARS検証結果に基づく改善（REQ-BOOK-001, REQ-BOOK-005, REQ-RESERVE-005の具体化）|

---

**生成日**: 2026-01-04
**ドメイン**: library
**EARS準拠**: Yes
