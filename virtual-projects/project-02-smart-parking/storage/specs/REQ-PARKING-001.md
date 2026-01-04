# 要件定義書: Smart Parking Management System
# バージョン: 1.0.0
# 作成日: 2026-01-04
# ドメイン: parking

## 1. プロジェクト概要

### 1.1 目的
駐車場の入出庫管理、空き状況のリアルタイム表示、料金計算を自動化し、ユーザーの利便性と運営効率を向上させるシステムを構築する。

### 1.2 スコープ
- 駐車スペース管理
- 入出庫処理
- 料金計算・精算
- 予約機能
- 満空表示

---

## 2. 機能要件（EARS形式）

### 2.1 駐車スペース管理

#### REQ-SPACE-001: スペース登録
**[Ubiquitous]**
THE システム SHALL 駐車スペース情報（番号、タイプ[普通車/大型車/バイク/障害者用]、フロア、エリア）を登録し、各スペースに一意のIDを付与する

#### REQ-SPACE-002: スペース状態更新
**[Event-driven]**
WHEN IoTセンサーが車両の検知状態を変更する
THE システム SHALL 該当スペースの状態（empty/occupied/reserved/maintenance）を1秒以内に更新する

#### REQ-SPACE-003: 空き状況表示
**[State-driven]**
WHILE ユーザーがダッシュボードを表示中
THE システム SHALL 全スペースの状態をリアルタイムで集計し、タイプ別・フロア別の空き数を5秒間隔で更新表示する

### 2.2 入出庫処理

#### REQ-ENTRY-001: 入庫処理
**[Event-driven]**
WHEN 車両がエントリーゲートでナンバープレートを読み取られる
THE システム SHALL 車両情報を記録し、利用可能な最寄りスペースを案内し、入庫時刻をミリ秒精度で記録する

#### REQ-ENTRY-002: 出庫処理
**[Event-driven]**
WHEN 車両がエグジットゲートでナンバープレートを読み取られる
THE システム SHALL 入庫記録を検索し、駐車時間と料金を計算し、精算処理を開始する

#### REQ-ENTRY-003: 不正入庫防止
**[Unwanted]**
THE システム SHALL NOT 有効な入庫記録のない車両の出庫処理を許可する（エラーコードERR-NO-ENTRY-001を返却し、オペレーターに通知）

### 2.3 料金計算

#### REQ-FEE-001: 基本料金計算
**[Event-driven]**
WHEN 出庫処理が開始される
THE システム SHALL 入庫時刻から出庫時刻までの駐車時間を計算し、料金テーブル（最初の30分無料、以降30分ごとに200円、24時間最大2000円）に基づき料金を算出する

#### REQ-FEE-002: 料金割引適用
**[Optional]**
IF 提携店舗の認証済み割引コードが入力された場合
THEN THE システム SHALL 割引率（20%/50%/100%）を適用し、割引前金額・割引後金額をともに記録する

#### REQ-FEE-003: 料金上限適用
**[Ubiquitous]**
THE システム SHALL 24時間あたりの料金上限を超えないよう自動的に料金を調整し、上限適用時はその旨を明示する

### 2.4 精算処理

#### REQ-PAY-001: 現金精算
**[Event-driven]**
WHEN ユーザーが精算機で現金を投入する
THE システム SHALL 投入金額を計算し、料金以上であれば精算完了とし、おつりがある場合は排出する

#### REQ-PAY-002: キャッシュレス精算
**[Event-driven]**
WHEN ユーザーが精算機でICカード/QRコードをかざす
THE システム SHALL 決済ゲートウェイに認証要求を送信し、10秒以内に結果を取得し、成功時は精算完了とする

#### REQ-PAY-003: 事前精算
**[Optional]**
IF ユーザーが出庫前に事前精算機で精算を行った場合
THEN THE システム SHALL 精算完了フラグを立て、20分以内の出庫を許可し、超過時は追加料金を計算する

### 2.5 予約機能

#### REQ-RESERVE-001: スペース予約
**[Event-driven]**
WHEN ユーザーが予約フォームで日時と車種を指定して送信する
THE システム SHALL 指定条件に合う空きスペースを検索し、予約を確定し、スペース状態を「reserved」に変更する

#### REQ-RESERVE-002: 予約キャンセル
**[Event-driven]**
WHEN ユーザーが予約をキャンセルする
THE システム SHALL 予約開始時刻の1時間前までは無料キャンセルとし、それ以降は予約料金（500円）を請求し、スペース状態を「empty」に戻す

#### REQ-RESERVE-003: 予約時間超過
**[Event-driven]**
WHEN 予約開始時刻から30分経過しても入庫がない
THE システム SHALL 予約をキャンセルし、スペース状態を「empty」に変更し、ユーザーに通知を送信する

---

## 3. 非機能要件

### 3.1 パフォーマンス

#### REQ-NFR-001: センサー応答
**[Ubiquitous]**
THE システム SHALL IoTセンサーからのデータを100ミリ秒以内に処理し、データベースに反映する

#### REQ-NFR-002: 同時処理
**[Ubiquitous]**
THE システム SHALL 50台同時入出庫の負荷下でREQ-NFR-001の応答時間を維持する

### 3.2 信頼性

#### REQ-NFR-003: データ整合性
**[Ubiquitous]**
THE システム SHALL 入出庫記録と料金計算の整合性を保証し、システム障害時も記録を失わない

#### REQ-NFR-004: フェイルセーフ
**[Event-driven]**
WHEN システム障害が発生する
THE システム SHALL ゲートを開放モードに切り替え、オフライン記録を開始し、復旧後にデータを同期する

### 3.3 セキュリティ

#### REQ-NFR-005: 決済セキュリティ
**[Ubiquitous]**
THE システム SHALL 決済情報をPCI-DSS準拠の方式で処理し、カード情報を一切保存しない

#### REQ-NFR-006: アクセス制御
**[Unwanted]**
THE システム SHALL NOT 管理者権限なしでの料金テーブル・割引設定の変更を許可する

---

## 4. トレーサビリティマトリクス

| 要件ID | カテゴリ | EARSパターン | 優先度 | 測定可能性 |
|--------|----------|--------------|--------|------------|
| REQ-SPACE-001 | スペース管理 | Ubiquitous | P0 | ✅ |
| REQ-SPACE-002 | スペース管理 | Event-driven | P0 | ✅ |
| REQ-SPACE-003 | スペース管理 | State-driven | P0 | ✅ |
| REQ-ENTRY-001 | 入出庫 | Event-driven | P0 | ✅ |
| REQ-ENTRY-002 | 入出庫 | Event-driven | P0 | ✅ |
| REQ-ENTRY-003 | 入出庫 | Unwanted | P0 | ✅ |
| REQ-FEE-001 | 料金 | Event-driven | P0 | ✅ |
| REQ-FEE-002 | 料金 | Optional | P1 | ✅ |
| REQ-FEE-003 | 料金 | Ubiquitous | P0 | ✅ |
| REQ-PAY-001 | 精算 | Event-driven | P0 | ✅ |
| REQ-PAY-002 | 精算 | Event-driven | P0 | ✅ |
| REQ-PAY-003 | 精算 | Optional | P1 | ✅ |
| REQ-RESERVE-001 | 予約 | Event-driven | P1 | ✅ |
| REQ-RESERVE-002 | 予約 | Event-driven | P1 | ✅ |
| REQ-RESERVE-003 | 予約 | Event-driven | P1 | ✅ |
| REQ-NFR-001 | 非機能 | Ubiquitous | P0 | ✅ |
| REQ-NFR-002 | 非機能 | Ubiquitous | P0 | ✅ |
| REQ-NFR-003 | 非機能 | Ubiquitous | P0 | ✅ |
| REQ-NFR-004 | 非機能 | Event-driven | P1 | ✅ |
| REQ-NFR-005 | 非機能 | Ubiquitous | P0 | ✅ |
| REQ-NFR-006 | 非機能 | Unwanted | P0 | ✅ |
