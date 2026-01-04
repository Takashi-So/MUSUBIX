# REQ-COWORK-001: コワーキングスペース予約システム要件定義

## 1. プロジェクト概要

| 項目 | 内容 |
|------|------|
| プロジェクト名 | SpaceHub - コワーキングスペース予約システム |
| ドメイン | booking（予約）+ workspace |
| 目的 | コワーキングスペースの席・会議室予約、利用時間管理 |
| ターゲット | リモートワーカー、フリーランサー、スタートアップ |

## 2. 機能要件（EARS形式）

### 2.1 スペース管理機能

#### REQ-COWORK-001-01: スペース登録
**Type**: Ubiquitous  
**Priority**: P0

> THE システム SHALL スペース（デスク、会議室、電話ブース）の情報を登録・管理できること

**Acceptance Criteria**:
- [ ] スペースタイプ: desk（個人デスク）、meeting_room（会議室）、phone_booth（電話ブース）、lounge（ラウンジ）
- [ ] 各スペースに収容人数、設備情報、時間単価を設定可能
- [ ] スペースの有効/無効を切り替え可能

#### REQ-COWORK-001-02: スペース検索
**Type**: Event-driven  
**Priority**: P0

> WHEN ユーザーがスペースを検索する
> THE システム SHALL 条件（日時、タイプ、人数、設備）に合致する空きスペースを表示すること

**Acceptance Criteria**:
- [ ] 検索結果は空き状況でフィルタリング
- [ ] 設備（WiFi、モニター、ホワイトボード等）で絞り込み可能
- [ ] 人数要件を満たすスペースのみ表示

### 2.2 予約機能

#### REQ-COWORK-001-03: 予約作成
**Type**: Event-driven  
**Priority**: P0

> WHEN ユーザーがスペースを予約する
> THE システム SHALL 予約情報（スペース、開始時刻、終了時刻、人数）を記録すること

**Acceptance Criteria**:
- [ ] 予約は15分単位で設定可能
- [ ] 最小予約時間は30分、最大は8時間
- [ ] 予約ステータス: pending → confirmed → checked_in → completed

#### REQ-COWORK-001-04: 重複予約防止
**Type**: Unwanted  
**Priority**: P0

> THE システム SHALL NOT 同一スペースの同一時間帯に重複した予約を許可しないこと

**Acceptance Criteria**:
- [ ] 時間帯が1分でも重複する場合はエラー
- [ ] 直前の予約終了時刻から5分間のバッファを確保

#### REQ-COWORK-001-05: 予約変更
**Type**: Optional  
**Priority**: P1

> IF 予約開始の1時間前まで
> THEN THE ユーザー SHALL 予約の日時を変更できること

**Acceptance Criteria**:
- [ ] 変更先の空き確認を自動実施
- [ ] 変更履歴を記録

#### REQ-COWORK-001-06: 予約キャンセル
**Type**: Optional  
**Priority**: P0

> IF 予約開始の2時間前まで
> THEN THE ユーザー SHALL 予約をキャンセルできること（全額返金）

**Acceptance Criteria**:
- [ ] 2時間以内のキャンセルは50%返金
- [ ] キャンセル理由の入力（任意）

### 2.3 チェックイン・チェックアウト機能

#### REQ-COWORK-001-07: チェックイン
**Type**: Event-driven  
**Priority**: P0

> WHEN ユーザーが予約開始時刻の前後15分以内にチェックインする
> THE システム SHALL 予約ステータスを「利用中」に更新すること

**Acceptance Criteria**:
- [ ] QRコードまたはアプリでチェックイン
- [ ] 15分以上遅刻の場合は予約自動キャンセル（no_show）

#### REQ-COWORK-001-08: 自動チェックアウト
**Type**: Event-driven  
**Priority**: P1

> WHEN 予約終了時刻になった
> THE システム SHALL 自動的にチェックアウト処理を実行すること

**Acceptance Criteria**:
- [ ] 終了10分前に通知
- [ ] 延長オプションを提示（空きがある場合）

### 2.4 利用時間・課金機能

#### REQ-COWORK-001-09: 利用時間計算
**Type**: Event-driven  
**Priority**: P0

> WHEN チェックアウトが完了した
> THE システム SHALL 実際の利用時間と料金を計算すること

**Acceptance Criteria**:
- [ ] 料金は15分単位で計算
- [ ] 早期チェックアウトの場合も予約時間分を請求
- [ ] 延長利用は追加料金を自動計算

#### REQ-COWORK-001-10: 利用履歴
**Type**: Ubiquitous  
**Priority**: P1

> THE システム SHALL ユーザーの利用履歴（日時、スペース、利用時間、料金）を参照できること

## 3. 非機能要件

#### REQ-COWORK-001-11: 同時アクセス
**Type**: Ubiquitous  
**Priority**: P0

> THE システム SHALL 100人の同時予約リクエストを処理できること

#### REQ-COWORK-001-12: データ整合性
**Type**: Ubiquitous  
**Priority**: P0

> THE システム SHALL 予約の整合性を常に保証すること（ACID特性）

## 4. オントロジーマッピング

| 概念 | エンティティ | 関係性 |
|------|------------|--------|
| Space | Space | BELONGS_TO Location |
| Reservation | Reservation | RESERVES Space |
| User | User | MAKES Reservation |
| CheckIn | CheckInRecord | STARTS Reservation |
| Payment | PaymentRecord | CHARGES Reservation |

## 5. トレーサビリティ

| 要件ID | 設計ID | タスクID | テストID |
|--------|--------|----------|----------|
| REQ-COWORK-001-01 | DES-COWORK-001 | TSK-COWORK-001 | TEST-COWORK-001 |
| REQ-COWORK-001-02 | DES-COWORK-001 | TSK-COWORK-002 | TEST-COWORK-002 |
| REQ-COWORK-001-03 | DES-COWORK-002 | TSK-COWORK-003 | TEST-COWORK-003 |
| REQ-COWORK-001-04 | DES-COWORK-002 | TSK-COWORK-004 | TEST-COWORK-004 |
| REQ-COWORK-001-05 | DES-COWORK-002 | TSK-COWORK-005 | TEST-COWORK-005 |
| REQ-COWORK-001-06 | DES-COWORK-002 | TSK-COWORK-006 | TEST-COWORK-006 |
| REQ-COWORK-001-07 | DES-COWORK-003 | TSK-COWORK-007 | TEST-COWORK-007 |
| REQ-COWORK-001-08 | DES-COWORK-003 | TSK-COWORK-008 | TEST-COWORK-008 |
| REQ-COWORK-001-09 | DES-COWORK-004 | TSK-COWORK-009 | TEST-COWORK-009 |
| REQ-COWORK-001-10 | DES-COWORK-004 | TSK-COWORK-010 | TEST-COWORK-010 |

---
**作成日**: 2026-01-04  
**バージョン**: 1.0  
**ステータス**: Draft
