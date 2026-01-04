# REQ-PET-001: ペット健康管理システム要件定義

## 1. プロジェクト概要

| 項目 | 内容 |
|------|------|
| プロジェクト名 | PetCare - ペット健康管理システム |
| ドメイン | veterinary（動物病院） |
| 目的 | ペットの健康記録、ワクチン接種管理、診療予約の一元管理 |
| ターゲット | ペットオーナー、動物病院スタッフ |

## 2. 機能要件（EARS形式）

### 2.1 ペット登録機能

#### REQ-PET-001-01: ペット基本情報登録
**Type**: Ubiquitous  
**Priority**: P0

> THE システム SHALL ペットの基本情報（名前、種類、品種、生年月日、体重、性別）を登録できること

**Acceptance Criteria**:
- [ ] 必須項目（名前、種類）が未入力の場合、エラーメッセージを表示
- [ ] 体重は0.1kg単位で記録可能
- [ ] 写真をアップロード可能（最大5MB）

#### REQ-PET-001-02: 複数ペット管理
**Type**: Ubiquitous  
**Priority**: P1

> THE システム SHALL 1人のオーナーに対して複数のペットを関連付けて管理できること

**Acceptance Criteria**:
- [ ] オーナーは無制限にペットを登録可能
- [ ] ペット一覧画面で全ペットを表示

### 2.2 健康記録機能

#### REQ-PET-001-03: 健康記録の登録
**Type**: Event-driven  
**Priority**: P0

> WHEN オーナーまたはスタッフが健康記録を入力する
> THE システム SHALL 日時、体重、体温、症状、メモを記録すること

**Acceptance Criteria**:
- [ ] 体温は35.0〜42.0°Cの範囲で入力可能
- [ ] 症状は選択式＋自由入力の両方をサポート
- [ ] 記録日時は自動で現在時刻を設定（手動変更可）

#### REQ-PET-001-04: 健康アラート
**Type**: State-driven  
**Priority**: P1

> WHILE ペットの体重が前回記録から10%以上変動している状態
> THE システム SHALL オーナーに健康アラートを通知すること

**Acceptance Criteria**:
- [ ] アラートはアプリ内通知とメールで送信
- [ ] アラート閾値はオーナーがカスタマイズ可能

### 2.3 ワクチン管理機能

#### REQ-PET-001-05: ワクチン接種記録
**Type**: Event-driven  
**Priority**: P0

> WHEN スタッフがワクチン接種を実施した
> THE システム SHALL ワクチン種類、接種日、次回予定日、ロット番号を記録すること

**Acceptance Criteria**:
- [ ] ワクチン種類はマスターデータから選択
- [ ] 次回予定日は自動計算（手動変更可）
- [ ] ロット番号は必須

#### REQ-PET-001-06: ワクチンリマインダー
**Type**: Event-driven  
**Priority**: P0

> WHEN 次回ワクチン接種予定日の14日前になった
> THE システム SHALL オーナーにリマインダー通知を送信すること

**Acceptance Criteria**:
- [ ] 通知は14日前、7日前、前日の3回
- [ ] 通知方法はアプリ内通知、メール、SMS（設定可）

### 2.4 診療予約機能

#### REQ-PET-001-07: 診療予約作成
**Type**: Event-driven  
**Priority**: P0

> WHEN オーナーが診療予約をリクエストした
> THE システム SHALL 希望日時、診療内容、ペット情報を含む予約を作成すること

**Acceptance Criteria**:
- [ ] 予約可能枠は動物病院が設定
- [ ] 同一時間帯の重複予約を防止
- [ ] 予約確定までのステータス：tentative → confirmed → active → completed

#### REQ-PET-001-08: 予約キャンセル
**Type**: Optional  
**Priority**: P1

> IF 予約日の24時間前まで
> THEN THE オーナー SHALL 予約をキャンセルできること

**Acceptance Criteria**:
- [ ] 24時間以内のキャンセルは動物病院への電話連絡が必要
- [ ] キャンセル理由の入力（任意）

### 2.5 非機能要件

#### REQ-PET-001-09: データプライバシー
**Type**: Unwanted  
**Priority**: P0

> THE システム SHALL NOT オーナーの許可なく健康記録を第三者に共有しないこと

**Acceptance Criteria**:
- [ ] 共有には明示的な同意が必要
- [ ] 共有ログを記録

#### REQ-PET-001-10: パフォーマンス
**Type**: Ubiquitous  
**Priority**: P1

> THE システム SHALL 全てのAPI応答を2秒以内に返すこと

## 3. オントロジーマッピング

| 概念 | エンティティ | 関係性 |
|------|------------|--------|
| Pet | Pet | BELONGS_TO Owner |
| Owner | Owner | OWNS Pet |
| HealthRecord | HealthRecord | RECORDED_FOR Pet |
| Vaccination | Vaccination | ADMINISTERED_TO Pet |
| Appointment | Appointment | SCHEDULED_FOR Pet |
| Clinic | VeterinaryClinic | PROVIDES Appointment |

## 4. トレーサビリティ

| 要件ID | 設計ID | タスクID | テストID |
|--------|--------|----------|----------|
| REQ-PET-001-01 | DES-PET-001 | TSK-PET-001 | TEST-PET-001 |
| REQ-PET-001-02 | DES-PET-001 | TSK-PET-002 | TEST-PET-002 |
| REQ-PET-001-03 | DES-PET-002 | TSK-PET-003 | TEST-PET-003 |
| REQ-PET-001-04 | DES-PET-002 | TSK-PET-004 | TEST-PET-004 |
| REQ-PET-001-05 | DES-PET-003 | TSK-PET-005 | TEST-PET-005 |
| REQ-PET-001-06 | DES-PET-003 | TSK-PET-006 | TEST-PET-006 |
| REQ-PET-001-07 | DES-PET-004 | TSK-PET-007 | TEST-PET-007 |
| REQ-PET-001-08 | DES-PET-004 | TSK-PET-008 | TEST-PET-008 |

---
**作成日**: 2026-01-04  
**バージョン**: 1.0  
**ステータス**: Draft
