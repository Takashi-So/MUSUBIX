# REQ-CLINIC-001: Medical Clinic Appointment System Requirements

## Document Information

| Item | Value |
|------|-------|
| Document ID | REQ-CLINIC-001 |
| Version | 1.1.0 |
| Status | Approved |
| Author | AI Agent |
| Created | 2026-01-04 |

## 1. System Overview

Medical Clinic Appointment System（医療クリニック予約システム）は、小〜中規模の医療クリニック向けの予約・患者管理システムです。

### 1.1 Objectives

- 患者がオンラインで診察予約を行えるようにする
- 医師のスケジュールを効率的に管理する
- 患者の診察履歴・医療記録を安全に管理する
- 待ち時間の削減と患者満足度の向上

---

## 2. Functional Requirements

### 2.1 Patient Management (患者管理)

#### REQ-CLINIC-001-F001: Patient Registration
**EARS Pattern**: Ubiquitous

> THE system SHALL allow new patients to register with their personal information including name, date of birth, contact information, and insurance details.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 新規患者登録フォームの提供
- [ ] 必須項目の入力検証
- [ ] 重複登録の防止

#### REQ-CLINIC-001-F002: Patient Profile Management
**EARS Pattern**: Event-driven

> WHEN a patient updates their profile, THE system SHALL validate the changes and update the patient record within 1 second.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] プロフィール編集機能
- [ ] 変更履歴の記録
- [ ] 更新通知の送信

#### REQ-CLINIC-001-F003: Patient Medical History
**EARS Pattern**: Ubiquitous

> THE system SHALL maintain a complete medical history for each patient including past diagnoses, treatments, allergies, and medications.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 診察履歴の表示
- [ ] アレルギー情報の管理
- [ ] 服薬情報の管理

---

### 2.2 Appointment Management (予約管理)

#### REQ-CLINIC-001-F010: Appointment Booking
**EARS Pattern**: Event-driven

> WHEN a patient selects an available time slot, THE system SHALL create an appointment and send confirmation to both the patient and the assigned doctor.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 空き時間枠の表示
- [ ] 予約の確定処理
- [ ] 確認メール/SMS送信

#### REQ-CLINIC-001-F011: Appointment Cancellation
**EARS Pattern**: Optional

> IF a patient cancels an appointment at least 24 hours before the scheduled time, THEN THE system SHALL allow the cancellation without penalty and release the time slot.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] キャンセルポリシーの適用
- [ ] 時間枠の解放
- [ ] キャンセル通知の送信

#### REQ-CLINIC-001-F012: Appointment Rescheduling
**EARS Pattern**: Event-driven

> WHEN a patient requests to reschedule an appointment, THE system SHALL display available alternative time slots and allow the patient to select a new time.

**Priority**: P1 (Should)
**Acceptance Criteria**:
- [ ] 代替時間枠の提案
- [ ] 変更履歴の記録
- [ ] 変更通知の送信

#### REQ-CLINIC-001-F013: Appointment Reminder
**EARS Pattern**: State-driven

> WHILE an appointment is scheduled for the next 24 hours, THE system SHALL send reminder notifications to the patient at 24 hours and 2 hours before the appointment.

**Priority**: P1 (Should)
**Acceptance Criteria**:
- [ ] 24時間前リマインダー
- [ ] 2時間前リマインダー
- [ ] 通知設定のカスタマイズ

#### REQ-CLINIC-001-F014: Estimated Wait Time Display
**EARS Pattern**: State-driven

> WHILE a patient is checked in and waiting for consultation, THE system SHALL display the estimated wait time based on current queue position and average consultation duration.

**Priority**: P1 (Should)
**Acceptance Criteria**:
- [ ] リアルタイム待ち時間表示
- [ ] 順番待ち人数の表示
- [ ] 遅延時の自動更新

#### REQ-CLINIC-001-F015: No-Show Handling
**EARS Pattern**: Optional

> IF a patient does not appear within 15 minutes of the scheduled appointment time, THEN THE system SHALL mark the appointment as no-show, release the time slot, and record the incident in the patient's history.

**Priority**: P1 (Should)
**Acceptance Criteria**:
- [ ] 15分経過後の自動判定
- [ ] 時間枠の自動解放
- [ ] No-Show履歴の記録

---

### 2.3 Doctor Schedule Management (医師スケジュール管理)

#### REQ-CLINIC-001-F020: Doctor Availability Setup
**EARS Pattern**: Ubiquitous

> THE system SHALL allow doctors to define their available working hours for each day of the week.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 曜日ごとの勤務時間設定
- [ ] 休診日の設定
- [ ] 診察時間枠の長さ設定

#### REQ-CLINIC-001-F021: Doctor Schedule View
**EARS Pattern**: Ubiquitous

> THE system SHALL display a doctor's schedule showing all appointments, available slots, and blocked times.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 日/週/月表示切り替え
- [ ] 予約済み/空き/ブロックの色分け
- [ ] 予約詳細の表示

#### REQ-CLINIC-001-F022: Emergency Slot Blocking
**EARS Pattern**: Event-driven

> WHEN a doctor marks a time slot as blocked for emergency, THE system SHALL prevent new bookings for that slot and notify affected patients if any appointments exist.

**Priority**: P1 (Should)
**Acceptance Criteria**:
- [ ] 緊急ブロック機能
- [ ] 影響患者への通知
- [ ] 代替予約の提案

---

### 2.4 Medical Records (診察記録)

#### REQ-CLINIC-001-F030: Consultation Record Creation
**EARS Pattern**: Event-driven

> WHEN a doctor completes a consultation, THE system SHALL allow the doctor to create a consultation record including diagnosis, treatment plan, and prescriptions.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 診断内容の記録
- [ ] 治療計画の記録
- [ ] 処方箋の発行

#### REQ-CLINIC-001-F031: Prescription Management
**EARS Pattern**: Ubiquitous

> THE system SHALL generate digital prescriptions with medication details, dosage, and instructions.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 処方箋のデジタル発行
- [ ] 用量・用法の記載
- [ ] 薬局への送信機能

#### REQ-CLINIC-001-F032: Lab Test Ordering
**EARS Pattern**: Event-driven

> WHEN a doctor orders a lab test, THE system SHALL create a test order and notify the patient of preparation instructions.

**Priority**: P1 (Should)
**Acceptance Criteria**:
- [ ] 検査オーダーの作成
- [ ] 準備事項の通知
- [ ] 結果の記録・表示

---

### 2.5 Billing & Payment (請求・決済)

#### REQ-CLINIC-001-F040: Invoice Generation
**EARS Pattern**: Event-driven

> WHEN a consultation is completed, THE system SHALL generate an itemized invoice including consultation fee, procedures, and any additional charges.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] 明細付き請求書の生成
- [ ] 保険適用の計算
- [ ] 自己負担額の表示

#### REQ-CLINIC-001-F041: Payment Processing
**EARS Pattern**: Ubiquitous

> THE system SHALL accept payments via credit card, bank transfer, and cash.

**Priority**: P0 (Must)
**Acceptance Criteria**:
- [ ] クレジットカード決済
- [ ] 銀行振込対応
- [ ] 現金支払い記録

#### REQ-CLINIC-001-F042: Insurance Claim
**EARS Pattern**: Optional

> IF a patient has insurance coverage, THEN THE system SHALL generate insurance claim documents and track claim status.

**Priority**: P1 (Should)
**Acceptance Criteria**:
- [ ] 保険請求書の生成
- [ ] 請求ステータスの追跡
- [ ] 保険会社への電子送信

---

## 3. Non-Functional Requirements

### 3.1 Security (セキュリティ)

#### REQ-CLINIC-001-NF001: Data Encryption
**EARS Pattern**: Ubiquitous

> THE system SHALL encrypt all patient medical records using AES-256 encryption both at rest and in transit.

**Priority**: P0 (Must)

#### REQ-CLINIC-001-NF002: Access Control
**EARS Pattern**: Unwanted

> THE system SHALL NOT allow unauthorized users to access patient medical records.

**Priority**: P0 (Must)

#### REQ-CLINIC-001-NF003: Audit Logging
**EARS Pattern**: Ubiquitous

> THE system SHALL log all access to patient records with timestamp, user ID, and action performed.

**Priority**: P0 (Must)

---

### 3.2 Performance (パフォーマンス)

#### REQ-CLINIC-001-NF010: Response Time
**EARS Pattern**: Ubiquitous

> THE system SHALL respond to user interactions within 2 seconds under normal load.

**Priority**: P0 (Must)

#### REQ-CLINIC-001-NF011: Concurrent Users
**EARS Pattern**: Ubiquitous

> THE system SHALL support at least 100 concurrent users without performance degradation.

**Priority**: P1 (Should)

---

### 3.3 Availability (可用性)

#### REQ-CLINIC-001-NF020: System Uptime
**EARS Pattern**: Ubiquitous

> THE system SHALL maintain 99.5% uptime during clinic operating hours (8:00-20:00).

**Priority**: P0 (Must)

#### REQ-CLINIC-001-NF021: Data Backup
**EARS Pattern**: State-driven

> WHILE the system is operational, THE system SHALL perform automated backups every 6 hours.

**Priority**: P0 (Must)

---

## 4. Constraints

### 4.1 Regulatory Compliance

- 個人情報保護法への準拠
- 医療法に基づく記録保存要件（5年間）
- 電子処方箋の法的要件

### 4.2 Technical Constraints

- Node.js 20+ runtime
- PostgreSQL database
- HTTPS必須

---

## 5. Glossary

| Term | Definition |
|------|------------|
| Patient | 医療サービスを受ける患者 |
| Doctor | 診察を行う医師 |
| Appointment | 診察予約 |
| Consultation | 診察 |
| Prescription | 処方箋 |
| Medical Record | 診察記録 |

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2026-01-04 | AI Agent | Initial draft |
