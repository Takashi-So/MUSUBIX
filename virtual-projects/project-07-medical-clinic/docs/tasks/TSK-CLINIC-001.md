# TSK-CLINIC-001: Implementation Tasks

## Document Information

| Item | Value |
|------|-------|
| Document ID | TSK-CLINIC-001 |
| Version | 1.0.0 |
| Design Reference | DES-CLINIC-001 |
| Created | 2026-01-04 |

---

## Task Summary

| Sprint | Tasks | Story Points |
|--------|-------|--------------|
| Sprint 1 | TSK-001〜004 | 13 |
| Sprint 2 | TSK-005〜008 | 13 |
| Sprint 3 | TSK-009〜012 | 13 |

---

## Sprint 1: Core Infrastructure

### TSK-CLINIC-001-001: Project Setup
**Story Points**: 3

**Description**: プロジェクト基盤のセットアップ

**Acceptance Criteria**:
- [ ] TypeScript + Node.js プロジェクト構成
- [ ] ESLint + Prettier 設定
- [ ] Vitest テスト環境
- [ ] Docker Compose 環境

**Traceability**: 全要件の基盤

---

### TSK-CLINIC-001-002: Patient Entity & Repository
**Story Points**: 3

**Description**: 患者エンティティとリポジトリの実装

**Acceptance Criteria**:
- [ ] Patient エンティティ定義
- [ ] IPatientRepository インターフェース
- [ ] PostgresPatientRepository 実装
- [ ] 単体テスト（90%カバレッジ）

**Traceability**: REQ-CLINIC-001-F001, F002, F003

---

### TSK-CLINIC-001-003: PatientService Implementation
**Story Points**: 5

**Description**: 患者サービスのビジネスロジック実装

**Acceptance Criteria**:
- [ ] registerPatient() - 新規登録
- [ ] getPatient() - 情報取得
- [ ] updatePatient() - 情報更新
- [ ] getMedicalHistory() - 履歴取得
- [ ] 単体テスト（90%カバレッジ）

**Traceability**: REQ-CLINIC-001-F001, F002, F003

---

### TSK-CLINIC-001-004: Patient API Endpoints
**Story Points**: 2

**Description**: 患者APIエンドポイントの実装

**Acceptance Criteria**:
- [ ] POST /api/patients
- [ ] GET /api/patients/:id
- [ ] PUT /api/patients/:id
- [ ] GET /api/patients/:id/history
- [ ] 統合テスト

**Traceability**: REQ-CLINIC-001-F001, F002, F003

---

## Sprint 2: Appointment Management

### TSK-CLINIC-001-005: Doctor & Schedule Entities
**Story Points**: 3

**Description**: 医師とスケジュールエンティティの実装

**Acceptance Criteria**:
- [ ] Doctor エンティティ定義
- [ ] DoctorSchedule エンティティ定義
- [ ] TimeSlot 値オブジェクト
- [ ] 単体テスト

**Traceability**: REQ-CLINIC-001-F020, F021

---

### TSK-CLINIC-001-006: Appointment Entity & Repository
**Story Points**: 3

**Description**: 予約エンティティとリポジトリの実装

**Acceptance Criteria**:
- [ ] Appointment エンティティ定義
- [ ] IAppointmentRepository インターフェース
- [ ] PostgresAppointmentRepository 実装
- [ ] 単体テスト（90%カバレッジ）

**Traceability**: REQ-CLINIC-001-F010, F011, F012

---

### TSK-CLINIC-001-007: AppointmentService Implementation
**Story Points**: 5

**Description**: 予約サービスのビジネスロジック実装

**Acceptance Criteria**:
- [ ] getAvailableSlots() - 空き取得
- [ ] bookAppointment() - 予約作成
- [ ] cancelAppointment() - キャンセル
- [ ] rescheduleAppointment() - 変更
- [ ] checkIn() - チェックイン
- [ ] handleNoShow() - No-Show処理
- [ ] 単体テスト（90%カバレッジ）

**Traceability**: REQ-CLINIC-001-F010〜F015

---

### TSK-CLINIC-001-008: Appointment API Endpoints
**Story Points**: 2

**Description**: 予約APIエンドポイントの実装

**Acceptance Criteria**:
- [ ] GET /api/appointments/slots
- [ ] POST /api/appointments
- [ ] PUT /api/appointments/:id
- [ ] DELETE /api/appointments/:id
- [ ] POST /api/appointments/:id/checkin
- [ ] 統合テスト

**Traceability**: REQ-CLINIC-001-F010〜F015

---

## Sprint 3: Billing & Integration

### TSK-CLINIC-001-009: Invoice Entity & Service
**Story Points**: 3

**Description**: 請求エンティティとサービスの実装

**Acceptance Criteria**:
- [ ] Invoice エンティティ定義
- [ ] InvoiceItem 値オブジェクト
- [ ] InvoiceService 実装
- [ ] 単体テスト

**Traceability**: REQ-CLINIC-001-F040

---

### TSK-CLINIC-001-010: Payment Integration
**Story Points**: 5

**Description**: 決済連携の実装

**Acceptance Criteria**:
- [ ] IPaymentGatewayAdapter インターフェース
- [ ] StripePaymentAdapter 実装（モック可）
- [ ] PaymentService 実装
- [ ] 単体テスト

**Traceability**: REQ-CLINIC-001-F041

---

### TSK-CLINIC-001-011: Notification Service
**Story Points**: 3

**Description**: 通知サービスの実装

**Acceptance Criteria**:
- [ ] INotificationAdapter インターフェース
- [ ] EmailNotificationAdapter 実装
- [ ] SMSNotificationAdapter 実装
- [ ] ReminderService 実装
- [ ] 単体テスト

**Traceability**: REQ-CLINIC-001-F013

---

### TSK-CLINIC-001-012: End-to-End Testing
**Story Points**: 2

**Description**: E2Eテストと統合確認

**Acceptance Criteria**:
- [ ] 患者登録〜予約〜診察〜請求フロー
- [ ] 予約キャンセル・変更フロー
- [ ] 全API統合テスト
- [ ] カバレッジ80%以上

**Traceability**: 全要件

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2026-01-04 | AI Agent | Initial task breakdown |
