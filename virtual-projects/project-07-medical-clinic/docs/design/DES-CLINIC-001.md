# DES-CLINIC-001: Medical Clinic System Design

## Document Information

| Item | Value |
|------|-------|
| Document ID | DES-CLINIC-001 |
| Version | 1.0.0 |
| Status | Draft |
| Author | AI Agent |
| Created | 2026-01-04 |
| Requirements | REQ-CLINIC-001 v1.1.0 |

---

## 1. C4 Model - Context Diagram

### 1.1 System Context

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           External Systems                               │
│                                                                          │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐                │
│  │   Patient    │   │   Doctor     │   │   Admin      │                │
│  │   (Web/App)  │   │   (Desktop)  │   │   (Desktop)  │                │
│  └──────┬───────┘   └──────┬───────┘   └──────┬───────┘                │
│         │                  │                  │                         │
│         │                  │                  │                         │
│         ▼                  ▼                  ▼                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                                                                  │   │
│  │              Medical Clinic Appointment System                   │   │
│  │                                                                  │   │
│  │  - Patient registration & management                            │   │
│  │  - Appointment booking & scheduling                             │   │
│  │  - Medical records management                                   │   │
│  │  - Billing & payment processing                                 │   │
│  │                                                                  │   │
│  └─────────────────────────┬───────────────────────────────────────┘   │
│                            │                                            │
│         ┌──────────────────┼──────────────────┐                        │
│         ▼                  ▼                  ▼                        │
│  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐               │
│  │   Payment    │   │   Email/SMS  │   │  Insurance   │               │
│  │   Gateway    │   │   Provider   │   │   Provider   │               │
│  └──────────────┘   └──────────────┘   └──────────────┘               │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 1.2 Actors

| Actor | Description | Primary Use Cases |
|-------|-------------|-------------------|
| Patient | 診察を受ける患者 | 予約管理、診察履歴閲覧 |
| Doctor | 診察を行う医師 | スケジュール管理、診察記録 |
| Admin | クリニック管理者 | システム設定、レポート |

---

## 2. C4 Model - Container Diagram

### 2.1 System Containers

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     Medical Clinic System                                │
│                                                                          │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                    Web Application (React)                      │    │
│  │  - Patient Portal                                              │    │
│  │  - Doctor Dashboard                                            │    │
│  │  - Admin Console                                               │    │
│  └────────────────────────────────┬───────────────────────────────┘    │
│                                   │ HTTPS/REST                         │
│                                   ▼                                    │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │                    API Gateway (Node.js)                        │    │
│  │  - Authentication                                               │    │
│  │  - Rate Limiting                                                │    │
│  │  - Request Routing                                              │    │
│  └─────────────┬──────────────────┬──────────────────┬────────────┘    │
│                │                  │                  │                 │
│                ▼                  ▼                  ▼                 │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐        │
│  │  Patient        │  │  Appointment    │  │  Billing        │        │
│  │  Service        │  │  Service        │  │  Service        │        │
│  │  (Node.js)      │  │  (Node.js)      │  │  (Node.js)      │        │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘        │
│           │                    │                    │                  │
│           │                    │                    │                  │
│           ▼                    ▼                    ▼                  │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                    PostgreSQL Database                          │   │
│  │  - Patients, Doctors, Appointments, Medical Records, Billing    │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Container Details

| Container | Technology | Purpose | Ports |
|-----------|------------|---------|-------|
| Web Application | React + TypeScript | フロントエンドUI | 3000 |
| API Gateway | Node.js + Express | APIルーティング・認証 | 8080 |
| Patient Service | Node.js + TypeScript | 患者管理ドメイン | 8081 |
| Appointment Service | Node.js + TypeScript | 予約管理ドメイン | 8082 |
| Billing Service | Node.js + TypeScript | 請求・決済ドメイン | 8083 |
| Database | PostgreSQL 15 | データ永続化 | 5432 |

---

## 3. C4 Model - Component Diagram

### 3.1 Patient Service Components

```
┌──────────────────────────────────────────────────────────────────┐
│                     Patient Service                               │
│                                                                   │
│  ┌──────────────────┐   ┌──────────────────┐                    │
│  │  PatientRouter   │   │  PatientController│                    │
│  │  /api/patients/* │──▶│  HTTP Handler     │                    │
│  └──────────────────┘   └────────┬──────────┘                    │
│                                  │                                │
│                                  ▼                                │
│  ┌──────────────────────────────────────────────────────────────┐│
│  │                    PatientService                            ││
│  │  - registerPatient(data): Patient                            ││
│  │  - getPatient(id): Patient                                   ││
│  │  - updatePatient(id, data): Patient                          ││
│  │  - getMedicalHistory(patientId): MedicalHistory[]            ││
│  └────────────────────────────┬─────────────────────────────────┘│
│                               │                                  │
│                               ▼                                  │
│  ┌──────────────────┐   ┌──────────────────┐                    │
│  │ PatientRepository│   │ MedicalHistory   │                    │
│  │ - CRUD operations│   │ Repository       │                    │
│  └────────┬─────────┘   └────────┬─────────┘                    │
│           │                      │                               │
│           └──────────┬───────────┘                               │
│                      ▼                                           │
│           ┌─────────────────────┐                                │
│           │   PostgreSQL        │                                │
│           │   patients table    │                                │
│           │   medical_history   │                                │
│           └─────────────────────┘                                │
└──────────────────────────────────────────────────────────────────┘
```

### 3.2 Appointment Service Components

```
┌──────────────────────────────────────────────────────────────────┐
│                   Appointment Service                             │
│                                                                   │
│  ┌────────────────────┐   ┌────────────────────┐                │
│  │ AppointmentRouter  │   │ AppointmentController│               │
│  │ /api/appointments/*│──▶│ HTTP Handler        │                │
│  └────────────────────┘   └──────────┬──────────┘                │
│                                      │                            │
│     ┌────────────────────────────────┼────────────────┐          │
│     │                                │                │          │
│     ▼                                ▼                ▼          │
│  ┌───────────────┐   ┌───────────────────┐  ┌────────────────┐  │
│  │ScheduleService│   │ AppointmentService │  │ ReminderService │  │
│  │- getAvailable │   │ - book()          │  │ - schedule()    │  │
│  │- blockSlot()  │   │ - cancel()        │  │ - send()        │  │
│  └───────┬───────┘   │ - reschedule()    │  └────────┬───────┘  │
│          │           └─────────┬─────────┘           │          │
│          │                     │                     │          │
│          ▼                     ▼                     ▼          │
│  ┌────────────────┐  ┌────────────────────┐  ┌──────────────┐   │
│  │ DoctorSchedule │  │ Appointment        │  │ Notification │   │
│  │ Repository     │  │ Repository         │  │ Adapter      │   │
│  └────────┬───────┘  └─────────┬──────────┘  └──────┬───────┘   │
│           │                    │                    │           │
│           └────────────────────┼────────────────────┘           │
│                                ▼                                 │
│           ┌───────────────────────────────────────┐              │
│           │   PostgreSQL                          │              │
│           │   - doctor_schedules                  │              │
│           │   - appointments                      │              │
│           │   - time_slots                        │              │
│           └───────────────────────────────────────┘              │
└──────────────────────────────────────────────────────────────────┘
```

### 3.3 Billing Service Components

```
┌──────────────────────────────────────────────────────────────────┐
│                     Billing Service                               │
│                                                                   │
│  ┌──────────────────┐   ┌──────────────────┐                    │
│  │  BillingRouter   │   │  BillingController│                    │
│  │  /api/billing/*  │──▶│  HTTP Handler     │                    │
│  └──────────────────┘   └────────┬──────────┘                    │
│                                  │                                │
│           ┌──────────────────────┼──────────────────┐            │
│           │                      │                  │            │
│           ▼                      ▼                  ▼            │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐     │
│  │ InvoiceService │  │ PaymentService │  │ InsuranceService│     │
│  │ - generate()   │  │ - process()    │  │ - submitClaim() │     │
│  │ - getByPatient │  │ - refund()     │  │ - checkStatus() │     │
│  └───────┬────────┘  └───────┬────────┘  └───────┬────────┘     │
│          │                   │                   │               │
│          ▼                   ▼                   ▼               │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐     │
│  │ Invoice        │  │ Payment        │  │ InsuranceClaim │     │
│  │ Repository     │  │ Gateway        │  │ Adapter        │     │
│  └────────────────┘  │ (Stripe/etc)   │  └────────────────┘     │
│                      └────────────────┘                          │
└──────────────────────────────────────────────────────────────────┘
```

---

## 4. Data Model

### 4.1 Entity Relationship Diagram

```
┌─────────────┐       ┌─────────────────┐       ┌─────────────┐
│   Patient   │       │   Appointment   │       │   Doctor    │
├─────────────┤       ├─────────────────┤       ├─────────────┤
│ id (PK)     │──────▶│ patient_id (FK) │       │ id (PK)     │
│ name        │       │ doctor_id (FK)  │◀──────│ name        │
│ email       │       │ date_time       │       │ specialty   │
│ phone       │       │ duration        │       │ license_no  │
│ dob         │       │ status          │       │ department  │
│ insurance_id│       │ type            │       │ email       │
│ created_at  │       │ notes           │       │ phone       │
└─────────────┘       │ created_at      │       └─────────────┘
      │               └─────────────────┘              │
      │                       │                        │
      │                       │                        │
      ▼                       ▼                        ▼
┌─────────────────┐   ┌─────────────────┐   ┌─────────────────┐
│ MedicalHistory  │   │ Consultation    │   │ DoctorSchedule  │
├─────────────────┤   ├─────────────────┤   ├─────────────────┤
│ id (PK)         │   │ id (PK)         │   │ id (PK)         │
│ patient_id (FK) │   │ appointment_id  │   │ doctor_id (FK)  │
│ diagnosis       │   │ diagnosis       │   │ day_of_week     │
│ treatment       │   │ treatment_plan  │   │ start_time      │
│ date            │   │ prescription    │   │ end_time        │
│ doctor_id       │   │ notes           │   │ slot_duration   │
└─────────────────┘   │ created_at      │   │ is_active       │
                      └─────────────────┘   └─────────────────┘
```

### 4.2 Core Entities

#### Patient
```typescript
interface Patient {
  id: string;              // UUID
  name: string;
  email: string;
  phone: string;
  dateOfBirth: Date;
  insuranceId?: string;
  allergies: string[];
  medications: string[];
  createdAt: Date;
  updatedAt: Date;
}
```

#### Doctor
```typescript
interface Doctor {
  id: string;              // UUID
  name: string;
  specialty: string;
  licenseNumber: string;
  department: string;
  email: string;
  phone: string;
  isActive: boolean;
  createdAt: Date;
}
```

#### Appointment
```typescript
interface Appointment {
  id: string;              // UUID
  patientId: string;
  doctorId: string;
  dateTime: Date;
  duration: number;        // minutes
  status: AppointmentStatus;
  type: AppointmentType;
  notes?: string;
  createdAt: Date;
  updatedAt: Date;
}

type AppointmentStatus = 
  | 'scheduled'
  | 'confirmed'
  | 'checked_in'
  | 'in_progress'
  | 'completed'
  | 'cancelled'
  | 'no_show';

type AppointmentType = 
  | 'initial'
  | 'follow_up'
  | 'emergency'
  | 'routine';
```

---

## 5. Design Patterns Applied

### 5.1 Repository Pattern
**Traceability**: REQ-CLINIC-001-F001, F002, F003

各エンティティに対してRepositoryを実装し、データアクセスを抽象化。

```typescript
interface IPatientRepository {
  findById(id: string): Promise<Patient | null>;
  findByEmail(email: string): Promise<Patient | null>;
  create(data: CreatePatientDTO): Promise<Patient>;
  update(id: string, data: UpdatePatientDTO): Promise<Patient>;
  delete(id: string): Promise<void>;
}
```

### 5.2 Service Layer Pattern
**Traceability**: REQ-CLINIC-001-F010, F011, F012

ビジネスロジックをServiceクラスに集約。

### 5.3 Adapter Pattern
**Traceability**: REQ-CLINIC-001-F041, F042

外部システム連携（Payment Gateway, Insurance Provider）をAdapterで抽象化。

```typescript
interface IPaymentGatewayAdapter {
  processPayment(request: PaymentRequest): Promise<PaymentResult>;
  refund(transactionId: string): Promise<RefundResult>;
}

interface INotificationAdapter {
  sendEmail(to: string, template: string, data: object): Promise<void>;
  sendSMS(to: string, message: string): Promise<void>;
}
```

### 5.4 Factory Pattern
**Traceability**: REQ-CLINIC-001-F040

Invoice生成をFactoryで実装。

---

## 6. API Design

### 6.1 Patient API

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| POST | /api/patients | 患者登録 | Admin |
| GET | /api/patients/:id | 患者情報取得 | Patient/Doctor |
| PUT | /api/patients/:id | 患者情報更新 | Patient/Admin |
| GET | /api/patients/:id/history | 診察履歴取得 | Patient/Doctor |

### 6.2 Appointment API

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| GET | /api/appointments/slots | 空き時間取得 | Patient |
| POST | /api/appointments | 予約作成 | Patient |
| PUT | /api/appointments/:id | 予約変更 | Patient |
| DELETE | /api/appointments/:id | 予約キャンセル | Patient |
| POST | /api/appointments/:id/checkin | チェックイン | Staff |

### 6.3 Billing API

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| GET | /api/billing/invoices | 請求一覧 | Patient/Admin |
| POST | /api/billing/invoices | 請求作成 | Doctor/Admin |
| POST | /api/billing/payments | 決済処理 | Patient |

---

## 7. Security Design

### 7.1 Authentication
- JWT-based authentication
- OAuth 2.0 for external integrations
- Session timeout: 30 minutes

### 7.2 Authorization (RBAC)
| Role | Permissions |
|------|-------------|
| Patient | Read own data, Create/Cancel appointments |
| Doctor | Read patients, Create consultations, View schedule |
| Admin | Full access |

### 7.3 Data Protection
- AES-256 encryption for medical records
- TLS 1.3 for data in transit
- Field-level encryption for sensitive data (SSN, etc.)

---

## 8. Traceability Matrix

| Requirement ID | Component | Service | Status |
|----------------|-----------|---------|--------|
| REQ-CLINIC-001-F001 | PatientController | PatientService | ✅ |
| REQ-CLINIC-001-F002 | PatientController | PatientService | ✅ |
| REQ-CLINIC-001-F003 | MedicalHistoryRepository | PatientService | ✅ |
| REQ-CLINIC-001-F010 | AppointmentController | AppointmentService | ✅ |
| REQ-CLINIC-001-F011 | AppointmentController | AppointmentService | ✅ |
| REQ-CLINIC-001-F012 | AppointmentController | AppointmentService | ✅ |
| REQ-CLINIC-001-F013 | ReminderService | NotificationAdapter | ✅ |
| REQ-CLINIC-001-F014 | QueueService | AppointmentService | ✅ |
| REQ-CLINIC-001-F015 | NoShowHandler | AppointmentService | ✅ |
| REQ-CLINIC-001-F020 | ScheduleController | ScheduleService | ✅ |
| REQ-CLINIC-001-F021 | ScheduleController | ScheduleService | ✅ |
| REQ-CLINIC-001-F022 | ScheduleController | ScheduleService | ✅ |
| REQ-CLINIC-001-F030 | ConsultationController | ConsultationService | ✅ |
| REQ-CLINIC-001-F031 | PrescriptionController | PrescriptionService | ✅ |
| REQ-CLINIC-001-F040 | InvoiceController | InvoiceService | ✅ |
| REQ-CLINIC-001-F041 | PaymentController | PaymentService | ✅ |

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2026-01-04 | AI Agent | Initial draft |
