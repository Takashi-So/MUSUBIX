# Requirements Document: Property Rental Management System
## REQ-RENTAL-001 v1.1.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 1.1.0 |
| **Status** | Approved |
| **Created** | 2026-01-04 |
| **Author** | MUSUBIX SDD System |
| **Domain** | Real Estate |

---

### 2. System Overview

#### 2.1 Purpose
不動産賃貸管理システム（Property Rental Management System）は、物件オーナー、不動産管理会社、および入居者（テナント）間の賃貸物件管理を効率化するためのシステムです。

#### 2.2 Scope
- 物件情報管理
- テナント（入居者）管理
- 賃貸契約管理
- 家賃・支払い管理
- メンテナンスリクエスト管理

#### 2.3 Stakeholders

| Stakeholder | Role | Interest |
|-------------|------|----------|
| **Property Owner** | 物件オーナー | 物件収益最大化、空室最小化 |
| **Property Manager** | 管理会社スタッフ | 効率的な物件・契約管理 |
| **Tenant** | 入居者 | 快適な住環境、簡易な手続き |
| **Maintenance Staff** | メンテナンススタッフ | メンテナンスリクエストの効率的処理 |

---

### 3. Functional Requirements (EARS Format)

#### 3.1 Property Management Requirements

##### REQ-RENTAL-001-F001: Property Registration
**Category**: Property Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a property manager creates a new property, **THE** system **SHALL** store property details including address, type, size, amenities, rent amount, and availability status with a unique property ID.

**Acceptance Criteria**:
1. Property ID format: `PROP-YYYYMMDD-NNN`
2. Required fields: address, property_type, size_sqm, monthly_rent, deposit
3. Optional fields: amenities, description, photos, floor_plan

---

##### REQ-RENTAL-001-F002: Property Search
**Category**: Property Management  
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a user searches for properties, **THE** system **SHALL** return matching properties based on criteria including location, price range, size, and amenities within 2 seconds.

**Search Criteria**:
- Location (area, city, prefecture)
- Monthly rent range (min-max)
- Size range (min-max sqm)
- Property type (apartment, house, condominium)
- Amenities (parking, pet-friendly, etc.)

---

##### REQ-RENTAL-001-F003: Property Availability Update
**Category**: Property Management
**Priority**: P0 (Must Have)  
**EARS Pattern**: State-driven

> **WHILE** a property is under lease contract, **THE** system **SHALL** mark the property as unavailable for new applications.

**Status Values**:
- `available`: 募集中
- `pending`: 申込中
- `occupied`: 入居中
- `maintenance`: メンテナンス中

---

#### 3.2 Tenant Management Requirements

##### REQ-RENTAL-001-F010: Tenant Registration
**Category**: Tenant Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a new tenant is registered, **THE** system **SHALL** store tenant information including name, contact details, identification documents, and employment information with a unique tenant ID.

**Tenant ID Format**: `TEN-YYYYMMDD-NNN`

**Required Fields**:
- Name (full name, furigana)
- Contact (phone, email, current address)
- Identification (ID type, ID number)
- Employment (employer, income verification)
- Emergency contact

---

##### REQ-RENTAL-001-F011: Tenant Application
**Category**: Tenant Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a tenant submits a rental application, **THE** system **SHALL** create an application record linking tenant and property, initiate screening process, and notify the property manager within 30 seconds.

**Application Status**:
- `submitted`: 提出済み
- `screening`: 審査中
- `approved`: 承認
- `rejected`: 却下
- `withdrawn`: 取り下げ

---

##### REQ-RENTAL-001-F012: Tenant Screening
**Category**: Tenant Management  
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** an application moves to screening status, **THE** system **SHALL** collect and verify income documentation, credit check consent, and guarantor information.

---

##### REQ-RENTAL-001-F013: Guarantor Management
**Category**: Tenant Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a tenant requires a guarantor, **THE** system **SHALL** store guarantor information including name, relationship, contact details, employment, and income verification with a unique guarantor ID.

**Guarantor ID Format**: `GUA-YYYYMMDD-NNN`

**Required Fields**:
- Name (full name, furigana)
- Relationship to tenant
- Contact (phone, email, address)
- Employment (employer, income)
- Consent documentation

---

#### 3.3 Lease Contract Management Requirements

##### REQ-RENTAL-001-F020: Contract Creation
**Category**: Contract Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a rental application is approved, **THE** system **SHALL** generate a lease contract document with terms including start date, end date, monthly rent, deposit amount, key money, and renewal conditions.

**Contract ID Format**: `LEASE-YYYYMMDD-NNN`

**Contract Fields**:
- Start date / End date
- Monthly rent (月額家賃)
- Deposit (敷金) - typically 1-2 months rent
- Key money (礼金) - typically 0-2 months rent
- Maintenance fee (管理費)
- Renewal fee (更新料)
- Special conditions

---

##### REQ-RENTAL-001-F021: Contract Renewal
**Category**: Contract Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** a lease contract is within 90 days of expiration, **THE** system **SHALL** notify both tenant and property manager, and provide options for renewal or termination.

---

##### REQ-RENTAL-001-F022: Contract Termination
**Category**: Contract Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a tenant or property manager initiates contract termination, **THE** system **SHALL** calculate final settlement including deposit return, outstanding rent, and any damage charges.

**Notice Period**: 30 days minimum

---

#### 3.4 Payment Management Requirements

##### REQ-RENTAL-001-F030: Rent Payment Recording
**Category**: Payment Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a rent payment is received, **THE** system **SHALL** record the payment with date, amount, payment method, and automatically update the tenant's payment history.

**Payment ID Format**: `PAY-YYYYMMDD-NNN`

---

##### REQ-RENTAL-001-F031: Payment Reminder
**Category**: Payment Management
**Priority**: P1 (Should Have)
**EARS Pattern**: State-driven

> **WHILE** a rent payment is overdue, **THE** system **SHALL** send reminders at 3 days, 7 days, and 14 days past due date to the tenant.

---

##### REQ-RENTAL-001-F032: Late Payment Fee
**Category**: Payment Management
**Priority**: P1 (Should Have)  
**EARS Pattern**: State-driven

> **WHILE** a rent payment remains overdue beyond the grace period, **THE** system **SHALL** calculate and apply late fees according to the contract terms.

**Default Late Fee**: 14.6% annual rate (standard legal maximum in Japan)

---

##### REQ-RENTAL-001-F033: Payment History
**Category**: Payment Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a tenant or property manager requests payment history, **THE** system **SHALL** display a chronological list of all payments including status, date, and amounts.

---

#### 3.5 Maintenance Request Management Requirements

##### REQ-RENTAL-001-F040: Maintenance Request Submission
**Category**: Maintenance Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a tenant submits a maintenance request, **THE** system **SHALL** create a ticket with description, urgency level, and photos, then notify the property manager immediately.

**Urgency Levels**:
- `emergency`: 緊急（水漏れ、ガス漏れ等）- 24時間以内対応
- `high`: 高（暖房/冷房故障等）- 48時間以内対応
- `medium`: 中（設備不具合）- 1週間以内対応
- `low`: 低（美観問題等）- 2週間以内対応

---

##### REQ-RENTAL-001-F041: Maintenance Status Update
**Category**: Maintenance Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a maintenance status changes, **THE** system **SHALL** update the ticket status and notify the tenant of the change.

**Status Values**:
- `submitted`: 提出済み
- `assigned`: 担当者割当済み
- `scheduled`: 作業日程確定
- `in_progress`: 作業中
- `completed`: 完了
- `closed`: クローズ

---

##### REQ-RENTAL-001-F042: Maintenance Cost Assignment
**Category**: Maintenance Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** maintenance work is completed, **THE** system **SHALL** assign cost responsibility (owner or tenant) based on issue type and lease terms.

---

#### 3.6 Reporting Requirements

##### REQ-RENTAL-001-F050: Owner Revenue Report
**Category**: Reporting
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** a property owner requests a revenue report, **THE** system **SHALL** generate a summary including rental income, maintenance costs, vacancy periods, and net profit for the specified period.

**Report Contents**:
- Gross rental income
- Maintenance expenses
- Management fees
- Vacancy loss calculation
- Net operating income
- Year-over-year comparison

---

##### REQ-RENTAL-001-F051: Occupancy Report
**Category**: Reporting
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** a property manager requests an occupancy report, **THE** system **SHALL** display current and historical occupancy rates across all managed properties.

---

### 4. Non-Functional Requirements

#### 4.1 Performance Requirements

##### REQ-RENTAL-001-NF001: Response Time
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** respond to all user queries within 2 seconds under normal load conditions.

---

##### REQ-RENTAL-001-NF002: Concurrent Users
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** support at least 100 concurrent users without performance degradation.

---

#### 4.2 Security Requirements

##### REQ-RENTAL-001-NF010: Authentication
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** require authentication for all operations except public property search.

---

##### REQ-RENTAL-001-NF011: Data Encryption
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** encrypt all personal information at rest and in transit using AES-256 and TLS 1.3.

---

##### REQ-RENTAL-001-NF012: Personal Information Protection
**EARS Pattern**: Unwanted

> **THE** system **SHALL NOT** expose tenant personal information (ID numbers, financial data) to unauthorized users.

---

#### 4.3 Availability Requirements

##### REQ-RENTAL-001-NF020: System Availability
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** maintain 99.5% availability during business hours (8:00-22:00 JST).

---

#### 4.4 Compliance Requirements

##### REQ-RENTAL-001-NF030: Legal Compliance
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** comply with Japanese Personal Information Protection Act (個人情報保護法) and Real Estate Transaction Act (宅地建物取引業法).

---

#### 4.5 Audit Requirements

##### REQ-RENTAL-001-NF040: Audit Logging
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** maintain audit logs of all data modifications including user ID, timestamp, action type, and before/after values for a minimum of 7 years.

---

##### REQ-RENTAL-001-NF041: Audit Trail Access
**EARS Pattern**: Event-driven

> **WHEN** an administrator requests audit trail data, **THE** system **SHALL** provide searchable access to historical records with appropriate access controls.

---

### 5. Constraints

| ID | Category | Constraint |
|----|----------|------------|
| CON-001 | Technology | TypeScript + Node.js runtime |
| CON-002 | Database | PostgreSQL for persistence |
| CON-003 | Architecture | Microservices pattern |
| CON-004 | Compliance | Japanese real estate regulations |
| CON-005 | Language | Japanese language support required |

---

### 6. Dependencies

| ID | Dependency | Type |
|----|------------|------|
| DEP-001 | Authentication service | External |
| DEP-002 | Email notification service | External |
| DEP-003 | Payment gateway integration | External |
| DEP-004 | Document storage service | External |

---

### 7. Assumptions

1. All users have internet access
2. Property data is provided in Japanese format
3. Currency is Japanese Yen (JPY)
4. Date/time follows JST timezone
5. Standard Japanese lease terms apply

---

### 8. Glossary

| Term | Definition |
|------|------------|
| **Property** | 賃貸物件（アパート、マンション、一戸建て等） |
| **Tenant** | 入居者・借主 |
| **Property Owner** | 物件オーナー・大家 |
| **Lease** | 賃貸借契約 |
| **Deposit** | 敷金 |
| **Key Money** | 礼金 |
| **Monthly Rent** | 月額家賃 |
| **Maintenance Fee** | 管理費・共益費 |

---

### 9. Requirements Traceability

| Requirement ID | Category | Priority | Status |
|---------------|----------|----------|--------|
| REQ-RENTAL-001-F001 | Property | P0 | Approved |
| REQ-RENTAL-001-F002 | Property | P0 | Approved |
| REQ-RENTAL-001-F003 | Property | P0 | Approved |
| REQ-RENTAL-001-F010 | Tenant | P0 | Approved |
| REQ-RENTAL-001-F011 | Tenant | P0 | Approved |
| REQ-RENTAL-001-F012 | Tenant | P1 | Approved |
| REQ-RENTAL-001-F013 | Tenant | P0 | Approved |
| REQ-RENTAL-001-F020 | Contract | P0 | Approved |
| REQ-RENTAL-001-F021 | Contract | P1 | Approved |
| REQ-RENTAL-001-F022 | Contract | P0 | Approved |
| REQ-RENTAL-001-F030 | Payment | P0 | Approved |
| REQ-RENTAL-001-F031 | Payment | P1 | Approved |
| REQ-RENTAL-001-F032 | Payment | P1 | Approved |
| REQ-RENTAL-001-F033 | Payment | P0 | Approved |
| REQ-RENTAL-001-F040 | Maintenance | P0 | Approved |
| REQ-RENTAL-001-F041 | Maintenance | P0 | Approved |
| REQ-RENTAL-001-F042 | Maintenance | P1 | Approved |
| REQ-RENTAL-001-F050 | Reporting | P1 | Approved |
| REQ-RENTAL-001-F051 | Reporting | P1 | Approved |
| REQ-RENTAL-001-NF040 | Audit | P0 | Approved |
| REQ-RENTAL-001-NF041 | Audit | P1 | Approved |

---

### 10. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-04 | MUSUBIX SDD | Initial requirements document |
| 1.1.0 | 2026-01-04 | MUSUBIX SDD | Added F013 (Guarantor), F050-F051 (Reporting), NF040-NF041 (Audit); Added key_money to F020; Added Tenant ID format |

---

**Document Status**: ✅ Approved

**Approval Required**: [x] Product Owner [x] Technical Lead [x] Legal Compliance
