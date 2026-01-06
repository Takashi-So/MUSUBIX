# Requirements Document: Property Rental Management System
## REQ-RENTAL-001 v2.0.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 2.0.0 |
| **Status** | Draft |
| **Created** | 2026-01-06 |
| **Author** | MUSUBIX SDD System |
| **Domain** | Real Estate |
| **SDD Compliance** | Full (Constitution Articles I-IX) |
| **YATA Integration** | Auto-learning enabled |

---

### 2. System Overview

#### 2.1 Purpose

Property Rental Management System（PRMS）は、不動産賃貸業務を効率化するためのシステムです。
物件オーナー、管理会社、入居者間の賃貸プロセスをデジタル化し、透明性と効率性を向上させます。

#### 2.2 Core Domain Model

```
Property ─── LeaseContract ─── Tenant
    │              │
    │              └─── Payment
    │
    └─── MaintenanceRequest ─── Tenant
```

#### 2.3 Stakeholders

| Stakeholder | Role | Primary Goal |
|-------------|------|--------------|
| PropertyOwner | 物件オーナー | 収益最大化、空室最小化 |
| PropertyManager | 管理会社 | 効率的な物件・契約管理 |
| Tenant | 入居者 | 快適な住環境、簡易手続き |
| MaintenanceStaff | メンテナンス担当 | 作業の効率的処理 |

---

### 3. Functional Requirements (EARS Format)

---

## 3.1 Property Management

### REQ-RENTAL-001-F001: Property Registration
**Category**: Property Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Event-driven

> **WHEN** a property manager registers a new property,  
> **THE** system **SHALL** create a property record with a unique ID (format: `PROP-YYYYMMDD-NNN`), storing address, property type, size (sqm), monthly rent, and deposit amount.

**Acceptance Criteria**:
- AC1: Property ID is auto-generated in format `PROP-YYYYMMDD-NNN`
- AC2: Required fields validation: address, propertyType, sizeSqm, monthlyRent, deposit
- AC3: Optional fields accepted: amenities[], description, photos[]
- AC4: Created property has status `available` by default

**Traceability**: DES-RENTAL-001-C001, TSK-RENTAL-001-001

---

### REQ-RENTAL-001-F002: Property Status Transition
**Category**: Property Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: State-driven

> **WHILE** a property exists in the system,  
> **THE** system **SHALL** enforce valid status transitions: `available` → `pending` | `maintenance`, `pending` → `occupied` | `available`, `occupied` → `available` | `maintenance`, `maintenance` → `available`.

**Status Transition Map**:
```
available    → [pending, maintenance]
pending      → [occupied, available]
occupied     → [available, maintenance]
maintenance  → [available]
```

**Acceptance Criteria**:
- AC1: Invalid transitions are rejected with error
- AC2: Status change records timestamp and reason

**Traceability**: DES-RENTAL-001-C001, TSK-RENTAL-001-002

---

### REQ-RENTAL-001-F003: Property Search
**Category**: Property Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Event-driven

> **WHEN** a user searches for properties with filter criteria,  
> **THE** system **SHALL** return all matching properties within 2 seconds, supporting filters for location, price range, size range, property type, and amenities.

**Search Filters**:
- location: string (partial match)
- minRent / maxRent: number
- minSize / maxSize: number
- propertyType: 'apartment' | 'house' | 'condominium'
- amenities: string[] (AND match)

**Traceability**: DES-RENTAL-001-C001, TSK-RENTAL-001-003

---

## 3.2 Tenant Management

### REQ-RENTAL-001-F010: Tenant Registration
**Category**: Tenant Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Event-driven

> **WHEN** a new tenant is registered,  
> **THE** system **SHALL** create a tenant record with unique ID (format: `TEN-YYYYMMDD-NNN`), storing name, contact information, and emergency contact.

**Required Fields**:
- fullName: string
- email: string (valid email format)
- phone: string
- emergencyContact: { name: string, phone: string }

**Traceability**: DES-RENTAL-001-C002, TSK-RENTAL-001-010

---

### REQ-RENTAL-001-F011: Tenant Verification Status
**Category**: Tenant Management  
**Priority**: P1 (Should Have)  
**EARS Pattern**: State-driven

> **WHILE** a tenant is in `pending-verification` status,  
> **THE** system **SHALL NOT** allow the tenant to sign any lease contract.

**Verification Status**: `pending-verification` → `verified` | `rejected`

**Traceability**: DES-RENTAL-001-C002, TSK-RENTAL-001-011

---

## 3.3 Lease Contract Management

### REQ-RENTAL-001-F020: Contract Creation
**Category**: Contract Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Event-driven

> **WHEN** a property manager creates a lease contract,  
> **THE** system **SHALL** create a contract record with unique ID (format: `LEASE-YYYYMMDD-NNN`), linking the property and tenant, with start date, end date, monthly rent, and deposit.

**Preconditions**:
- Property status must be `available` or `pending`
- Tenant verification status must be `verified`

**Postconditions**:
- Property status changes to `occupied`
- Contract status is `active`

**Traceability**: DES-RENTAL-001-C003, TSK-RENTAL-001-020

---

### REQ-RENTAL-001-F021: Contract Termination
**Category**: Contract Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Event-driven

> **WHEN** a lease contract is terminated,  
> **THE** system **SHALL** update contract status to `terminated`, record termination date and reason, and change property status to `available`.

**Termination Reasons**: `natural-expiry` | `early-termination` | `breach`

**Traceability**: DES-RENTAL-001-C003, TSK-RENTAL-001-021

---

### REQ-RENTAL-001-F022: Contract Renewal
**Category**: Contract Management  
**Priority**: P1 (Should Have)  
**EARS Pattern**: Conditional

> **IF** a lease contract is within 30 days of expiry **AND** neither party has indicated termination intent,  
> **THEN THE** system **SHALL** generate a renewal notification and create a draft renewal contract.

**Traceability**: DES-RENTAL-001-C003, TSK-RENTAL-001-022

---

## 3.4 Payment Management

### REQ-RENTAL-001-F030: Payment Recording
**Category**: Payment Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Event-driven

> **WHEN** a payment is recorded for a lease contract,  
> **THE** system **SHALL** create a payment record with unique ID (format: `PAY-YYYYMMDD-NNN`), storing amount, payment date, payment method, and payment period.

**Payment Methods**: `bank-transfer` | `credit-card` | `cash` | `auto-debit`

**Traceability**: DES-RENTAL-001-C004, TSK-RENTAL-001-030

---

### REQ-RENTAL-001-F031: Overdue Payment Detection
**Category**: Payment Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: State-driven

> **WHILE** a payment for a contract period is not recorded by the due date,  
> **THE** system **SHALL** mark the payment as `overdue` and generate an overdue notification.

**Grace Period**: 5 days after due date

**Traceability**: DES-RENTAL-001-C004, TSK-RENTAL-001-031

---

### REQ-RENTAL-001-F032: Payment History Query
**Category**: Payment Management  
**Priority**: P1 (Should Have)  
**EARS Pattern**: Event-driven

> **WHEN** a user queries payment history for a contract or tenant,  
> **THE** system **SHALL** return all payments ordered by date with running balance information.

**Traceability**: DES-RENTAL-001-C004, TSK-RENTAL-001-032

---

## 3.5 Maintenance Request Management

### REQ-RENTAL-001-F040: Maintenance Request Submission
**Category**: Maintenance Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Event-driven

> **WHEN** a tenant submits a maintenance request,  
> **THE** system **SHALL** create a request record with unique ID (format: `MAINT-YYYYMMDD-NNN`), storing property reference, description, priority, and photos.

**Priority Levels**: `emergency` | `high` | `medium` | `low`

**Traceability**: DES-RENTAL-001-C005, TSK-RENTAL-001-040

---

### REQ-RENTAL-001-F041: Maintenance Request Status Workflow
**Category**: Maintenance Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: State-driven

> **WHILE** a maintenance request exists,  
> **THE** system **SHALL** enforce status workflow: `submitted` → `assigned` → `in-progress` → `completed` | `cancelled`.

**Status Transition Map**:
```
submitted   → [assigned, cancelled]
assigned    → [in-progress, cancelled]
in-progress → [completed, cancelled]
completed   → []
cancelled   → []
```

**Traceability**: DES-RENTAL-001-C005, TSK-RENTAL-001-041

---

### REQ-RENTAL-001-F042: Emergency Maintenance Escalation
**Category**: Maintenance Management  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Conditional

> **IF** a maintenance request has priority `emergency` **AND** is not assigned within 1 hour,  
> **THEN THE** system **SHALL** automatically escalate to property manager with alert notification.

**Traceability**: DES-RENTAL-001-C005, TSK-RENTAL-001-042

---

## 4. Non-Functional Requirements

### REQ-RENTAL-001-NF001: Data Integrity
**Category**: Data Quality  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** maintain referential integrity between all entities, preventing orphan records.

---

### REQ-RENTAL-001-NF002: Audit Trail
**Category**: Compliance  
**Priority**: P0 (Must Have)  
**EARS Pattern**: Ubiquitous

> **THE** system **SHALL** maintain audit logs for all create, update, and delete operations with timestamp, user, and change details.

---

### REQ-RENTAL-001-NF003: Concurrent Access
**Category**: Performance  
**Priority**: P1 (Should Have)  
**EARS Pattern**: State-driven

> **WHILE** multiple users access the same record,  
> **THE** system **SHALL** use optimistic locking to prevent data conflicts.

---

## 5. Requirements Traceability Matrix (Preview)

| Requirement ID | Design ID | Task ID | Test ID |
|----------------|-----------|---------|---------|
| REQ-RENTAL-001-F001 | DES-RENTAL-001-C001 | TSK-RENTAL-001-001 | TEST-F001-* |
| REQ-RENTAL-001-F002 | DES-RENTAL-001-C001 | TSK-RENTAL-001-002 | TEST-F002-* |
| REQ-RENTAL-001-F003 | DES-RENTAL-001-C001 | TSK-RENTAL-001-003 | TEST-F003-* |
| REQ-RENTAL-001-F010 | DES-RENTAL-001-C002 | TSK-RENTAL-001-010 | TEST-F010-* |
| REQ-RENTAL-001-F020 | DES-RENTAL-001-C003 | TSK-RENTAL-001-020 | TEST-F020-* |
| REQ-RENTAL-001-F030 | DES-RENTAL-001-C004 | TSK-RENTAL-001-030 | TEST-F030-* |
| REQ-RENTAL-001-F040 | DES-RENTAL-001-C005 | TSK-RENTAL-001-040 | TEST-F040-* |

---

## 6. YATA Knowledge Graph Integration

This document will be stored in YATA Local with the following triples:

```turtle
@prefix req: <http://musubix.io/requirements/> .
@prefix rental: <http://musubix.io/property-rental/> .

req:REQ-RENTAL-001-F001 a req:FunctionalRequirement ;
    req:priority "P0" ;
    req:earsPattern "Event-driven" ;
    req:tracesTo rental:DES-RENTAL-001-C001 .
```

---

**Document End**
