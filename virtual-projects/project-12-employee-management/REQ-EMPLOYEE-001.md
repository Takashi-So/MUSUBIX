# Requirements Document: Employee Management System
## REQ-EMPLOYEE-001 v1.1.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 1.1.0 |
| **Status** | Approved |
| **Created** | 2026-01-04 |
| **Updated** | 2026-01-04 |
| **Author** | MUSUBIX SDD System |
| **Domain** | Human Resources |
| **Review Status** | Reviewed and approved |

---

### 2. System Overview

#### 2.1 Purpose
従業員管理システム（Employee Management System）は、企業の人事部門が従業員情報、部門構成、勤怠、給与を効率的に管理するためのシステムです。

#### 2.2 Scope
- 従業員情報管理（登録・更新・退職処理）
- 部門管理（作成・階層構造）
- 雇用形態管理
- 勤怠記録管理
- 給与計算・支払い管理

#### 2.3 Stakeholders

| Stakeholder | Role | Interest |
|-------------|------|----------|
| **HR Manager** | 人事マネージャー | 従業員情報の統合管理、レポート作成 |
| **Department Manager** | 部門長 | 部門メンバーの管理、勤怠承認 |
| **Employee** | 従業員 | 自身の情報確認、勤怠入力 |
| **Payroll Admin** | 給与担当 | 給与計算、支払い処理 |

---

### 3. Functional Requirements (EARS Format)

#### 3.1 Employee Management Requirements

##### REQ-EMPLOYEE-001-F001: Employee Registration
**Category**: Employee Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** an HR manager registers a new employee, **THE** system **SHALL** store employee details including name, email, hire date, department, position, and employment type with a unique employee ID.

**Acceptance Criteria**:
1. Employee ID format: `EMP-YYYYMMDD-NNN`
2. Required fields: name, email, hire_date, department_id, position, employment_type
3. Optional fields: phone, address, emergency_contact, profile_photo
4. Initial status: `active`

---

##### REQ-EMPLOYEE-001-F002: Employee Status Management
**Category**: Employee Management
**Priority**: P0 (Must Have)
**EARS Pattern**: State-driven

> **WHILE** an employee is in any status, **THE** system **SHALL** only allow valid status transitions as defined in the status transition map.

**Status Transition Map**:
| From | To | Condition |
|------|-----|-----------|
| `active` | `on_leave` | Leave request approved |
| `active` | `suspended` | Disciplinary action |
| `active` | `terminated` | Resignation or termination |
| `on_leave` | `active` | Leave period ended |
| `suspended` | `active` | Suspension lifted |
| `suspended` | `terminated` | Termination during suspension |

**Status Values**:
- `active`: 在籍中
- `on_leave`: 休職中
- `suspended`: 停職中
- `terminated`: 退職済み

---

##### REQ-EMPLOYEE-001-F003: Employee Search
**Category**: Employee Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a user searches for employees, **THE** system **SHALL** return matching employees based on criteria including name, department, position, and employment type within 2 seconds.

---

#### 3.2 Department Management Requirements

##### REQ-EMPLOYEE-001-F010: Department Creation
**Category**: Department Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** an administrator creates a new department, **THE** system **SHALL** store department details including name, code, and optional parent department with a unique department ID.

**Department ID Format**: `DEPT-YYYYMMDD-NNN`

**Required Fields**:
- Name
- Code (unique, alphanumeric)

**Optional Fields**:
- Parent department ID (for hierarchical structure)
- Description
- Manager employee ID

---

##### REQ-EMPLOYEE-001-F011: Department Hierarchy
**Category**: Department Management
**Priority**: P1 (Should Have)
**EARS Pattern**: State-driven

> **WHILE** a department has a parent department, **THE** system **SHALL** maintain the hierarchical relationship and allow traversal of the organization tree.

---

##### REQ-EMPLOYEE-001-F012: Department Member Query
**Category**: Department Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** a user requests department members, **THE** system **SHALL** return all employees assigned to the specified department.

---

#### 3.3 Attendance Management Requirements

##### REQ-EMPLOYEE-001-F020: Attendance Record Creation
**Category**: Attendance Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** an employee clocks in or out, **THE** system **SHALL** record the timestamp and calculate worked hours.

**Attendance ID Format**: `ATT-YYYYMMDD-NNN`

**Record Types**:
- `clock_in`: 出勤打刻
- `clock_out`: 退勤打刻

---

##### REQ-EMPLOYEE-001-F021: Working Hours Calculation
**Category**: Attendance Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** an employee clocks out, **THE** system **SHALL** calculate the total worked hours for that day, excluding break time.

**Calculation Rules**:
- Regular hours: First 8 hours
- Overtime hours: Hours exceeding 8 hours
- Standard break: 1 hour (deducted if worked > 6 hours)

---

##### REQ-EMPLOYEE-001-F022: Monthly Attendance Summary
**Category**: Attendance Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** a user requests monthly attendance summary, **THE** system **SHALL** calculate and return total worked days, total regular hours, and total overtime hours for the specified employee and month.

---

#### 3.4 Payroll Management Requirements

##### REQ-EMPLOYEE-001-F030: Payroll Calculation
**Category**: Payroll Management
**Priority**: P0 (Must Have)
**EARS Pattern**: Event-driven

> **WHEN** payroll is processed for a pay period, **THE** system **SHALL** calculate gross pay based on base salary, overtime, and allowances.

**Payroll ID Format**: `PAY-YYYYMMDD-NNN`

**Calculation Components**:
- Base salary (monthly)
- Overtime pay (hourly rate × 1.25 × overtime hours)
- Allowances (transport, housing, etc.)
- Deductions (tax, insurance, etc.)

---

##### REQ-EMPLOYEE-001-F031: Payroll Status Management
**Category**: Payroll Management
**Priority**: P0 (Must Have)
**EARS Pattern**: State-driven

> **WHILE** a payroll record exists, **THE** system **SHALL** track its status through the processing workflow.

**Payroll Status Transitions**:
| From | To | Action |
|------|-----|--------|
| `draft` | `pending_approval` | Submit for approval |
| `pending_approval` | `approved` | Manager approval |
| `pending_approval` | `draft` | Rejection with changes |
| `approved` | `paid` | Payment processed |

---

##### REQ-EMPLOYEE-001-F032: Tax Calculation
**Category**: Payroll Management
**Priority**: P1 (Should Have)
**EARS Pattern**: Event-driven

> **WHEN** payroll is calculated, **THE** system **SHALL** apply income tax based on gross pay using progressive tax brackets.

**Tax Brackets (Simplified)**:
| Gross Pay Range (Monthly) | Tax Rate |
|---------------------------|----------|
| 0 - 300,000 | 5% |
| 300,001 - 500,000 | 10% |
| 500,001 - 1,000,000 | 20% |
| 1,000,001+ | 30% |

---

#### 3.5 Error Handling Requirements

##### REQ-EMPLOYEE-001-F040: Duplicate Email Prevention
**Category**: Error Handling
**Priority**: P0 (Must Have)
**EARS Pattern**: Unwanted

> **THE** system **SHALL NOT** allow registration of employees with duplicate email addresses.

---

##### REQ-EMPLOYEE-001-F041: Invalid Status Transition Prevention
**Category**: Error Handling
**Priority**: P0 (Must Have)
**EARS Pattern**: Unwanted

> **THE** system **SHALL NOT** allow invalid employee status transitions.

---

##### REQ-EMPLOYEE-001-F042: Attendance Validation
**Category**: Error Handling
**Priority**: P0 (Must Have)
**EARS Pattern**: Unwanted

> **THE** system **SHALL NOT** allow clock-out without prior clock-in on the same day.

---

### 4. Non-Functional Requirements

#### 4.1 Performance
- Employee search response time: < 2 seconds
- Payroll calculation: < 5 seconds per employee
- Monthly summary generation: < 10 seconds

#### 4.2 Security
- Salary information access: HR and Payroll Admin only
- Personal information: Encrypted at rest
- Audit logging for all modifications

#### 4.3 Compliance
- Labor law compliance for overtime calculations
- Tax regulation compliance for payroll

---

### 5. Traceability Matrix

| Requirement ID | Design | Task | Test |
|---------------|--------|------|------|
| REQ-EMPLOYEE-001-F001 | DES-4.1.1 | TSK-003 | TEST-001 |
| REQ-EMPLOYEE-001-F002 | DES-4.1.1 | TSK-003 | TEST-002 |
| REQ-EMPLOYEE-001-F003 | DES-5.1 | TSK-007 | TEST-003 |
| REQ-EMPLOYEE-001-F010 | DES-4.1.2 | TSK-004 | TEST-010 |
| REQ-EMPLOYEE-001-F011 | DES-4.1.2 | TSK-004 | TEST-011 |
| REQ-EMPLOYEE-001-F012 | DES-5.2 | TSK-008 | TEST-012 |
| REQ-EMPLOYEE-001-F020 | DES-4.1.3 | TSK-005 | TEST-020 |
| REQ-EMPLOYEE-001-F021 | DES-4.1.3 | TSK-005 | TEST-021 |
| REQ-EMPLOYEE-001-F022 | DES-5.3 | TSK-009 | TEST-022 |
| REQ-EMPLOYEE-001-F030 | DES-4.1.4 | TSK-006 | TEST-030 |
| REQ-EMPLOYEE-001-F031 | DES-4.1.4 | TSK-006 | TEST-031 |
| REQ-EMPLOYEE-001-F032 | DES-4.1.4 | TSK-006 | TEST-032 |
| REQ-EMPLOYEE-001-F040 | DES-5.1 | TSK-007 | TEST-040 |
| REQ-EMPLOYEE-001-F041 | DES-4.1.1 | TSK-003 | TEST-041 |
| REQ-EMPLOYEE-001-F042 | DES-5.3 | TSK-009 | TEST-042 |

---

### 6. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-04 | MUSUBIX SDD | Initial draft |
| 1.1.0 | 2026-01-04 | MUSUBIX SDD | Added tax calculation, clarified status transitions |
