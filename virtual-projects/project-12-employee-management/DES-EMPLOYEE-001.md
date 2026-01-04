# Design Document: Employee Management System
## DES-EMPLOYEE-001 v1.0.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 1.0.0 |
| **Status** | Approved |
| **Created** | 2026-01-04 |
| **Author** | MUSUBIX SDD System |
| **Requirement Ref** | REQ-EMPLOYEE-001 v1.1.0 |

---

### 2. Architecture Overview

#### 2.1 Architecture Pattern
**Clean Architecture** with the following layers:
- **Domain Layer**: Entities, Value Objects, Domain Services
- **Application Layer**: Use Cases, Application Services
- **Infrastructure Layer**: Repositories, External Services

#### 2.2 Design Principles
- **SOLID Principles**: All components follow SOLID
- **DI (Dependency Injection)**: Repository interfaces injected into services
- **Domain-Driven Design**: Rich domain models with business logic

---

### 3. C4 Model

#### 3.1 Context Diagram (Level 1)

```
┌─────────────────────────────────────────────────────────────────┐
│                    Employee Management System                    │
│                        [Software System]                         │
│                                                                  │
│  Manages employee information, attendance, departments,          │
│  and payroll processing                                          │
└─────────────────────────────────────────────────────────────────┘
         ▲                    ▲                    ▲
         │                    │                    │
    ┌────┴────┐         ┌────┴────┐         ┌────┴────┐
    │HR Manager│         │Department│         │ Payroll │
    │ [Actor] │         │ Manager  │         │  Admin  │
    │         │         │ [Actor]  │         │ [Actor] │
    └─────────┘         └──────────┘         └─────────┘
```

#### 3.2 Container Diagram (Level 2)

```
┌─────────────────────────────────────────────────────────────────┐
│                    Employee Management System                    │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │
│  │   Application   │  │    Domain       │  │ Infrastructure  │  │
│  │     Layer       │  │     Layer       │  │     Layer       │  │
│  │  [Container]    │  │  [Container]    │  │  [Container]    │  │
│  │                 │  │                 │  │                 │  │
│  │ • EmployeeService│  │ • Employee     │  │ • EmployeeRepo  │  │
│  │ • DepartmentSvc │  │ • Department   │  │ • DepartmentRepo│  │
│  │ • AttendanceSvc │  │ • Attendance   │  │ • AttendanceRepo│  │
│  │ • PayrollService│  │ • Payroll      │  │ • PayrollRepo   │  │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

#### 3.3 Component Diagram (Level 3)

```
┌─────────────────── Domain Layer ───────────────────┐
│                                                     │
│  ┌─────────────┐  ┌─────────────┐  ┌────────────┐  │
│  │  Employee   │  │ Department  │  │ Attendance │  │
│  │  [Entity]   │  │  [Entity]   │  │  [Entity]  │  │
│  └─────────────┘  └─────────────┘  └────────────┘  │
│                                                     │
│  ┌─────────────┐  ┌─────────────┐                  │
│  │  Payroll    │  │   Money     │                  │
│  │  [Entity]   │  │[ValueObject]│                  │
│  └─────────────┘  └─────────────┘                  │
└─────────────────────────────────────────────────────┘

┌─────────────── Application Layer ──────────────────┐
│                                                     │
│  ┌─────────────────┐  ┌─────────────────────────┐  │
│  │EmployeeService  │  │ DepartmentService       │  │
│  │                 │  │                         │  │
│  │ • registerEmployee │ • createDepartment     │  │
│  │ • updateEmployee│  │ • getDepartmentMembers │  │
│  │ • changeStatus  │  │ • getHierarchy         │  │
│  │ • searchEmployees│ └─────────────────────────┘  │
│  └─────────────────┘                               │
│                                                     │
│  ┌─────────────────┐  ┌─────────────────────────┐  │
│  │AttendanceService│  │ PayrollService          │  │
│  │                 │  │                         │  │
│  │ • clockIn       │  │ • calculatePayroll     │  │
│  │ • clockOut      │  │ • approvePayroll       │  │
│  │ • getMonthlySummary│ • processPayment       │  │
│  └─────────────────┘  └─────────────────────────┘  │
└─────────────────────────────────────────────────────┘

┌─────────────── Infrastructure Layer ───────────────┐
│                                                     │
│  ┌─────────────────┐  ┌─────────────────────────┐  │
│  │EmployeeRepository│ │ DepartmentRepository    │  │
│  │ <<interface>>   │  │ <<interface>>           │  │
│  └────────┬────────┘  └────────────┬────────────┘  │
│           │                         │               │
│  ┌────────▼────────┐  ┌────────────▼────────────┐  │
│  │InMemoryEmployee │  │ InMemoryDepartment      │  │
│  │    Repository   │  │      Repository         │  │
│  └─────────────────┘  └─────────────────────────┘  │
│                                                     │
│  ┌─────────────────┐  ┌─────────────────────────┐  │
│  │AttendanceRepository│ │ PayrollRepository      │  │
│  │ <<interface>>   │  │ <<interface>>           │  │
│  └────────┬────────┘  └────────────┬────────────┘  │
│           │                         │               │
│  ┌────────▼────────┐  ┌────────────▼────────────┐  │
│  │InMemoryAttendance│ │ InMemoryPayroll         │  │
│  │    Repository   │  │      Repository         │  │
│  └─────────────────┘  └─────────────────────────┘  │
└─────────────────────────────────────────────────────┘
```

---

### 4. Entity Definitions

#### 4.1 Domain Entities

##### 4.1.1 Employee Entity

```typescript
// REQ-EMPLOYEE-001-F001, F002, F003
interface Employee {
  id: EmployeeId;           // "EMP-YYYYMMDD-NNN"
  name: PersonName;
  email: string;
  phone?: string;
  hireDate: Date;
  departmentId: DepartmentId;
  position: string;
  employmentType: EmploymentType;  // full_time | part_time | contract
  status: EmployeeStatus;          // active | on_leave | suspended | terminated
  salary: Money;
  createdAt: Date;
  updatedAt: Date;
}

// Valid status transitions
const employeeStatusTransitions: Record<EmployeeStatus, EmployeeStatus[]> = {
  active: ['on_leave', 'suspended', 'terminated'],
  on_leave: ['active'],
  suspended: ['active', 'terminated'],
  terminated: [],
};
```

##### 4.1.2 Department Entity

```typescript
// REQ-EMPLOYEE-001-F010, F011, F012
interface Department {
  id: DepartmentId;         // "DEPT-YYYYMMDD-NNN"
  name: string;
  code: string;             // Unique alphanumeric code
  parentId?: DepartmentId;  // For hierarchical structure
  managerId?: EmployeeId;
  description?: string;
  createdAt: Date;
  updatedAt: Date;
}
```

##### 4.1.3 Attendance Entity

```typescript
// REQ-EMPLOYEE-001-F020, F021, F022
interface Attendance {
  id: AttendanceId;         // "ATT-YYYYMMDD-NNN"
  employeeId: EmployeeId;
  date: Date;
  clockIn?: Date;
  clockOut?: Date;
  breakMinutes: number;     // Default: 60 if worked > 6 hours
  regularHours: number;     // Max 8 hours
  overtimeHours: number;    // Hours exceeding 8
  createdAt: Date;
  updatedAt: Date;
}

interface MonthlySummary {
  employeeId: EmployeeId;
  year: number;
  month: number;
  totalWorkedDays: number;
  totalRegularHours: number;
  totalOvertimeHours: number;
}
```

##### 4.1.4 Payroll Entity

```typescript
// REQ-EMPLOYEE-001-F030, F031, F032
interface Payroll {
  id: PayrollId;            // "PAY-YYYYMMDD-NNN"
  employeeId: EmployeeId;
  payPeriodStart: Date;
  payPeriodEnd: Date;
  baseSalary: Money;
  overtimePay: Money;
  allowances: Money;
  grossPay: Money;
  taxDeduction: Money;
  otherDeductions: Money;
  netPay: Money;
  status: PayrollStatus;    // draft | pending_approval | approved | paid
  createdAt: Date;
  updatedAt: Date;
}

// Payroll status transitions
const payrollStatusTransitions: Record<PayrollStatus, PayrollStatus[]> = {
  draft: ['pending_approval'],
  pending_approval: ['approved', 'draft'],
  approved: ['paid'],
  paid: [],
};

// Tax calculation (simplified)
const taxBrackets: TaxBracket[] = [
  { minAmount: 0, maxAmount: 300000, rate: 0.05 },
  { minAmount: 300001, maxAmount: 500000, rate: 0.10 },
  { minAmount: 500001, maxAmount: 1000000, rate: 0.20 },
  { minAmount: 1000001, maxAmount: Infinity, rate: 0.30 },
];
```

#### 4.2 Value Objects

##### 4.2.1 Money Value Object

```typescript
interface Money {
  amount: number;
  currency: Currency;  // Default: "JPY"
}

function createMoney(amount: number, currency: Currency = 'JPY'): Money {
  if (amount < 0) throw new Error('Amount cannot be negative');
  return { amount, currency };
}

function addMoney(a: Money, b: Money): Money {
  if (a.currency !== b.currency) throw new Error('Currency mismatch');
  return createMoney(a.amount + b.amount, a.currency);
}
```

##### 4.2.2 PersonName Value Object

```typescript
interface PersonName {
  firstName: string;
  lastName: string;
  fullName: string;  // Computed: lastName + ' ' + firstName (Japanese style)
}
```

---

### 5. Repository Interfaces

#### 5.1 EmployeeRepository

```typescript
// REQ-EMPLOYEE-001-F001, F002, F003, F040
interface EmployeeRepository {
  save(employee: Employee): Promise<void>;
  findById(id: EmployeeId): Promise<Employee | null>;
  findByEmail(email: string): Promise<Employee | null>;
  findByDepartmentId(departmentId: DepartmentId): Promise<Employee[]>;
  search(criteria: EmployeeSearchCriteria): Promise<Employee[]>;
  findAll(): Promise<Employee[]>;
  delete(id: EmployeeId): Promise<void>;
}

interface EmployeeSearchCriteria {
  name?: string;
  departmentId?: DepartmentId;
  position?: string;
  employmentType?: EmploymentType;
  status?: EmployeeStatus;
}
```

#### 5.2 DepartmentRepository

```typescript
// REQ-EMPLOYEE-001-F010, F011, F012
interface DepartmentRepository {
  save(department: Department): Promise<void>;
  findById(id: DepartmentId): Promise<Department | null>;
  findByCode(code: string): Promise<Department | null>;
  findByParentId(parentId: DepartmentId): Promise<Department[]>;
  findAll(): Promise<Department[]>;
  delete(id: DepartmentId): Promise<void>;
}
```

#### 5.3 AttendanceRepository

```typescript
// REQ-EMPLOYEE-001-F020, F021, F022, F042
interface AttendanceRepository {
  save(attendance: Attendance): Promise<void>;
  findById(id: AttendanceId): Promise<Attendance | null>;
  findByEmployeeAndDate(employeeId: EmployeeId, date: Date): Promise<Attendance | null>;
  findByEmployeeAndMonth(employeeId: EmployeeId, year: number, month: number): Promise<Attendance[]>;
  findAll(): Promise<Attendance[]>;
  delete(id: AttendanceId): Promise<void>;
}
```

#### 5.4 PayrollRepository

```typescript
// REQ-EMPLOYEE-001-F030, F031
interface PayrollRepository {
  save(payroll: Payroll): Promise<void>;
  findById(id: PayrollId): Promise<Payroll | null>;
  findByEmployeeId(employeeId: EmployeeId): Promise<Payroll[]>;
  findByPeriod(start: Date, end: Date): Promise<Payroll[]>;
  findAll(): Promise<Payroll[]>;
  delete(id: PayrollId): Promise<void>;
}
```

---

### 6. Application Services

#### 6.1 EmployeeService

```typescript
class EmployeeService {
  constructor(
    private employeeRepository: EmployeeRepository,
    private departmentRepository: DepartmentRepository
  ) {}

  // REQ-EMPLOYEE-001-F001
  async registerEmployee(input: CreateEmployeeInput): Promise<Employee> {
    // Check duplicate email
    const existing = await this.employeeRepository.findByEmail(input.email);
    if (existing) throw new DuplicateEmailError(input.email);
    
    // Verify department exists
    const department = await this.departmentRepository.findById(input.departmentId);
    if (!department) throw new DepartmentNotFoundError(input.departmentId);
    
    const employee = createEmployee(input);
    await this.employeeRepository.save(employee);
    return employee;
  }

  // REQ-EMPLOYEE-001-F002
  async changeStatus(id: EmployeeId, newStatus: EmployeeStatus): Promise<Employee> {
    const employee = await this.employeeRepository.findById(id);
    if (!employee) throw new EmployeeNotFoundError(id);
    
    const updatedEmployee = changeEmployeeStatus(employee, newStatus);
    await this.employeeRepository.save(updatedEmployee);
    return updatedEmployee;
  }

  // REQ-EMPLOYEE-001-F003
  async searchEmployees(criteria: EmployeeSearchCriteria): Promise<Employee[]> {
    return this.employeeRepository.search(criteria);
  }
}
```

#### 6.2 AttendanceService

```typescript
class AttendanceService {
  constructor(
    private attendanceRepository: AttendanceRepository,
    private employeeRepository: EmployeeRepository
  ) {}

  // REQ-EMPLOYEE-001-F020
  async clockIn(employeeId: EmployeeId): Promise<Attendance> {
    const employee = await this.employeeRepository.findById(employeeId);
    if (!employee) throw new EmployeeNotFoundError(employeeId);
    
    const today = new Date();
    const existing = await this.attendanceRepository.findByEmployeeAndDate(employeeId, today);
    if (existing?.clockIn) throw new AlreadyClockedInError(employeeId);
    
    const attendance = createAttendance({ employeeId, clockIn: new Date() });
    await this.attendanceRepository.save(attendance);
    return attendance;
  }

  // REQ-EMPLOYEE-001-F021
  async clockOut(employeeId: EmployeeId): Promise<Attendance> {
    const today = new Date();
    const attendance = await this.attendanceRepository.findByEmployeeAndDate(employeeId, today);
    if (!attendance?.clockIn) throw new NotClockedInError(employeeId);
    if (attendance.clockOut) throw new AlreadyClockedOutError(employeeId);
    
    const updatedAttendance = recordClockOut(attendance, new Date());
    await this.attendanceRepository.save(updatedAttendance);
    return updatedAttendance;
  }

  // REQ-EMPLOYEE-001-F022
  async getMonthlySummary(employeeId: EmployeeId, year: number, month: number): Promise<MonthlySummary> {
    const records = await this.attendanceRepository.findByEmployeeAndMonth(employeeId, year, month);
    return calculateMonthlySummary(employeeId, year, month, records);
  }
}
```

#### 6.3 PayrollService

```typescript
class PayrollService {
  constructor(
    private payrollRepository: PayrollRepository,
    private employeeRepository: EmployeeRepository,
    private attendanceRepository: AttendanceRepository
  ) {}

  // REQ-EMPLOYEE-001-F030
  async calculatePayroll(employeeId: EmployeeId, periodStart: Date, periodEnd: Date): Promise<Payroll> {
    const employee = await this.employeeRepository.findById(employeeId);
    if (!employee) throw new EmployeeNotFoundError(employeeId);
    
    // Get attendance records for period
    const attendanceRecords = await this.getAttendanceForPeriod(employeeId, periodStart, periodEnd);
    const { regularHours, overtimeHours } = sumAttendanceHours(attendanceRecords);
    
    // Calculate pay components
    const baseSalary = employee.salary;
    const hourlyRate = calculateHourlyRate(baseSalary);
    const overtimePay = createMoney(hourlyRate * 1.25 * overtimeHours);
    const grossPay = addMoney(baseSalary, overtimePay);
    
    // REQ-EMPLOYEE-001-F032: Tax calculation
    const taxDeduction = calculateTax(grossPay);
    const netPay = subtractMoney(grossPay, taxDeduction);
    
    const payroll = createPayroll({
      employeeId,
      payPeriodStart: periodStart,
      payPeriodEnd: periodEnd,
      baseSalary,
      overtimePay,
      allowances: createMoney(0),
      grossPay,
      taxDeduction,
      otherDeductions: createMoney(0),
      netPay,
    });
    
    await this.payrollRepository.save(payroll);
    return payroll;
  }

  // REQ-EMPLOYEE-001-F031
  async updateStatus(id: PayrollId, newStatus: PayrollStatus): Promise<Payroll> {
    const payroll = await this.payrollRepository.findById(id);
    if (!payroll) throw new PayrollNotFoundError(id);
    
    const updatedPayroll = changePayrollStatus(payroll, newStatus);
    await this.payrollRepository.save(updatedPayroll);
    return updatedPayroll;
  }
}
```

---

### 7. Error Definitions

```typescript
// Domain Errors
class EmployeeNotFoundError extends Error {
  constructor(id: EmployeeId) {
    super(`Employee not found: ${id}`);
    this.name = 'EmployeeNotFoundError';
  }
}

class DuplicateEmailError extends Error {
  constructor(email: string) {
    super(`Email already registered: ${email}`);
    this.name = 'DuplicateEmailError';
  }
}

class InvalidStatusTransitionError extends Error {
  constructor(from: string, to: string) {
    super(`Invalid status transition from ${from} to ${to}`);
    this.name = 'InvalidStatusTransitionError';
  }
}

class DepartmentNotFoundError extends Error {
  constructor(id: DepartmentId) {
    super(`Department not found: ${id}`);
    this.name = 'DepartmentNotFoundError';
  }
}

class AlreadyClockedInError extends Error {
  constructor(employeeId: EmployeeId) {
    super(`Employee ${employeeId} already clocked in today`);
    this.name = 'AlreadyClockedInError';
  }
}

class NotClockedInError extends Error {
  constructor(employeeId: EmployeeId) {
    super(`Employee ${employeeId} has not clocked in today`);
    this.name = 'NotClockedInError';
  }
}

class PayrollNotFoundError extends Error {
  constructor(id: PayrollId) {
    super(`Payroll not found: ${id}`);
    this.name = 'PayrollNotFoundError';
  }
}
```

---

### 8. Traceability to Requirements

| Design Component | Requirements |
|-----------------|--------------|
| Employee Entity | REQ-EMPLOYEE-001-F001, F002, F003, F040, F041 |
| Department Entity | REQ-EMPLOYEE-001-F010, F011, F012 |
| Attendance Entity | REQ-EMPLOYEE-001-F020, F021, F022, F042 |
| Payroll Entity | REQ-EMPLOYEE-001-F030, F031, F032 |
| EmployeeService | REQ-EMPLOYEE-001-F001, F002, F003, F040, F041 |
| AttendanceService | REQ-EMPLOYEE-001-F020, F021, F022, F042 |
| PayrollService | REQ-EMPLOYEE-001-F030, F031, F032 |

---

### 9. Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-04 | MUSUBIX SDD | Initial design |
