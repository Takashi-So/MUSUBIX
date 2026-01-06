# Design Document: Property Rental Management System
## DES-RENTAL-001 v2.0.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 2.0.0 |
| **Status** | Draft |
| **Created** | 2026-01-06 |
| **Author** | MUSUBIX SDD System |
| **Requirements** | REQ-RENTAL-001 v2.0.0 |
| **Design Pattern** | DDD, Repository, Service Layer |

---

### 2. C4 Model

#### 2.1 Context Diagram (Level 1)

```
┌─────────────────────────────────────────────────────────────┐
│                    Property Rental System                     │
│                                                               │
│  ┌───────────────┐                    ┌───────────────┐      │
│  │  Property     │                    │    Tenant     │      │
│  │  Manager      │                    │               │      │
│  └───────┬───────┘                    └───────┬───────┘      │
│          │                                    │              │
│          ▼                                    ▼              │
│  ┌───────────────────────────────────────────────────┐      │
│  │           Property Rental Management System        │      │
│  │                      (PRMS)                        │      │
│  └───────────────────────────────────────────────────┘      │
│          │                                    │              │
│          ▼                                    ▼              │
│  ┌───────────────┐                    ┌───────────────┐      │
│  │  Maintenance  │                    │  Notification │      │
│  │    Staff      │                    │    Service    │      │
│  └───────────────┘                    └───────────────┘      │
└─────────────────────────────────────────────────────────────┘
```

#### 2.2 Container Diagram (Level 2)

```
┌─────────────────────────────────────────────────────────────┐
│                        PRMS Application                      │
│                                                               │
│  ┌─────────────────────────────────────────────────────┐    │
│  │                   Domain Layer                        │    │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐            │    │
│  │  │ Property │ │  Tenant  │ │ Contract │            │    │
│  │  │  Module  │ │  Module  │ │  Module  │            │    │
│  │  └──────────┘ └──────────┘ └──────────┘            │    │
│  │  ┌──────────┐ ┌──────────┐                          │    │
│  │  │ Payment  │ │Maintenance│                          │    │
│  │  │  Module  │ │  Module  │                          │    │
│  │  └──────────┘ └──────────┘                          │    │
│  └─────────────────────────────────────────────────────┘    │
│                            │                                  │
│  ┌─────────────────────────────────────────────────────┐    │
│  │              Infrastructure Layer                     │    │
│  │  ┌──────────────┐    ┌──────────────┐              │    │
│  │  │  Repository  │    │ YATA Local   │              │    │
│  │  │   (SQLite)   │    │   (KG)       │              │    │
│  │  └──────────────┘    └──────────────┘              │    │
│  └─────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
```

---

### 3. Component Design (Level 3)

#### 3.1 DES-RENTAL-001-C001: Property Component

**Traces to**: REQ-RENTAL-001-F001, F002, F003

```typescript
// Entity: Property
interface Property {
  id: PropertyId;              // PROP-YYYYMMDD-NNN
  address: Address;            // Value Object
  propertyType: PropertyType;  // apartment | house | condominium
  sizeSqm: number;
  monthlyRent: Money;          // Value Object
  deposit: Money;              // Value Object
  status: PropertyStatus;      // available | pending | occupied | maintenance
  amenities: string[];
  description?: string;
  photos?: string[];
  createdAt: Date;
  updatedAt: Date;
  version: number;             // Optimistic locking
}

// Value Objects
interface PropertyId { value: string }
interface Address { prefecture: string; city: string; street: string; building?: string }
interface Money { amount: number; currency: 'JPY' }
type PropertyType = 'apartment' | 'house' | 'condominium';
type PropertyStatus = 'available' | 'pending' | 'occupied' | 'maintenance';

// Status Transition Map (BP-DESIGN-001)
const validPropertyStatusTransitions: Record<PropertyStatus, PropertyStatus[]> = {
  'available': ['pending', 'maintenance'],
  'pending': ['occupied', 'available'],
  'occupied': ['available', 'maintenance'],
  'maintenance': ['available'],
};

// Repository Interface
interface PropertyRepository {
  create(input: CreatePropertyInput): Promise<Result<Property, DomainError>>;
  findById(id: PropertyId): Promise<Result<Property | null, DomainError>>;
  findByFilters(filters: PropertySearchFilters): Promise<Result<Property[], DomainError>>;
  updateStatus(id: PropertyId, newStatus: PropertyStatus, reason: string): Promise<Result<Property, DomainError>>;
  update(property: Property): Promise<Result<Property, DomainError>>;
}

// Service
interface PropertyService {
  registerProperty(input: CreatePropertyInput): Promise<Result<Property, DomainError>>;
  searchProperties(filters: PropertySearchFilters): Promise<Result<Property[], DomainError>>;
  changeStatus(id: PropertyId, newStatus: PropertyStatus, reason: string): Promise<Result<Property, DomainError>>;
}
```

---

#### 3.2 DES-RENTAL-001-C002: Tenant Component

**Traces to**: REQ-RENTAL-001-F010, F011

```typescript
// Entity: Tenant
interface Tenant {
  id: TenantId;                  // TEN-YYYYMMDD-NNN
  fullName: string;
  email: Email;                  // Value Object
  phone: Phone;                  // Value Object
  emergencyContact: EmergencyContact;
  verificationStatus: VerificationStatus;
  createdAt: Date;
  updatedAt: Date;
  version: number;
}

// Value Objects
interface TenantId { value: string }
interface Email { value: string }
interface Phone { value: string }
interface EmergencyContact { name: string; phone: Phone }
type VerificationStatus = 'pending-verification' | 'verified' | 'rejected';

// Status Transition Map
const validVerificationStatusTransitions: Record<VerificationStatus, VerificationStatus[]> = {
  'pending-verification': ['verified', 'rejected'],
  'verified': [],
  'rejected': [],
};

// Repository Interface
interface TenantRepository {
  create(input: CreateTenantInput): Promise<Result<Tenant, DomainError>>;
  findById(id: TenantId): Promise<Result<Tenant | null, DomainError>>;
  updateVerificationStatus(id: TenantId, status: VerificationStatus): Promise<Result<Tenant, DomainError>>;
}

// Service
interface TenantService {
  registerTenant(input: CreateTenantInput): Promise<Result<Tenant, DomainError>>;
  verifyTenant(id: TenantId): Promise<Result<Tenant, DomainError>>;
  rejectTenant(id: TenantId, reason: string): Promise<Result<Tenant, DomainError>>;
}
```

---

#### 3.3 DES-RENTAL-001-C003: LeaseContract Component

**Traces to**: REQ-RENTAL-001-F020, F021, F022

```typescript
// Entity: LeaseContract
interface LeaseContract {
  id: LeaseContractId;           // LEASE-YYYYMMDD-NNN
  propertyId: PropertyId;
  tenantId: TenantId;
  startDate: Date;
  endDate: Date;
  monthlyRent: Money;
  deposit: Money;
  status: ContractStatus;
  terminationDate?: Date;
  terminationReason?: TerminationReason;
  createdAt: Date;
  updatedAt: Date;
  version: number;
}

// Types
interface LeaseContractId { value: string }
type ContractStatus = 'draft' | 'active' | 'terminated' | 'expired';
type TerminationReason = 'natural-expiry' | 'early-termination' | 'breach';

// Status Transition Map
const validContractStatusTransitions: Record<ContractStatus, ContractStatus[]> = {
  'draft': ['active'],
  'active': ['terminated', 'expired'],
  'terminated': [],
  'expired': [],
};

// Repository Interface
interface LeaseContractRepository {
  create(input: CreateLeaseContractInput): Promise<Result<LeaseContract, DomainError>>;
  findById(id: LeaseContractId): Promise<Result<LeaseContract | null, DomainError>>;
  findByPropertyId(propertyId: PropertyId): Promise<Result<LeaseContract[], DomainError>>;
  findByTenantId(tenantId: TenantId): Promise<Result<LeaseContract[], DomainError>>;
  findExpiringContracts(withinDays: number): Promise<Result<LeaseContract[], DomainError>>;
  terminate(id: LeaseContractId, reason: TerminationReason): Promise<Result<LeaseContract, DomainError>>;
}

// Service
interface LeaseContractService {
  createContract(input: CreateLeaseContractInput): Promise<Result<LeaseContract, DomainError>>;
  terminateContract(id: LeaseContractId, reason: TerminationReason): Promise<Result<LeaseContract, DomainError>>;
  checkRenewalEligibility(id: LeaseContractId): Promise<Result<RenewalEligibility, DomainError>>;
}
```

---

#### 3.4 DES-RENTAL-001-C004: Payment Component

**Traces to**: REQ-RENTAL-001-F030, F031, F032

```typescript
// Entity: Payment
interface Payment {
  id: PaymentId;                 // PAY-YYYYMMDD-NNN
  contractId: LeaseContractId;
  amount: Money;
  paymentDate: Date;
  paymentMethod: PaymentMethod;
  paymentPeriod: PaymentPeriod;  // e.g., "2026-01"
  status: PaymentStatus;
  dueDate: Date;
  createdAt: Date;
  updatedAt: Date;
}

// Types
interface PaymentId { value: string }
type PaymentMethod = 'bank-transfer' | 'credit-card' | 'cash' | 'auto-debit';
type PaymentPeriod = string;  // YYYY-MM format
type PaymentStatus = 'pending' | 'paid' | 'overdue';

// Grace Period: 5 days
const PAYMENT_GRACE_PERIOD_DAYS = 5;

// Repository Interface
interface PaymentRepository {
  create(input: CreatePaymentInput): Promise<Result<Payment, DomainError>>;
  findById(id: PaymentId): Promise<Result<Payment | null, DomainError>>;
  findByContractId(contractId: LeaseContractId): Promise<Result<Payment[], DomainError>>;
  findOverduePayments(): Promise<Result<Payment[], DomainError>>;
  markAsOverdue(id: PaymentId): Promise<Result<Payment, DomainError>>;
}

// Service
interface PaymentService {
  recordPayment(input: CreatePaymentInput): Promise<Result<Payment, DomainError>>;
  getPaymentHistory(contractId: LeaseContractId): Promise<Result<PaymentHistory, DomainError>>;
  checkOverduePayments(): Promise<Result<OverdueReport, DomainError>>;
}
```

---

#### 3.5 DES-RENTAL-001-C005: MaintenanceRequest Component

**Traces to**: REQ-RENTAL-001-F040, F041, F042

```typescript
// Entity: MaintenanceRequest
interface MaintenanceRequest {
  id: MaintenanceRequestId;      // MAINT-YYYYMMDD-NNN
  propertyId: PropertyId;
  tenantId: TenantId;
  description: string;
  priority: MaintenancePriority;
  status: MaintenanceStatus;
  photos?: string[];
  assignedTo?: string;
  assignedAt?: Date;
  completedAt?: Date;
  createdAt: Date;
  updatedAt: Date;
}

// Types
interface MaintenanceRequestId { value: string }
type MaintenancePriority = 'emergency' | 'high' | 'medium' | 'low';
type MaintenanceStatus = 'submitted' | 'assigned' | 'in-progress' | 'completed' | 'cancelled';

// Status Transition Map
const validMaintenanceStatusTransitions: Record<MaintenanceStatus, MaintenanceStatus[]> = {
  'submitted': ['assigned', 'cancelled'],
  'assigned': ['in-progress', 'cancelled'],
  'in-progress': ['completed', 'cancelled'],
  'completed': [],
  'cancelled': [],
};

// Escalation threshold: 1 hour for emergency
const EMERGENCY_ESCALATION_MINUTES = 60;

// Repository Interface
interface MaintenanceRequestRepository {
  create(input: CreateMaintenanceRequestInput): Promise<Result<MaintenanceRequest, DomainError>>;
  findById(id: MaintenanceRequestId): Promise<Result<MaintenanceRequest | null, DomainError>>;
  findByPropertyId(propertyId: PropertyId): Promise<Result<MaintenanceRequest[], DomainError>>;
  findUnassignedEmergencies(olderThanMinutes: number): Promise<Result<MaintenanceRequest[], DomainError>>;
  updateStatus(id: MaintenanceRequestId, status: MaintenanceStatus): Promise<Result<MaintenanceRequest, DomainError>>;
  assignTo(id: MaintenanceRequestId, assignee: string): Promise<Result<MaintenanceRequest, DomainError>>;
}

// Service
interface MaintenanceRequestService {
  submitRequest(input: CreateMaintenanceRequestInput): Promise<Result<MaintenanceRequest, DomainError>>;
  assignRequest(id: MaintenanceRequestId, assignee: string): Promise<Result<MaintenanceRequest, DomainError>>;
  updateStatus(id: MaintenanceRequestId, status: MaintenanceStatus): Promise<Result<MaintenanceRequest, DomainError>>;
  checkEmergencyEscalations(): Promise<Result<EscalationReport, DomainError>>;
}
```

---

### 4. Design Patterns Applied

| Pattern | Applied To | Justification |
|---------|------------|---------------|
| **Repository** | All entities | Abstraction over data access (BP-DESIGN-002) |
| **Service Layer** | All modules | Business logic encapsulation (BP-DESIGN-003) |
| **Value Object** | PropertyId, Money, Email, etc. | Immutable domain concepts (BP-CODE-004) |
| **Status Transition Map** | Property, Contract, Maintenance | Explicit state machine (BP-DESIGN-001) |
| **Result Type** | All operations | Explicit error handling (BP-CODE-005) |
| **Optimistic Locking** | All entities | Concurrent access control (BP-DESIGN-004) |
| **Factory Function** | Value Object creation | Type-safe construction (BP-CODE-004) |

---

### 5. File Structure

```
src/
├── entities/
│   ├── Property.ts           # Property entity & value objects
│   ├── Tenant.ts             # Tenant entity & value objects
│   ├── LeaseContract.ts      # LeaseContract entity
│   ├── Payment.ts            # Payment entity
│   └── MaintenanceRequest.ts # MaintenanceRequest entity
├── repositories/
│   ├── PropertyRepository.ts
│   ├── TenantRepository.ts
│   ├── LeaseContractRepository.ts
│   ├── PaymentRepository.ts
│   └── MaintenanceRequestRepository.ts
├── services/
│   ├── PropertyService.ts
│   ├── TenantService.ts
│   ├── LeaseContractService.ts
│   ├── PaymentService.ts
│   └── MaintenanceRequestService.ts
├── types/
│   ├── common.ts             # Shared types
│   └── errors.ts             # Domain errors
└── index.ts                  # Public API
```

---

### 6. Traceability Matrix

| Requirement | Design Component | Implementation File |
|-------------|------------------|---------------------|
| REQ-RENTAL-001-F001 | DES-RENTAL-001-C001 | src/entities/Property.ts |
| REQ-RENTAL-001-F002 | DES-RENTAL-001-C001 | src/entities/Property.ts |
| REQ-RENTAL-001-F003 | DES-RENTAL-001-C001 | src/services/PropertyService.ts |
| REQ-RENTAL-001-F010 | DES-RENTAL-001-C002 | src/entities/Tenant.ts |
| REQ-RENTAL-001-F011 | DES-RENTAL-001-C002 | src/services/TenantService.ts |
| REQ-RENTAL-001-F020 | DES-RENTAL-001-C003 | src/services/LeaseContractService.ts |
| REQ-RENTAL-001-F021 | DES-RENTAL-001-C003 | src/services/LeaseContractService.ts |
| REQ-RENTAL-001-F022 | DES-RENTAL-001-C003 | src/services/LeaseContractService.ts |
| REQ-RENTAL-001-F030 | DES-RENTAL-001-C004 | src/entities/Payment.ts |
| REQ-RENTAL-001-F031 | DES-RENTAL-001-C004 | src/services/PaymentService.ts |
| REQ-RENTAL-001-F032 | DES-RENTAL-001-C004 | src/services/PaymentService.ts |
| REQ-RENTAL-001-F040 | DES-RENTAL-001-C005 | src/entities/MaintenanceRequest.ts |
| REQ-RENTAL-001-F041 | DES-RENTAL-001-C005 | src/entities/MaintenanceRequest.ts |
| REQ-RENTAL-001-F042 | DES-RENTAL-001-C005 | src/services/MaintenanceRequestService.ts |

---

**Document End**
