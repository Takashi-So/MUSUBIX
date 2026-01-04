# Design Document: Property Rental Management System
## DES-RENTAL-001 v1.1.0

### 1. Document Information

| Item | Value |
|------|-------|
| **Version** | 1.1.0 |
| **Status** | Approved |
| **Created** | 2026-01-04 |
| **Author** | MUSUBIX SDD System |
| **Requirements** | REQ-RENTAL-001 v1.1.0 |

---

### 2. Design Overview

#### 2.1 Architecture Style
**Microservices Architecture** with Domain-Driven Design (DDD) principles

#### 2.2 Design Patterns Applied

| Pattern | Usage | Rationale |
|---------|-------|-----------|
| **Repository** | Data access abstraction | Decouple domain from persistence |
| **Service Layer** | Business logic encapsulation | Separation of concerns |
| **Factory** | Entity creation | Complex object instantiation |
| **Strategy** | Payment/Fee calculation | Multiple calculation algorithms |
| **Observer** | Notification system | Loose coupling for events |
| **Specification** | Search criteria | Flexible query composition |

---

### 3. C4 Model

#### 3.1 Level 1: System Context

```
┌─────────────────────────────────────────────────────────────────┐
│                        External Systems                          │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────────┐ │
│  │ Payment  │  │  Email   │  │ Document │  │  Credit Check    │ │
│  │ Gateway  │  │ Service  │  │ Storage  │  │  Service         │ │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────────┬─────────┘ │
└───────┼─────────────┼────────────┼──────────────────┼───────────┘
        │             │            │                  │
        └─────────────┴────────────┴──────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│              Property Rental Management System                   │
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    API Gateway                           │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                   │
│  ┌──────────┬──────────┬─────┴────┬──────────┬──────────────┐   │
│  │ Property │  Tenant  │ Contract │ Payment  │ Maintenance  │   │
│  │ Service  │ Service  │ Service  │ Service  │   Service    │   │
│  └──────────┴──────────┴──────────┴──────────┴──────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                              │
        ┌─────────────────────┴─────────────────────┐
        ▼                     ▼                     ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────────┐
│   Property   │    │    Tenant    │    │  Property        │
│    Owner     │    │   (Tenant)   │    │  Manager         │
└──────────────┘    └──────────────┘    └──────────────────┘
```

#### 3.2 Level 2: Container Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                Property Rental Management System                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │                     Web Application (SPA)                       │ │
│  │                     [React + TypeScript]                        │ │
│  └────────────────────────────────┬───────────────────────────────┘ │
│                                   │ HTTPS/REST                       │
│  ┌────────────────────────────────▼───────────────────────────────┐ │
│  │                       API Gateway                               │ │
│  │                    [Node.js + Express]                          │ │
│  │           Authentication, Rate Limiting, Routing                │ │
│  └────────────────────────────────┬───────────────────────────────┘ │
│                                   │                                  │
│  ┌────────────┬───────────┬───────┴────┬───────────┬─────────────┐  │
│  │            │           │            │           │             │  │
│  ▼            ▼           ▼            ▼           ▼             │  │
│ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌──────────┐        │  │
│ │Property│ │ Tenant │ │Contract│ │Payment │ │Maintenan.│        │  │
│ │Service │ │Service │ │Service │ │Service │ │ Service  │        │  │
│ │[Node]  │ │[Node]  │ │[Node]  │ │[Node]  │ │ [Node]   │        │  │
│ └───┬────┘ └───┬────┘ └───┬────┘ └───┬────┘ └────┬─────┘        │  │
│     │          │          │          │           │               │  │
│     └──────────┴──────────┴────┬─────┴───────────┘               │  │
│                                │                                  │  │
│  ┌─────────────────────────────▼─────────────────────────────────┐ │
│  │                      PostgreSQL Database                       │ │
│  │              Properties, Tenants, Contracts, Payments          │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────────┐   │
│  │   Redis Cache    │  │  Message Queue   │  │  Audit Logger    │   │
│  │   [Sessions]     │  │  [Bull/Redis]    │  │  [Elasticsearch] │   │
│  └──────────────────┘  └──────────────────┘  └──────────────────┘   │
└─────────────────────────────────────────────────────────────────────┘
```

---

### 4. Domain Model

#### 4.1 Core Entities

##### 4.1.1 Property Entity
```typescript
interface Property {
  id: string;                    // PROP-YYYYMMDD-NNN
  ownerId: string;               // Reference to PropertyOwner
  address: Address;              // Embedded value object
  propertyType: PropertyType;    // apartment | house | condominium
  sizeSqm: number;               // Size in square meters
  monthlyRent: Money;            // Monthly rent amount
  deposit: Money;                // 敷金
  keyMoney: Money;               // 礼金
  maintenanceFee: Money;         // 管理費
  amenities: Amenity[];          // Parking, pet-friendly, etc.
  status: PropertyStatus;        // available | pending | occupied | maintenance
  description?: string;
  photos: string[];              // URLs to photos
  createdAt: Date;
  updatedAt: Date;
}

type PropertyStatus = 'available' | 'pending' | 'occupied' | 'maintenance';
type PropertyType = 'apartment' | 'house' | 'condominium' | 'studio';
```

##### 4.1.2 Tenant Entity
```typescript
interface Tenant {
  id: string;                    // TEN-YYYYMMDD-NNN
  name: PersonName;              // Full name with furigana
  contact: ContactInfo;          // Phone, email, address
  identification: Identification; // ID type and number
  employment: EmploymentInfo;    // Employer, income
  emergencyContact: ContactInfo;
  guarantorId?: string;          // Reference to Guarantor
  status: TenantStatus;
  createdAt: Date;
  updatedAt: Date;
}

type TenantStatus = 'active' | 'inactive' | 'blacklisted';
```

##### 4.1.3 Guarantor Entity
```typescript
interface Guarantor {
  id: string;                    // GUA-YYYYMMDD-NNN
  tenantId: string;              // Reference to Tenant
  name: PersonName;
  relationship: string;          // 続柄
  contact: ContactInfo;
  employment: EmploymentInfo;
  consentDate: Date;
  createdAt: Date;
  updatedAt: Date;
}
```

##### 4.1.4 LeaseContract Entity
```typescript
interface LeaseContract {
  id: string;                    // LEASE-YYYYMMDD-NNN
  propertyId: string;
  tenantId: string;
  guarantorId?: string;
  startDate: Date;
  endDate: Date;
  monthlyRent: Money;
  deposit: Money;
  keyMoney: Money;
  maintenanceFee: Money;
  renewalFee?: Money;            // 更新料
  specialConditions?: string;
  status: ContractStatus;
  createdAt: Date;
  updatedAt: Date;
}

type ContractStatus = 'draft' | 'active' | 'expiring' | 'terminated' | 'renewed';
```

##### 4.1.5 Payment Entity
```typescript
interface Payment {
  id: string;                    // PAY-YYYYMMDD-NNN
  contractId: string;
  tenantId: string;
  amount: Money;
  paymentType: PaymentType;      // rent | deposit | key_money | maintenance | late_fee
  paymentMethod: PaymentMethod;  // bank_transfer | credit_card | cash
  dueDate: Date;
  paidDate?: Date;
  status: PaymentStatus;
  lateFee?: Money;
  createdAt: Date;
  updatedAt: Date;
}

type PaymentStatus = 'pending' | 'paid' | 'overdue' | 'partial' | 'waived';
type PaymentType = 'rent' | 'deposit' | 'key_money' | 'maintenance' | 'late_fee' | 'renewal';
```

##### 4.1.6 MaintenanceRequest Entity
```typescript
interface MaintenanceRequest {
  id: string;                    // MNT-YYYYMMDD-NNN
  propertyId: string;
  tenantId: string;
  description: string;
  urgency: UrgencyLevel;
  photos: string[];
  status: MaintenanceStatus;
  assignedTo?: string;           // Staff ID
  scheduledDate?: Date;
  completedDate?: Date;
  cost?: Money;
  costResponsibility: 'owner' | 'tenant';
  notes?: string;
  createdAt: Date;
  updatedAt: Date;
}

type UrgencyLevel = 'emergency' | 'high' | 'medium' | 'low';
type MaintenanceStatus = 'submitted' | 'assigned' | 'scheduled' | 'in_progress' | 'completed' | 'closed';
```

##### 4.1.7 Application Entity
```typescript
interface RentalApplication {
  id: string;                    // APP-YYYYMMDD-NNN
  propertyId: string;
  tenantId: string;
  guarantorId?: string;
  status: ApplicationStatus;
  submittedAt: Date;
  screeningResult?: ScreeningResult;
  rejectionReason?: string;
  createdAt: Date;
  updatedAt: Date;
}

type ApplicationStatus = 'submitted' | 'screening' | 'approved' | 'rejected' | 'withdrawn';
```

##### 4.1.8 PropertyOwner Entity
```typescript
interface PropertyOwner {
  id: string;                    // OWN-YYYYMMDD-NNN
  name: PersonName;              // Full name with furigana (individual) or company name
  ownerType: OwnerType;          // individual | corporation
  contact: ContactInfo;
  bankAccount: BankAccount;      // For rent deposit
  taxId?: string;                // 法人番号 or マイナンバー (encrypted)
  properties: string[];          // List of property IDs
  status: OwnerStatus;
  createdAt: Date;
  updatedAt: Date;
}

type OwnerType = 'individual' | 'corporation';
type OwnerStatus = 'active' | 'inactive';

interface BankAccount {
  bankName: string;
  branchName: string;
  accountType: 'ordinary' | 'checking';  // 普通 | 当座
  accountNumber: string;         // Encrypted
  accountHolder: string;
}
```

#### 4.2 Value Objects

```typescript
interface Address {
  postalCode: string;            // 郵便番号
  prefecture: string;            // 都道府県
  city: string;                  // 市区町村
  street: string;                // 町名・番地
  building?: string;             // 建物名・部屋番号
}

interface PersonName {
  firstName: string;
  lastName: string;
  firstNameKana: string;         // フリガナ
  lastNameKana: string;
}

interface ContactInfo {
  phone: string;
  email: string;
  address: Address;
}

interface Money {
  amount: number;
  currency: 'JPY';
}

interface EmploymentInfo {
  employerName: string;
  position?: string;
  annualIncome: Money;
  yearsEmployed?: number;
}

interface Identification {
  type: 'drivers_license' | 'passport' | 'residence_card' | 'my_number';
  number: string;                // Encrypted
  issuedDate?: Date;
  expiryDate?: Date;
}
```

---

### 5. Component Design

#### 5.1 Property Service

```
┌─────────────────────────────────────────────────────────────┐
│                      Property Service                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │                  PropertyController                   │  │
│  │  - POST /properties                                   │  │
│  │  - GET  /properties/:id                               │  │
│  │  - GET  /properties/search                            │  │
│  │  - PUT  /properties/:id                               │  │
│  │  - PUT  /properties/:id/status                        │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                  PropertyService                      │  │
│  │  @REQ-RENTAL-001-F001 registerProperty()              │  │
│  │  @REQ-RENTAL-001-F002 searchProperties()              │  │
│  │  @REQ-RENTAL-001-F003 updateAvailability()            │  │
│  │                       getPropertyDetails()            │  │
│  │                       listOwnerProperties()           │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │              IPropertyRepository                      │  │
│  │  - create(property: CreatePropertyDTO)                │  │
│  │  - findById(id: string)                               │  │
│  │  - findByOwner(ownerId: string)                       │  │
│  │  - search(criteria: SearchCriteria)                   │  │
│  │  - update(id: string, data: UpdatePropertyDTO)        │  │
│  │  - updateStatus(id: string, status: PropertyStatus)   │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

#### 5.2 Tenant Service

```
┌─────────────────────────────────────────────────────────────┐
│                       Tenant Service                         │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │                   TenantController                    │  │
│  │  - POST /tenants                                      │  │
│  │  - GET  /tenants/:id                                  │  │
│  │  - PUT  /tenants/:id                                  │  │
│  │  - POST /tenants/:id/guarantor                        │  │
│  │  - POST /applications                                 │  │
│  │  - PUT  /applications/:id/status                      │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                   TenantService                       │  │
│  │  @REQ-RENTAL-001-F010 registerTenant()                │  │
│  │  @REQ-RENTAL-001-F011 submitApplication()             │  │
│  │  @REQ-RENTAL-001-F012 initiateScreening()             │  │
│  │  @REQ-RENTAL-001-F013 addGuarantor()                  │  │
│  │                       getTenantDetails()              │  │
│  │                       updateApplicationStatus()       │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │       ITenantRepository / IApplicationRepository      │  │
│  │       IGuarantorRepository                            │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

#### 5.3 Contract Service

```
┌─────────────────────────────────────────────────────────────┐
│                      Contract Service                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │                  ContractController                   │  │
│  │  - POST /contracts                                    │  │
│  │  - GET  /contracts/:id                                │  │
│  │  - PUT  /contracts/:id/renew                          │  │
│  │  - PUT  /contracts/:id/terminate                      │  │
│  │  - GET  /contracts/expiring                           │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                  ContractService                      │  │
│  │  @REQ-RENTAL-001-F020 createContract()                │  │
│  │  @REQ-RENTAL-001-F021 checkExpiringContracts()        │  │
│  │  @REQ-RENTAL-001-F021 renewContract()                 │  │
│  │  @REQ-RENTAL-001-F022 terminateContract()             │  │
│  │                       calculateSettlement()           │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                IContractRepository                    │  │
│  │  - create(contract: CreateContractDTO)                │  │
│  │  - findById(id: string)                               │  │
│  │  - findByTenant(tenantId: string)                     │  │
│  │  - findByProperty(propertyId: string)                 │  │
│  │  - findExpiring(withinDays: number)                   │  │
│  │  - update(id: string, data: UpdateContractDTO)        │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

#### 5.4 Payment Service

```
┌─────────────────────────────────────────────────────────────┐
│                       Payment Service                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │                  PaymentController                    │  │
│  │  - POST /payments                                     │  │
│  │  - GET  /payments/:id                                 │  │
│  │  - GET  /payments/tenant/:tenantId                    │  │
│  │  - GET  /payments/overdue                             │  │
│  │  - POST /payments/:id/reminder                        │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                  PaymentService                       │  │
│  │  @REQ-RENTAL-001-F030 recordPayment()                 │  │
│  │  @REQ-RENTAL-001-F031 sendReminder()                  │  │
│  │  @REQ-RENTAL-001-F032 calculateLateFee()              │  │
│  │  @REQ-RENTAL-001-F033 getPaymentHistory()             │  │
│  │                       generateMonthlyInvoices()       │  │
│  │                       processOverduePayments()        │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                  LateFeeStrategy                      │  │
│  │  - StandardLateFeeStrategy (14.6% annual)             │  │
│  │  - CustomLateFeeStrategy                              │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

#### 5.5 Maintenance Service

```
┌─────────────────────────────────────────────────────────────┐
│                    Maintenance Service                       │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │                MaintenanceController                  │  │
│  │  - POST /maintenance                                  │  │
│  │  - GET  /maintenance/:id                              │  │
│  │  - PUT  /maintenance/:id/status                       │  │
│  │  - PUT  /maintenance/:id/assign                       │  │
│  │  - PUT  /maintenance/:id/complete                     │  │
│  │  - GET  /maintenance/property/:propertyId             │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                MaintenanceService                     │  │
│  │  @REQ-RENTAL-001-F040 submitRequest()                 │  │
│  │  @REQ-RENTAL-001-F041 updateStatus()                  │  │
│  │  @REQ-RENTAL-001-F042 assignCostResponsibility()      │  │
│  │                       assignStaff()                   │  │
│  │                       scheduleWork()                  │  │
│  │                       completeRequest()               │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │              IMaintenanceRepository                   │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

#### 5.6 Reporting Service

```
┌─────────────────────────────────────────────────────────────┐
│                     Reporting Service                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │                 ReportingController                   │  │
│  │  - GET /reports/revenue/:ownerId                      │  │
│  │  - GET /reports/occupancy                             │  │
│  │  - GET /reports/payments/:period                      │  │
│  └────────────────────────┬─────────────────────────────┘  │
│                           │                                  │
│  ┌────────────────────────▼─────────────────────────────┐  │
│  │                 ReportingService                      │  │
│  │  @REQ-RENTAL-001-F050 generateRevenueReport()         │  │
│  │  @REQ-RENTAL-001-F051 generateOccupancyReport()       │  │
│  │                       generatePaymentReport()         │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

### 6. Database Schema

#### 6.1 Properties Table
```sql
CREATE TABLE properties (
    id VARCHAR(20) PRIMARY KEY,           -- PROP-YYYYMMDD-NNN
    owner_id VARCHAR(50) NOT NULL,
    postal_code VARCHAR(10) NOT NULL,
    prefecture VARCHAR(20) NOT NULL,
    city VARCHAR(50) NOT NULL,
    street VARCHAR(100) NOT NULL,
    building VARCHAR(100),
    property_type VARCHAR(20) NOT NULL,
    size_sqm DECIMAL(10,2) NOT NULL,
    monthly_rent INTEGER NOT NULL,
    deposit INTEGER NOT NULL,
    key_money INTEGER DEFAULT 0,
    maintenance_fee INTEGER DEFAULT 0,
    status VARCHAR(20) DEFAULT 'available',
    description TEXT,
    amenities JSONB DEFAULT '[]',
    photos JSONB DEFAULT '[]',
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.2 Tenants Table
```sql
CREATE TABLE tenants (
    id VARCHAR(20) PRIMARY KEY,           -- TEN-YYYYMMDD-NNN
    first_name VARCHAR(50) NOT NULL,
    last_name VARCHAR(50) NOT NULL,
    first_name_kana VARCHAR(50) NOT NULL,
    last_name_kana VARCHAR(50) NOT NULL,
    phone VARCHAR(20) NOT NULL,
    email VARCHAR(100) NOT NULL UNIQUE,
    current_address JSONB NOT NULL,
    identification_type VARCHAR(30) NOT NULL,
    identification_number_encrypted BYTEA NOT NULL,
    employer_name VARCHAR(100),
    annual_income INTEGER,
    emergency_contact JSONB NOT NULL,
    guarantor_id VARCHAR(20),
    status VARCHAR(20) DEFAULT 'active',
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.3 Guarantors Table
```sql
CREATE TABLE guarantors (
    id VARCHAR(20) PRIMARY KEY,           -- GUA-YYYYMMDD-NNN
    tenant_id VARCHAR(20) NOT NULL REFERENCES tenants(id),
    first_name VARCHAR(50) NOT NULL,
    last_name VARCHAR(50) NOT NULL,
    first_name_kana VARCHAR(50),
    last_name_kana VARCHAR(50),
    relationship VARCHAR(30) NOT NULL,
    phone VARCHAR(20) NOT NULL,
    email VARCHAR(100),
    address JSONB NOT NULL,
    employer_name VARCHAR(100),
    annual_income INTEGER,
    consent_date DATE NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.4 Lease Contracts Table
```sql
CREATE TABLE lease_contracts (
    id VARCHAR(20) PRIMARY KEY,           -- LEASE-YYYYMMDD-NNN
    property_id VARCHAR(20) NOT NULL REFERENCES properties(id),
    tenant_id VARCHAR(20) NOT NULL REFERENCES tenants(id),
    guarantor_id VARCHAR(20) REFERENCES guarantors(id),
    start_date DATE NOT NULL,
    end_date DATE NOT NULL,
    monthly_rent INTEGER NOT NULL,
    deposit INTEGER NOT NULL,
    key_money INTEGER DEFAULT 0,
    maintenance_fee INTEGER DEFAULT 0,
    renewal_fee INTEGER,
    special_conditions TEXT,
    status VARCHAR(20) DEFAULT 'draft',
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.5 Payments Table
```sql
CREATE TABLE payments (
    id VARCHAR(20) PRIMARY KEY,           -- PAY-YYYYMMDD-NNN
    contract_id VARCHAR(20) NOT NULL REFERENCES lease_contracts(id),
    tenant_id VARCHAR(20) NOT NULL REFERENCES tenants(id),
    amount INTEGER NOT NULL,
    payment_type VARCHAR(20) NOT NULL,
    payment_method VARCHAR(20),
    due_date DATE NOT NULL,
    paid_date DATE,
    status VARCHAR(20) DEFAULT 'pending',
    late_fee INTEGER DEFAULT 0,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.6 Maintenance Requests Table
```sql
CREATE TABLE maintenance_requests (
    id VARCHAR(20) PRIMARY KEY,           -- MNT-YYYYMMDD-NNN
    property_id VARCHAR(20) NOT NULL REFERENCES properties(id),
    tenant_id VARCHAR(20) NOT NULL REFERENCES tenants(id),
    description TEXT NOT NULL,
    urgency VARCHAR(20) NOT NULL,
    photos JSONB DEFAULT '[]',
    status VARCHAR(20) DEFAULT 'submitted',
    assigned_to VARCHAR(50),
    scheduled_date DATE,
    completed_date DATE,
    cost INTEGER,
    cost_responsibility VARCHAR(10) DEFAULT 'owner',
    notes TEXT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.7 Rental Applications Table
```sql
CREATE TABLE rental_applications (
    id VARCHAR(20) PRIMARY KEY,           -- APP-YYYYMMDD-NNN
    property_id VARCHAR(20) NOT NULL REFERENCES properties(id),
    tenant_id VARCHAR(20) NOT NULL REFERENCES tenants(id),
    guarantor_id VARCHAR(20) REFERENCES guarantors(id),
    status VARCHAR(20) DEFAULT 'submitted',
    submitted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    screening_result JSONB,
    rejection_reason TEXT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.8 Property Owners Table
```sql
CREATE TABLE property_owners (
    id VARCHAR(20) PRIMARY KEY,           -- OWN-YYYYMMDD-NNN
    first_name VARCHAR(50),
    last_name VARCHAR(50),
    first_name_kana VARCHAR(50),
    last_name_kana VARCHAR(50),
    company_name VARCHAR(100),
    owner_type VARCHAR(20) NOT NULL,      -- individual | corporation
    phone VARCHAR(20) NOT NULL,
    email VARCHAR(100) NOT NULL UNIQUE,
    address JSONB NOT NULL,
    bank_account_encrypted BYTEA,
    tax_id_encrypted BYTEA,
    status VARCHAR(20) DEFAULT 'active',
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.9 Audit Logs Table
```sql
CREATE TABLE audit_logs (
    id BIGSERIAL PRIMARY KEY,
    table_name VARCHAR(50) NOT NULL,
    record_id VARCHAR(50) NOT NULL,
    action VARCHAR(20) NOT NULL,          -- INSERT, UPDATE, DELETE
    user_id VARCHAR(50) NOT NULL,
    old_values JSONB,
    new_values JSONB,
    ip_address VARCHAR(45),
    user_agent TEXT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

#### 6.10 Database Indexes
```sql
-- Properties indexes
CREATE INDEX idx_properties_owner ON properties(owner_id);
CREATE INDEX idx_properties_status ON properties(status);
CREATE INDEX idx_properties_prefecture_city ON properties(prefecture, city);
CREATE INDEX idx_properties_rent ON properties(monthly_rent);
CREATE INDEX idx_properties_type ON properties(property_type);

-- Tenants indexes
CREATE INDEX idx_tenants_email ON tenants(email);
CREATE INDEX idx_tenants_status ON tenants(status);
CREATE INDEX idx_tenants_guarantor ON tenants(guarantor_id);

-- Lease contracts indexes
CREATE INDEX idx_contracts_property ON lease_contracts(property_id);
CREATE INDEX idx_contracts_tenant ON lease_contracts(tenant_id);
CREATE INDEX idx_contracts_status ON lease_contracts(status);
CREATE INDEX idx_contracts_end_date ON lease_contracts(end_date);

-- Payments indexes
CREATE INDEX idx_payments_contract ON payments(contract_id);
CREATE INDEX idx_payments_tenant ON payments(tenant_id);
CREATE INDEX idx_payments_status ON payments(status);
CREATE INDEX idx_payments_due_date ON payments(due_date);

-- Maintenance requests indexes
CREATE INDEX idx_maintenance_property ON maintenance_requests(property_id);
CREATE INDEX idx_maintenance_tenant ON maintenance_requests(tenant_id);
CREATE INDEX idx_maintenance_status ON maintenance_requests(status);
CREATE INDEX idx_maintenance_urgency ON maintenance_requests(urgency);

-- Audit logs indexes
CREATE INDEX idx_audit_table_record ON audit_logs(table_name, record_id);
CREATE INDEX idx_audit_user ON audit_logs(user_id);
CREATE INDEX idx_audit_created ON audit_logs(created_at);
```

---

### 7. API Specifications

#### 7.1 Property Endpoints

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| POST | `/api/v1/properties` | Create property | Manager |
| GET | `/api/v1/properties/:id` | Get property details | Public |
| GET | `/api/v1/properties/search` | Search properties | Public |
| PUT | `/api/v1/properties/:id` | Update property | Manager |
| PUT | `/api/v1/properties/:id/status` | Update availability | Manager |
| DELETE | `/api/v1/properties/:id` | Soft delete property | Manager |
| GET | `/api/v1/properties/owner/:ownerId` | List owner properties | Owner |

#### 7.2 Tenant Endpoints

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| POST | `/api/v1/tenants` | Register tenant | Tenant/Manager |
| GET | `/api/v1/tenants/:id` | Get tenant details | Tenant/Manager |
| PUT | `/api/v1/tenants/:id` | Update tenant | Tenant/Manager |
| DELETE | `/api/v1/tenants/:id` | Deactivate tenant | Manager |
| POST | `/api/v1/tenants/:id/guarantor` | Add guarantor | Tenant |
| POST | `/api/v1/applications` | Submit application | Tenant |
| PUT | `/api/v1/applications/:id/status` | Update application | Manager |

#### 7.3 Contract Endpoints

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| POST | `/api/v1/contracts` | Create contract | Manager |
| GET | `/api/v1/contracts/:id` | Get contract | Tenant/Manager |
| PUT | `/api/v1/contracts/:id/renew` | Renew contract | Manager |
| PUT | `/api/v1/contracts/:id/terminate` | Terminate contract | Manager |
| GET | `/api/v1/contracts/expiring` | List expiring contracts | Manager |

#### 7.4 Payment Endpoints

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| POST | `/api/v1/payments` | Record payment | Manager |
| GET | `/api/v1/payments/:id` | Get payment details | Tenant/Manager |
| GET | `/api/v1/payments/tenant/:tenantId` | Payment history | Tenant/Manager |
| GET | `/api/v1/payments/overdue` | List overdue payments | Manager |

#### 7.5 Maintenance Endpoints

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| POST | `/api/v1/maintenance` | Submit request | Tenant |
| GET | `/api/v1/maintenance/:id` | Get request details | Tenant/Manager |
| PUT | `/api/v1/maintenance/:id/status` | Update status | Manager |
| PUT | `/api/v1/maintenance/:id/assign` | Assign staff | Manager |
| GET | `/api/v1/maintenance/property/:propertyId` | List property requests | Manager |

#### 7.6 Reporting Endpoints

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| GET | `/api/v1/reports/revenue/:ownerId` | Owner revenue report | Owner/Manager |
| GET | `/api/v1/reports/occupancy` | Occupancy rate report | Manager |
| GET | `/api/v1/reports/payments` | Payment summary report | Manager |
| GET | `/api/v1/reports/maintenance` | Maintenance summary | Manager |

#### 7.7 Audit & Admin Endpoints

| Method | Endpoint | Description | Auth |
|--------|----------|-------------|------|
| GET | `/api/v1/admin/audit` | Query audit logs | Admin |
| GET | `/api/v1/admin/audit/:recordId` | Get audit trail for record | Admin |
| GET | `/api/v1/admin/users` | List system users | Admin |
| PUT | `/api/v1/admin/users/:id/role` | Update user role | Admin |

---

### 8. Security Design

#### 8.1 Authentication
- JWT-based authentication
- Token expiry: 24 hours
- Refresh token mechanism

#### 8.2 Authorization (RBAC)

| Role | Permissions |
|------|-------------|
| **Owner** | View own properties, View revenue reports |
| **Manager** | Full CRUD on all entities, Approve applications |
| **Tenant** | View own data, Submit applications/maintenance |
| **Admin** | System administration, Audit logs access |

#### 8.3 Data Encryption
- Personal data encrypted at rest (AES-256)
- All API traffic over TLS 1.3
- Identification numbers stored with envelope encryption

---

### 9. Requirements Traceability Matrix

| Requirement | Component | API Endpoint | Status |
|-------------|-----------|--------------|--------|
| REQ-RENTAL-001-F001 | PropertyService.registerProperty | POST /properties | Designed |
| REQ-RENTAL-001-F002 | PropertyService.searchProperties | GET /properties/search | Designed |
| REQ-RENTAL-001-F003 | PropertyService.updateAvailability | PUT /properties/:id/status | Designed |
| REQ-RENTAL-001-F010 | TenantService.registerTenant | POST /tenants | Designed |
| REQ-RENTAL-001-F011 | TenantService.submitApplication | POST /applications | Designed |
| REQ-RENTAL-001-F012 | TenantService.initiateScreening | PUT /applications/:id/status | Designed |
| REQ-RENTAL-001-F013 | TenantService.addGuarantor | POST /tenants/:id/guarantor | Designed |
| REQ-RENTAL-001-F020 | ContractService.createContract | POST /contracts | Designed |
| REQ-RENTAL-001-F021 | ContractService.renewContract | PUT /contracts/:id/renew | Designed |
| REQ-RENTAL-001-F022 | ContractService.terminateContract | PUT /contracts/:id/terminate | Designed |
| REQ-RENTAL-001-F030 | PaymentService.recordPayment | POST /payments | Designed |
| REQ-RENTAL-001-F031 | PaymentService.sendReminder | Scheduled job | Designed |
| REQ-RENTAL-001-F032 | PaymentService.calculateLateFee | Internal | Designed |
| REQ-RENTAL-001-F033 | PaymentService.getPaymentHistory | GET /payments/tenant/:id | Designed |
| REQ-RENTAL-001-F040 | MaintenanceService.submitRequest | POST /maintenance | Designed |
| REQ-RENTAL-001-F041 | MaintenanceService.updateStatus | PUT /maintenance/:id/status | Designed |
| REQ-RENTAL-001-F042 | MaintenanceService.assignCost | PUT /maintenance/:id/complete | Designed |
| REQ-RENTAL-001-F050 | ReportingService.revenueReport | GET /reports/revenue/:ownerId | Designed |
| REQ-RENTAL-001-F051 | ReportingService.occupancyReport | GET /reports/occupancy | Designed |
| REQ-RENTAL-001-NF040 | AuditLogger | Middleware | Designed |
| REQ-RENTAL-001-NF041 | AuditService | GET /admin/audit | Designed |

---

### 10. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-01-04 | MUSUBIX SDD | Initial design document |
| 1.1.0 | 2026-01-04 | MUSUBIX SDD | Added PropertyOwner entity, DELETE endpoints, DB indexes, Reporting/Audit APIs |

---

**Document Status**: ✅ Approved

**Approval Required**: [x] Technical Lead [x] Security Review [x] Architecture Review
