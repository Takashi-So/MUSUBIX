/**
 * Best Practices from Self-Learning
 *
 * Codified patterns from Project-07 (Medical Clinic), Project-08 (Property Rental),
 * Project-13 (Budget Tracker), and Project-14 (Ticket Reservation)
 *
 * @see REQ-LEARN-003 - Adaptive Reasoning
 * @module @musubix/core/learning
 */

/**
 * Best practice definition
 */
export interface BestPractice {
  id: string;
  name: string;
  category: 'code' | 'design' | 'test' | 'requirement';
  action: 'prefer' | 'avoid' | 'suggest';
  description: string;
  example?: string;
  antiPattern?: string;
  confidence: number;
  source: string;
}

/**
 * Codified best practices from learning feedback
 *
 * These patterns were extracted from successful project implementations
 */
export const LEARNED_BEST_PRACTICES: BestPractice[] = [
  // Code Patterns
  {
    id: 'BP-CODE-001',
    name: 'Entity Input DTO',
    category: 'code',
    action: 'prefer',
    description:
      'Use Input DTO objects for entity creation functions instead of multiple parameters',
    example: `
// ✅ Prefer: Input DTO
interface CreatePatientInput {
  name: PersonName;
  dateOfBirth: Date;
  contact: ContactInfo;
}
function createPatient(input: CreatePatientInput): Patient {
  // ...
}

// ❌ Avoid: Multiple parameters
function createPatient(
  name: PersonName,
  dateOfBirth: Date,
  contact: ContactInfo
): Patient {
  // ...
}`,
    antiPattern: 'Using multiple positional parameters for entity creation',
    confidence: 0.95,
    source: 'Project-07 Medical Clinic, Project-08 Property Rental',
  },
  {
    id: 'BP-CODE-002',
    name: 'Date-based ID Format',
    category: 'code',
    action: 'prefer',
    description:
      'Use PREFIX-YYYYMMDD-NNN format for entity IDs to ensure sortability and uniqueness',
    example: `
// ✅ Prefer: Date-based ID
function generatePatientId(): PatientId {
  const dateStr = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  const seq = String(++counter).padStart(3, '0');
  return \`PAT-\${dateStr}-\${seq}\` as PatientId;
}
// Result: PAT-20260104-001

// ❌ Avoid: UUID or sequential-only
function generatePatientId(): string {
  return crypto.randomUUID();  // Not sortable by date
}`,
    antiPattern: 'Using UUIDs or simple sequential numbers without date context',
    confidence: 0.90,
    source: 'Project-07 Medical Clinic, Project-08 Property Rental',
  },
  {
    id: 'BP-CODE-003',
    name: 'Value Objects for Domain Concepts',
    category: 'code',
    action: 'prefer',
    description:
      'Create dedicated Value Object types for domain concepts like PersonName, Money, Address',
    example: `
// ✅ Prefer: Value Objects
interface PersonName {
  firstName: string;
  lastName: string;
  firstNameKana: string;
  lastNameKana: string;
}

interface Money {
  amount: number;
  currency: string;
}

// ❌ Avoid: Primitive types
interface Patient {
  firstName: string;  // Lose semantic meaning
  lastName: string;
  income: number;     // Currency unclear
}`,
    antiPattern: 'Using primitive types for domain concepts',
    confidence: 0.90,
    source: 'Project-07 Medical Clinic, Project-08 Property Rental',
  },
  {
    id: 'BP-CODE-004',
    name: 'Function-based Value Objects',
    category: 'code',
    action: 'prefer',
    description:
      'Use interface + factory function pattern instead of classes for Value Objects to improve TypeScript compatibility',
    example: `
// ✅ Prefer: Interface + Factory Function
interface Price {
  readonly amount: number;
  readonly currency: 'JPY';
}

function createPrice(amount: number): Result<Price, ValidationError> {
  if (amount < 100 || amount > 1_000_000) {
    return err(new ValidationError('Price must be between 100 and 1,000,000 JPY'));
  }
  return ok({ amount, currency: 'JPY' });
}

// Helper functions
function addPrices(a: Price, b: Price): Price { ... }
function formatPrice(price: Price): string { ... }

// ❌ Avoid: Class-based Value Objects
class Price {
  private constructor(readonly amount: number) {}
  static create(amount: number): Price { ... }
}`,
    antiPattern: 'Using classes for Value Objects which causes import/structural typing issues',
    confidence: 0.95,
    source: 'Project-13 Budget Tracker, Project-14 Ticket Reservation',
  },
  {
    id: 'BP-CODE-005',
    name: 'Result Type for Fallible Operations',
    category: 'code',
    action: 'prefer',
    description:
      'Use Rust-inspired Result<T, E> type with ok/err for explicit error handling instead of exceptions',
    example: `
// ✅ Prefer: Result type
type Result<T, E> = { isOk(): this is Ok<T>; isErr(): this is Err<E> };

function createReservation(input: CreateReservationInput): Result<Reservation, ValidationError> {
  if (input.seatIds.length > 10) {
    return err(new ValidationError('Maximum 10 seats per reservation'));
  }
  if (input.seatIds.length === 0) {
    return err(new ValidationError('At least 1 seat required'));
  }
  return ok({ ... });
}

// Usage with type guards
const result = createReservation(input);
if (result.isOk()) {
  console.log('Created:', result.value.id);
} else {
  console.error('Error:', result.error.message);
}

// ❌ Avoid: Throwing exceptions for expected errors
function createReservation(input: CreateReservationInput): Reservation {
  if (input.seatIds.length > 10) {
    throw new Error('Maximum 10 seats');  // Caller may forget to catch
  }
  return { ... };
}`,
    antiPattern: 'Using thrown exceptions for business rule validation failures',
    confidence: 0.95,
    source: 'Project-13 Budget Tracker, Project-14 Ticket Reservation',
  },

  // Design Patterns
  {
    id: 'BP-DESIGN-001',
    name: 'Status Transition Map',
    category: 'design',
    action: 'prefer',
    description:
      'Define valid status transitions using a Map to prevent invalid state changes',
    example: `
// ✅ Prefer: Explicit transition map
const validStatusTransitions: Record<ContractStatus, ContractStatus[]> = {
  draft: ['active'],
  active: ['renewed', 'terminated', 'expired'],
  renewed: [],
  terminated: [],
  expired: ['renewed'],
};

function updateStatus(entity: Entity, newStatus: Status): Entity {
  const allowed = validStatusTransitions[entity.status];
  if (!allowed.includes(newStatus)) {
    throw new Error(\`Invalid transition: \${entity.status} -> \${newStatus}\`);
  }
  return { ...entity, status: newStatus };
}`,
    antiPattern: 'Allowing arbitrary status changes without validation',
    confidence: 0.95,
    source: 'Project-08 Property Rental',
  },
  {
    id: 'BP-DESIGN-002',
    name: 'Repository Async Pattern',
    category: 'design',
    action: 'prefer',
    description:
      'Repository methods should be async to allow future database migration',
    example: `
// ✅ Prefer: Async repository
interface IPatientRepository {
  findById(id: PatientId): Promise<Patient | null>;
  create(patient: Patient): Promise<Patient>;
  update(patient: Patient): Promise<Patient>;
}

class InMemoryPatientRepository implements IPatientRepository {
  async findById(id: PatientId): Promise<Patient | null> {
    return this.patients.get(id) ?? null;
  }
}

// ❌ Avoid: Sync repository
interface IPatientRepository {
  findById(id: PatientId): Patient | null;  // Hard to migrate later
}`,
    antiPattern: 'Using synchronous repository methods',
    confidence: 0.85,
    source: 'Project-08 Property Rental',
  },
  {
    id: 'BP-DESIGN-003',
    name: 'Service Layer with DI',
    category: 'design',
    action: 'prefer',
    description:
      'Encapsulate business logic in Service classes with Repository dependency injection',
    example: `
// ✅ Prefer: Service with DI
class PatientService {
  constructor(
    private patientRepository: IPatientRepository,
    private appointmentRepository: IAppointmentRepository
  ) {}

  async registerPatient(input: CreatePatientInput): Promise<Patient> {
    // Business logic here
    const patient = createPatient(input);
    return this.patientRepository.create(patient);
  }
}`,
    antiPattern: 'Mixing business logic with repository implementation',
    confidence: 0.90,
    source: 'Project-07 Medical Clinic, Project-08 Property Rental',
  },
  {
    id: 'BP-DESIGN-004',
    name: 'Optimistic Locking for Concurrent Updates',
    category: 'design',
    action: 'prefer',
    description:
      'Use version field for optimistic locking to detect concurrent modifications',
    example: `
// ✅ Prefer: Optimistic locking with version field
interface Task {
  id: TaskId;
  title: string;
  status: TaskStatus;
  version: number;  // Incremented on each update
  updatedAt: Date;
}

async function updateTaskStatus(
  taskId: TaskId,
  newStatus: TaskStatus,
  expectedVersion: number
): Promise<Task> {
  const task = await taskRepository.findById(taskId);
  if (task.version !== expectedVersion) {
    throw new ConcurrentUpdateError(
      \`Task \${taskId} was modified by another user. Please refresh and try again.\`
    );
  }
  return taskRepository.save({
    ...task,
    status: newStatus,
    version: task.version + 1,
    updatedAt: new Date()
  });
}

// ❌ Avoid: Last-write-wins without version check
async function updateTaskStatus(taskId: TaskId, newStatus: TaskStatus): Promise<Task> {
  const task = await taskRepository.findById(taskId);
  return taskRepository.save({ ...task, status: newStatus });  // Overwrites others' changes
}`,
    antiPattern: 'Last-write-wins without detecting concurrent modifications',
    confidence: 0.90,
    source: 'Project-10 Project Management (Kanban concurrent updates)',
  },
  {
    id: 'BP-DESIGN-005',
    name: 'AuditService for Data Changes',
    category: 'design',
    action: 'suggest',
    description:
      'Include AuditService in design to log all data modifications for compliance and debugging',
    example: `
// ✅ Prefer: Centralized audit logging
interface AuditLog {
  id: string;
  timestamp: Date;
  userId: string;
  action: 'create' | 'update' | 'delete';
  entityType: string;
  entityId: string;
  changes: Record<string, { old: unknown; new: unknown }>;
}

class AuditService {
  async log(entry: Omit<AuditLog, 'id' | 'timestamp'>): Promise<void> {
    await this.auditRepository.append({
      id: generateAuditId(),
      timestamp: new Date(),
      ...entry
    });
  }
}

// Usage in services
class InventoryService {
  constructor(
    private inventoryRepo: IInventoryRepository,
    private auditService: AuditService
  ) {}

  async adjustStock(productId: string, delta: number, userId: string): Promise<void> {
    const product = await this.inventoryRepo.findById(productId);
    const oldQuantity = product.quantity;
    product.quantity += delta;
    await this.inventoryRepo.save(product);
    await this.auditService.log({
      userId,
      action: 'update',
      entityType: 'Product',
      entityId: productId,
      changes: { quantity: { old: oldQuantity, new: product.quantity } }
    });
  }
}`,
    antiPattern: 'No audit trail for data modifications',
    confidence: 0.85,
    source: 'Project-09 Inventory Management, Project-10 Project Management',
  },
  {
    id: 'BP-DESIGN-006',
    name: 'Entity Counter Reset for Testing',
    category: 'design',
    action: 'prefer',
    description:
      'Include resetXxxCounter() functions in entity modules to enable deterministic test ordering',
    example: `
// Entity module (event.ts)
let eventCounter = 0;

export function createEvent(input: CreateEventInput): Result<Event, ValidationError> {
  const id = generateEventId();
  // ...
}

function generateEventId(): EventId {
  const dateStr = formatDate(new Date());
  return \`EVT-\${dateStr}-\${String(++eventCounter).padStart(3, '0')}\` as EventId;
}

// ✅ Export reset function for tests
export function resetEventCounter(): void {
  eventCounter = 0;
}

// Test file
import { createEvent, resetEventCounter } from './event.js';

beforeEach(() => {
  resetEventCounter();  // Ensure predictable IDs
});

it('should create event with ID EVT-...-001', () => {
  const result = createEvent(input);
  expect(result.value.id).toContain('-001');  // Always 001 in this test
});`,
    antiPattern: 'Tests depending on counter state from previous tests causing flaky results',
    confidence: 0.95,
    source: 'Project-13 Budget Tracker, Project-14 Ticket Reservation',
  },
  {
    id: 'BP-DESIGN-007',
    name: 'Expiry Time Business Logic',
    category: 'design',
    action: 'prefer',
    description:
      'Implement expiry logic with configurable duration and explicit validation functions',
    example: `
// ✅ Prefer: Explicit expiry logic
const RESERVATION_EXPIRY_MINUTES = 15;

interface Reservation {
  id: ReservationId;
  status: ReservationStatus;
  createdAt: Date;
  expiresAt: Date;  // Explicit expiry timestamp
}

export function isReservationExpired(reservation: Reservation): boolean {
  return reservation.status === 'pending' && new Date() > reservation.expiresAt;
}

export function expireReservation(reservation: Reservation): Result<Reservation, Error> {
  if (!isReservationExpired(reservation)) {
    return err(new Error('Reservation has not expired yet'));
  }
  return ok({ ...reservation, status: 'expired' });
}`,
    antiPattern: 'Calculating expiry on-the-fly without storing explicit expiresAt timestamp',
    confidence: 0.90,
    source: 'Project-14 Ticket Reservation',
  },

  // Test Patterns
  {
    id: 'BP-TEST-001',
    name: 'Test Counter Reset',
    category: 'test',
    action: 'prefer',
    description:
      'Provide resetXxxCounter() functions for ID generators and reset in beforeEach',
    example: `
// Entity file
let patientCounter = 0;

export function generatePatientId(): PatientId {
  return \`PAT-...-\${String(++patientCounter).padStart(3, '0')}\`;
}

export function resetPatientCounter(): void {
  patientCounter = 0;
}

// Test file
beforeEach(() => {
  resetPatientCounter();
  resetAppointmentCounter();
});

it('should create patient with ID PAT-...-001', () => {
  const patient = createPatient(input);
  expect(patient.id).toContain('-001');  // Predictable!
});`,
    antiPattern: 'Tests depending on counter state from previous tests',
    confidence: 0.95,
    source: 'Project-07 Medical Clinic',
  },
  {
    id: 'BP-TEST-002',
    name: 'Verify API Before Test',
    category: 'test',
    action: 'suggest',
    description:
      'Before writing tests, verify the actual entity API signatures to avoid mismatches',
    example: `
// ✅ First: Check entity signature
// Entity file shows:
// export function createPatient(input: CreatePatientInput): Patient

// Then: Write test with correct signature
const validInput: CreatePatientInput = {
  name: { firstName: '太郎', lastName: '山田', ... },
  contact: { phone: '090-...', email: '...' },
  ...
};
const patient = createPatient(validInput);

// ❌ Avoid: Assuming parameter signature
const patient = createPatient('太郎', '山田', ...);  // Wrong!`,
    antiPattern: 'Writing tests without verifying actual function signatures',
    confidence: 0.80,
    source: 'Project-08 Property Rental (learned from test failures)',
  },
  {
    id: 'BP-TEST-003',
    name: 'Vitest ESM Configuration',
    category: 'test',
    action: 'prefer',
    description:
      'Use Vitest with TypeScript ESM modules for modern test configuration',
    example: `
// vitest.config.ts
export default defineConfig({
  test: {
    globals: true,
    environment: 'node',
    include: ['__tests__/**/*.test.ts'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
    },
  },
});

// tsconfig.json
{
  "compilerOptions": {
    "module": "NodeNext",
    "moduleResolution": "NodeNext",
    "target": "ES2022"
  }
}`,
    antiPattern: 'Using CommonJS or outdated Jest configuration',
    confidence: 0.85,
    source: 'Project-07 Medical Clinic',
  },
  {
    id: 'BP-TEST-004',
    name: 'Result Type Test Pattern',
    category: 'test',
    action: 'prefer',
    description:
      'Test both success (isOk) and failure (isErr) cases with type guards for Result types',
    example: `
// ✅ Prefer: Explicit Result type testing
describe('createPrice', () => {
  it('should create valid price', () => {
    const result = createPrice(1000);
    expect(result.isOk()).toBe(true);
    if (result.isOk()) {
      expect(result.value.amount).toBe(1000);
      expect(result.value.currency).toBe('JPY');
    }
  });

  it('should reject price below minimum', () => {
    const result = createPrice(50);
    expect(result.isErr()).toBe(true);
    if (result.isErr()) {
      expect(result.error.message).toContain('100');
    }
  });
});

// ❌ Avoid: Not checking Result state properly
it('should create price', () => {
  const result = createPrice(1000);
  expect(result.value.amount).toBe(1000);  // May fail if isErr!
});`,
    antiPattern: 'Accessing Result.value without checking isOk() first',
    confidence: 0.95,
    source: 'Project-13 Budget Tracker, Project-14 Ticket Reservation',
  },
  {
    id: 'BP-TEST-005',
    name: 'Status Transition Testing',
    category: 'test',
    action: 'prefer',
    description:
      'Test all valid and invalid status transitions systematically',
    example: `
// ✅ Prefer: Comprehensive transition testing
describe('status transitions', () => {
  // Valid transitions
  it('should transition from draft to active', () => {
    const event = createEvent(input).value;
    const result = activateEvent(event);
    expect(result.isOk()).toBe(true);
  });

  // Invalid transitions
  it('should reject transition from completed to active', () => {
    const event = { ...createEvent(input).value, status: 'completed' };
    const result = activateEvent(event);
    expect(result.isErr()).toBe(true);
    expect(result.error.message).toContain('Invalid status transition');
  });

  // All valid paths
  const validTransitions = [
    ['draft', 'active'],
    ['draft', 'cancelled'],
    ['active', 'completed'],
    ['active', 'cancelled'],
  ];

  validTransitions.forEach(([from, to]) => {
    it(\`should allow \${from} -> \${to}\`, () => { ... });
  });
});`,
    antiPattern: 'Testing only happy path transitions',
    confidence: 0.90,
    source: 'Project-14 Ticket Reservation',
  },
];

/**
 * Get best practices by category
 */
export function getBestPracticesByCategory(
  category: BestPractice['category']
): BestPractice[] {
  return LEARNED_BEST_PRACTICES.filter((bp) => bp.category === category);
}

/**
 * Get best practices by action
 */
export function getBestPracticesByAction(
  action: BestPractice['action']
): BestPractice[] {
  return LEARNED_BEST_PRACTICES.filter((bp) => bp.action === action);
}

/**
 * Get all prefer patterns
 */
export function getPreferredPatterns(): BestPractice[] {
  return getBestPracticesByAction('prefer');
}

/**
 * Get all avoid patterns
 */
export function getAntiPatterns(): BestPractice[] {
  return getBestPracticesByAction('avoid');
}

/**
 * Get high confidence patterns (≥0.9)
 */
export function getHighConfidencePatterns(): BestPractice[] {
  return LEARNED_BEST_PRACTICES.filter((bp) => bp.confidence >= 0.9);
}

/**
 * Format best practice for display
 */
export function formatBestPractice(bp: BestPractice): string {
  const actionIcon =
    bp.action === 'prefer' ? '✅' : bp.action === 'avoid' ? '❌' : '💡';
  const confidence = `${Math.round(bp.confidence * 100)}%`;

  let output = `${actionIcon} **${bp.name}** (${bp.category}, ${confidence})\n\n`;
  output += `${bp.description}\n`;

  if (bp.example) {
    output += `\n**Example:**\n\`\`\`typescript\n${bp.example.trim()}\n\`\`\`\n`;
  }

  if (bp.antiPattern) {
    output += `\n**Anti-pattern:** ${bp.antiPattern}\n`;
  }

  output += `\n*Source: ${bp.source}*\n`;

  return output;
}

/**
 * Generate best practices report
 */
export function generateBestPracticesReport(): string {
  let report = '# MUSUBIX Learned Best Practices\n\n';
  report += `*Generated from self-learning feedback*\n\n`;
  report += `**Total Patterns:** ${LEARNED_BEST_PRACTICES.length}\n`;
  report += `**High Confidence (≥90%):** ${getHighConfidencePatterns().length}\n\n`;

  const categories: BestPractice['category'][] = [
    'code',
    'design',
    'test',
    'requirement',
  ];

  for (const category of categories) {
    const patterns = getBestPracticesByCategory(category);
    if (patterns.length === 0) continue;

    report += `## ${category.charAt(0).toUpperCase() + category.slice(1)} Patterns\n\n`;

    for (const bp of patterns) {
      report += formatBestPractice(bp);
      report += '\n---\n\n';
    }
  }

  return report;
}
