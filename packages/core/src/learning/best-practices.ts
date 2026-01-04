/**
 * Best Practices from Self-Learning
 *
 * Codified patterns from Project-07 (Medical Clinic) and Project-08 (Property Rental)
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
    source: 'Project-08 Property Rental',
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
