/**
 * Test Fixtures Repository
 *
 * @fileoverview Provides common test data and fixtures
 * @module @musubix/core/testing/test-fixtures
 * @requirement REQ-E2E-001
 */

import type { TestFixtures, EarsRequirementFixture, TripleFixture } from './types.js';

/**
 * Valid EARS requirement samples
 */
const validRequirements: EarsRequirementFixture[] = [
  {
    id: 'REQ-001',
    pattern: 'ubiquitous',
    text: 'THE system SHALL provide user authentication functionality.',
    valid: true,
  },
  {
    id: 'REQ-002',
    pattern: 'event-driven',
    text: 'WHEN a user logs in successfully, THE system SHALL create a session token.',
    valid: true,
  },
  {
    id: 'REQ-003',
    pattern: 'state-driven',
    text: 'WHILE the system is in maintenance mode, THE system SHALL reject all user requests.',
    valid: true,
  },
  {
    id: 'REQ-004',
    pattern: 'unwanted',
    text: 'THE system SHALL NOT store passwords in plain text.',
    valid: true,
  },
  {
    id: 'REQ-005',
    pattern: 'optional',
    text: 'IF the user has admin privileges, THEN THE system SHALL display admin controls.',
    valid: true,
  },
];

/**
 * Invalid requirement samples (not EARS format)
 */
const invalidRequirements: string[] = [
  'The system should provide authentication.', // No SHALL
  'Users can log in.', // No structured format
  'WHEN user logs in', // Incomplete
  'THE system SHALL.', // Missing requirement
  'Must support multiple languages.', // No EARS keywords
];

/**
 * TypeScript code samples
 */
const typescriptCode = `/**
 * User Authentication Service
 * @requirement REQ-001
 */
export class AuthService {
  private users: Map<string, User> = new Map();

  /**
   * Authenticate a user
   * @requirement REQ-002
   */
  async authenticate(username: string, password: string): Promise<Result<Session, AuthError>> {
    const user = this.users.get(username);
    if (!user) {
      return err(new AuthError('User not found'));
    }
    
    if (!this.verifyPassword(password, user.passwordHash)) {
      return err(new AuthError('Invalid password'));
    }
    
    return ok(this.createSession(user));
  }
  
  private verifyPassword(password: string, hash: string): boolean {
    // Password verification logic
    return password.length > 0;
  }
  
  private createSession(user: User): Session {
    return {
      userId: user.id,
      token: crypto.randomUUID(),
      expiresAt: new Date(Date.now() + 3600000),
    };
  }
}

interface User {
  id: string;
  username: string;
  passwordHash: string;
}

interface Session {
  userId: string;
  token: string;
  expiresAt: Date;
}

class AuthError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'AuthError';
  }
}

type Result<T, E> = { ok: true; value: T } | { ok: false; error: E };
const ok = <T>(value: T): Result<T, never> => ({ ok: true, value });
const err = <E>(error: E): Result<never, E> => ({ ok: false, error });
`;

/**
 * Design pattern code samples
 */
const patternSamples: Record<string, string> = {
  repository: `
export interface Repository<T, ID> {
  findById(id: ID): Promise<T | null>;
  findAll(): Promise<T[]>;
  save(entity: T): Promise<T>;
  delete(id: ID): Promise<void>;
}

export class InMemoryRepository<T extends { id: string }> implements Repository<T, string> {
  private items = new Map<string, T>();

  async findById(id: string): Promise<T | null> {
    return this.items.get(id) || null;
  }

  async findAll(): Promise<T[]> {
    return Array.from(this.items.values());
  }

  async save(entity: T): Promise<T> {
    this.items.set(entity.id, entity);
    return entity;
  }

  async delete(id: string): Promise<void> {
    this.items.delete(id);
  }
}
`,

  factory: `
export interface Product {
  name: string;
  price: number;
}

export interface ProductFactory {
  create(type: string): Product;
}

export class ConcreteProductFactory implements ProductFactory {
  create(type: string): Product {
    switch (type) {
      case 'basic':
        return { name: 'Basic Product', price: 100 };
      case 'premium':
        return { name: 'Premium Product', price: 500 };
      default:
        throw new Error(\`Unknown product type: \${type}\`);
    }
  }
}
`,

  singleton: `
export class ConfigManager {
  private static instance: ConfigManager | null = null;
  private config: Record<string, string> = {};

  private constructor() {}

  static getInstance(): ConfigManager {
    if (!ConfigManager.instance) {
      ConfigManager.instance = new ConfigManager();
    }
    return ConfigManager.instance;
  }

  get(key: string): string | undefined {
    return this.config[key];
  }

  set(key: string, value: string): void {
    this.config[key] = value;
  }
}
`,

  observer: `
export interface Observer<T> {
  update(data: T): void;
}

export interface Subject<T> {
  attach(observer: Observer<T>): void;
  detach(observer: Observer<T>): void;
  notify(data: T): void;
}

export class EventEmitter<T> implements Subject<T> {
  private observers: Observer<T>[] = [];

  attach(observer: Observer<T>): void {
    this.observers.push(observer);
  }

  detach(observer: Observer<T>): void {
    const index = this.observers.indexOf(observer);
    if (index >= 0) {
      this.observers.splice(index, 1);
    }
  }

  notify(data: T): void {
    for (const observer of this.observers) {
      observer.update(data);
    }
  }
}
`,
};

/**
 * Valid triple samples
 */
const validTriples: TripleFixture[] = [
  {
    subject: 'http://musubix.dev/req/REQ-001',
    predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
    object: 'http://musubix.dev/ontology#Requirement',
  },
  {
    subject: 'http://musubix.dev/req/REQ-002',
    predicate: 'http://musubix.dev/ontology#dependsOn',
    object: 'http://musubix.dev/req/REQ-001',
  },
  {
    subject: 'http://musubix.dev/design/DES-001',
    predicate: 'http://musubix.dev/ontology#implements',
    object: 'http://musubix.dev/req/REQ-001',
  },
];

/**
 * Circular dependency triple samples
 */
const circularTriples: TripleFixture[] = [
  { subject: 'A', predicate: 'dependsOn', object: 'B' },
  { subject: 'B', predicate: 'dependsOn', object: 'C' },
  { subject: 'C', predicate: 'dependsOn', object: 'A' },
];

/**
 * Inconsistent triple samples (type conflicts)
 */
const inconsistentTriples: TripleFixture[] = [
  {
    subject: 'http://example.org/entity',
    predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
    object: 'http://example.org/TypeA',
  },
  {
    subject: 'http://example.org/TypeA',
    predicate: 'http://www.w3.org/2002/07/owl#disjointWith',
    object: 'http://example.org/TypeB',
  },
  {
    subject: 'http://example.org/entity',
    predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
    object: 'http://example.org/TypeB',
  },
];

/**
 * Default test fixtures
 */
const defaultFixtures: TestFixtures = {
  requirements: {
    valid: validRequirements,
    invalid: invalidRequirements,
  },
  code: {
    typescript: typescriptCode,
    patterns: patternSamples,
  },
  triples: {
    valid: validTriples,
    circular: circularTriples,
    inconsistent: inconsistentTriples,
  },
};

/**
 * Get default test fixtures
 *
 * @returns Test fixtures collection
 *
 * @example
 * ```typescript
 * const fixtures = getFixtures();
 * for (const req of fixtures.requirements.valid) {
 *   expect(validateEars(req.text)).toBe(true);
 * }
 * ```
 */
export function getFixtures(): TestFixtures {
  return { ...defaultFixtures };
}

/**
 * Get fixtures with custom overrides
 *
 * @param overrides - Partial fixtures to merge
 * @returns Merged fixtures
 */
export function getFixturesWith(overrides: Partial<TestFixtures>): TestFixtures {
  return {
    requirements: overrides.requirements ?? defaultFixtures.requirements,
    code: overrides.code ?? defaultFixtures.code,
    triples: overrides.triples ?? defaultFixtures.triples,
  };
}

/**
 * Create a valid EARS requirement fixture
 */
export function createRequirementFixture(
  id: string,
  pattern: EarsRequirementFixture['pattern'],
  text: string
): EarsRequirementFixture {
  return { id, pattern, text, valid: true };
}

/**
 * Create triple fixtures
 */
export function createTripleFixture(
  subject: string,
  predicate: string,
  object: string
): TripleFixture {
  return { subject, predicate, object };
}
