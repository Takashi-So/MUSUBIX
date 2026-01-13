/**
 * Concurrency Patterns - Best Practices for Concurrent Operations
 *
 * @packageDocumentation
 * @module patterns/concurrency
 *
 * @see REQ-PAT-001 - 同時実行パターン追加
 * @see TSK-PAT-001 - 同時実行パターンタスク
 */

/**
 * Concurrency pattern definition
 */
export interface ConcurrencyPattern {
  /** Pattern ID */
  id: string;
  /** Pattern name */
  name: string;
  /** Short description */
  description: string;
  /** When to use this pattern */
  useCase: string;
  /** When NOT to use this pattern */
  antiPattern?: string;
  /** TypeScript template code */
  template: string;
  /** Usage example */
  example: string;
  /** Related patterns */
  relatedPatterns: string[];
  /** Tags for categorization */
  tags: string[];
  /** Confidence score (0-1) */
  confidence: number;
}

/**
 * PAT-CONC-001: Optimistic Locking Pattern
 *
 * Use when: Multiple users may edit the same resource,
 * but conflicts are rare.
 */
export const OPTIMISTIC_LOCKING: ConcurrencyPattern = {
  id: 'PAT-CONC-001',
  name: 'Optimistic Locking',
  description:
    'Allows concurrent reads while detecting conflicts at write time using a version field.',
  useCase:
    'Use when conflicts are rare and you want to maximize read concurrency. Good for high-read, low-write scenarios.',
  antiPattern:
    'Avoid when conflicts are frequent, as users will face many retry prompts.',
  template: `
interface WithVersion {
  version: number;
}

interface OptimisticLockError extends Error {
  code: 'OPTIMISTIC_LOCK_ERROR';
  currentVersion: number;
  providedVersion: number;
}

async function updateWithOptimisticLock<T extends WithVersion>(
  id: string,
  updates: Partial<T>,
  expectedVersion: number,
  repository: {
    findById(id: string): Promise<T | null>;
    save(entity: T): Promise<T>;
  }
): Promise<Result<T, OptimisticLockError>> {
  const current = await repository.findById(id);
  
  if (!current) {
    return err({ code: 'NOT_FOUND' } as any);
  }
  
  if (current.version !== expectedVersion) {
    return err({
      code: 'OPTIMISTIC_LOCK_ERROR',
      message: \`Version conflict: expected \${expectedVersion}, found \${current.version}\`,
      currentVersion: current.version,
      providedVersion: expectedVersion,
    } as OptimisticLockError);
  }
  
  const updated = {
    ...current,
    ...updates,
    version: current.version + 1,
  };
  
  return ok(await repository.save(updated));
}
`.trim(),
  example: `
// Entity with version field
interface Order extends WithVersion {
  id: string;
  status: OrderStatus;
  version: number;
}

// Update with optimistic lock
const result = await updateWithOptimisticLock(
  orderId,
  { status: 'completed' },
  order.version,
  orderRepository
);

if (result.isErr() && result.error.code === 'OPTIMISTIC_LOCK_ERROR') {
  // Handle conflict - reload and retry or notify user
  console.log('Order was modified by another user');
}
`.trim(),
  relatedPatterns: ['PAT-CONC-002', 'PAT-DESIGN-004'],
  tags: ['concurrency', 'versioning', 'conflict-detection'],
  confidence: 0.95,
};

/**
 * PAT-CONC-002: Pessimistic Locking Pattern
 *
 * Use when: Conflicts are frequent and you need to prevent them entirely.
 */
export const PESSIMISTIC_LOCKING: ConcurrencyPattern = {
  id: 'PAT-CONC-002',
  name: 'Pessimistic Locking',
  description:
    'Acquires exclusive lock before modification, preventing concurrent access.',
  useCase:
    'Use when conflicts are frequent or the cost of conflict resolution is high. Good for financial transactions.',
  antiPattern:
    'Avoid for high-concurrency read scenarios as it reduces throughput.',
  template: `
interface Lock {
  resourceId: string;
  ownerId: string;
  acquiredAt: Date;
  expiresAt: Date;
}

interface LockManager {
  acquire(resourceId: string, ownerId: string, ttlMs: number): Promise<Lock | null>;
  release(resourceId: string, ownerId: string): Promise<boolean>;
  isLocked(resourceId: string): Promise<boolean>;
}

async function withPessimisticLock<T>(
  resourceId: string,
  ownerId: string,
  lockManager: LockManager,
  operation: () => Promise<T>,
  options: { ttlMs?: number; retryCount?: number; retryDelayMs?: number } = {}
): Promise<Result<T, 'LOCK_FAILED' | 'OPERATION_FAILED'>> {
  const { ttlMs = 30000, retryCount = 3, retryDelayMs = 100 } = options;
  
  let lock: Lock | null = null;
  let attempts = 0;
  
  while (!lock && attempts < retryCount) {
    lock = await lockManager.acquire(resourceId, ownerId, ttlMs);
    if (!lock) {
      attempts++;
      await sleep(retryDelayMs * attempts);
    }
  }
  
  if (!lock) {
    return err('LOCK_FAILED');
  }
  
  try {
    const result = await operation();
    return ok(result);
  } finally {
    await lockManager.release(resourceId, ownerId);
  }
}

function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}
`.trim(),
  example: `
// Transfer money with pessimistic lock
const result = await withPessimisticLock(
  \`account:\${fromAccountId}\`,
  transactionId,
  lockManager,
  async () => {
    const from = await accountRepo.findById(fromAccountId);
    const to = await accountRepo.findById(toAccountId);
    
    from.balance -= amount;
    to.balance += amount;
    
    await accountRepo.save(from);
    await accountRepo.save(to);
    
    return { from, to };
  },
  { ttlMs: 5000 }
);
`.trim(),
  relatedPatterns: ['PAT-CONC-001', 'PAT-CONC-003'],
  tags: ['concurrency', 'locking', 'exclusive-access'],
  confidence: 0.90,
};

/**
 * PAT-CONC-003: Hold Pattern
 *
 * Use when: You need to temporarily reserve resources before confirmation.
 */
export const HOLD_PATTERN: ConcurrencyPattern = {
  id: 'PAT-CONC-003',
  name: 'Hold Pattern',
  description:
    'Temporarily reserves a resource with automatic expiry, useful for booking/checkout flows.',
  useCase:
    'Use for e-commerce checkout, seat reservations, or any scenario where users need time to complete a multi-step process.',
  antiPattern:
    'Avoid for instant operations where reservation overhead is unnecessary.',
  template: `
interface Hold<T> {
  id: string;
  resourceId: string;
  resourceType: string;
  heldBy: string;
  heldData: T;
  createdAt: Date;
  expiresAt: Date;
  status: 'active' | 'confirmed' | 'expired' | 'released';
}

interface HoldManager<T> {
  createHold(resourceId: string, data: T, ttlMs: number): Promise<Hold<T>>;
  confirmHold(holdId: string): Promise<T | null>;
  releaseHold(holdId: string): Promise<boolean>;
  getHold(holdId: string): Promise<Hold<T> | null>;
  cleanupExpired(): Promise<number>;
}

function createHoldManager<T>(
  repository: HoldRepository<T>
): HoldManager<T> {
  return {
    async createHold(resourceId, data, ttlMs) {
      const hold: Hold<T> = {
        id: generateId(),
        resourceId,
        resourceType: typeof data,
        heldBy: getCurrentUserId(),
        heldData: data,
        createdAt: new Date(),
        expiresAt: new Date(Date.now() + ttlMs),
        status: 'active',
      };
      return repository.save(hold);
    },
    
    async confirmHold(holdId) {
      const hold = await repository.findById(holdId);
      if (!hold || hold.status !== 'active') return null;
      if (hold.expiresAt < new Date()) {
        await repository.updateStatus(holdId, 'expired');
        return null;
      }
      await repository.updateStatus(holdId, 'confirmed');
      return hold.heldData;
    },
    
    async releaseHold(holdId) {
      return repository.updateStatus(holdId, 'released');
    },
    
    async getHold(holdId) {
      return repository.findById(holdId);
    },
    
    async cleanupExpired() {
      return repository.markExpired(new Date());
    },
  };
}
`.trim(),
  example: `
// E-commerce checkout flow
const holdManager = createHoldManager<CartItem[]>(holdRepository);

// Step 1: User adds items to cart - create hold
const hold = await holdManager.createHold(
  'cart:' + cartId,
  cartItems,
  15 * 60 * 1000 // 15 minutes
);

// Step 2: User completes payment
const confirmedItems = await holdManager.confirmHold(hold.id);
if (confirmedItems) {
  await createOrder(confirmedItems);
} else {
  // Hold expired, items may no longer be available
  throw new Error('Checkout session expired');
}
`.trim(),
  relatedPatterns: ['PAT-CONC-002', 'PAT-DESIGN-007'],
  tags: ['concurrency', 'reservation', 'expiry', 'checkout'],
  confidence: 0.90,
};

/**
 * PAT-CONC-004: Idempotency Key Pattern
 *
 * Use when: Operations may be retried (network failures, user double-clicks).
 */
export const IDEMPOTENCY_KEY: ConcurrencyPattern = {
  id: 'PAT-CONC-004',
  name: 'Idempotency Key',
  description:
    'Ensures operations are processed exactly once using a client-provided unique key.',
  useCase:
    'Use for payment processing, order creation, or any operation that should not be duplicated on retry.',
  antiPattern:
    'Not needed for naturally idempotent operations (like GET requests or updates that set absolute values).',
  template: `
interface IdempotencyRecord<T> {
  key: string;
  requestHash: string;
  status: 'processing' | 'completed' | 'failed';
  result?: T;
  error?: string;
  createdAt: Date;
  expiresAt: Date;
}

interface IdempotencyStore<T> {
  get(key: string): Promise<IdempotencyRecord<T> | null>;
  create(key: string, requestHash: string, ttlMs: number): Promise<boolean>;
  complete(key: string, result: T): Promise<void>;
  fail(key: string, error: string): Promise<void>;
}

async function withIdempotency<T>(
  idempotencyKey: string,
  requestBody: unknown,
  store: IdempotencyStore<T>,
  operation: () => Promise<T>,
  options: { ttlMs?: number } = {}
): Promise<Result<T, 'IN_PROGRESS' | 'REQUEST_MISMATCH'>> {
  const { ttlMs = 24 * 60 * 60 * 1000 } = options; // 24 hours default
  const requestHash = hashRequest(requestBody);
  
  // Check for existing record
  const existing = await store.get(idempotencyKey);
  
  if (existing) {
    // Verify request body matches
    if (existing.requestHash !== requestHash) {
      return err('REQUEST_MISMATCH');
    }
    
    // Return cached result if completed
    if (existing.status === 'completed' && existing.result !== undefined) {
      return ok(existing.result);
    }
    
    // Still processing
    if (existing.status === 'processing') {
      return err('IN_PROGRESS');
    }
  }
  
  // Create new record
  const created = await store.create(idempotencyKey, requestHash, ttlMs);
  if (!created) {
    return err('IN_PROGRESS'); // Race condition - another request got there first
  }
  
  try {
    const result = await operation();
    await store.complete(idempotencyKey, result);
    return ok(result);
  } catch (error) {
    await store.fail(idempotencyKey, String(error));
    throw error;
  }
}

function hashRequest(body: unknown): string {
  return JSON.stringify(body); // Simplified - use crypto hash in production
}
`.trim(),
  example: `
// Payment processing with idempotency
app.post('/payments', async (req, res) => {
  const idempotencyKey = req.headers['idempotency-key'];
  
  if (!idempotencyKey) {
    return res.status(400).json({ error: 'Idempotency-Key header required' });
  }
  
  const result = await withIdempotency(
    idempotencyKey,
    req.body,
    idempotencyStore,
    async () => {
      return await paymentService.processPayment(req.body);
    }
  );
  
  if (result.isErr()) {
    if (result.error === 'IN_PROGRESS') {
      return res.status(409).json({ error: 'Request in progress' });
    }
    return res.status(422).json({ error: 'Request body mismatch' });
  }
  
  return res.json(result.value);
});
`.trim(),
  relatedPatterns: ['PAT-CONC-001', 'PAT-DESIGN-005'],
  tags: ['concurrency', 'idempotency', 'retry-safety', 'payment'],
  confidence: 0.95,
};

/**
 * All concurrency patterns
 */
export const CONCURRENCY_PATTERNS: ConcurrencyPattern[] = [
  OPTIMISTIC_LOCKING,
  PESSIMISTIC_LOCKING,
  HOLD_PATTERN,
  IDEMPOTENCY_KEY,
];

/**
 * Get pattern by ID
 */
export function getConcurrencyPattern(id: string): ConcurrencyPattern | undefined {
  return CONCURRENCY_PATTERNS.find((p) => p.id === id);
}

/**
 * Get patterns by tag
 */
export function getConcurrencyPatternsByTag(tag: string): ConcurrencyPattern[] {
  return CONCURRENCY_PATTERNS.filter((p) => p.tags.includes(tag));
}

/**
 * Get all concurrency pattern IDs
 */
export function getConcurrencyPatternIds(): string[] {
  return CONCURRENCY_PATTERNS.map((p) => p.id);
}
