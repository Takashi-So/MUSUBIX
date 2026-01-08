/**
 * @fileoverview Token Bucket Rate Limiter for NVD API
 * @module @nahisaho/musubix-security/cve/rate-limiter
 *
 * Implements Token Bucket algorithm for rate limiting.
 * - With API Key: 50 requests per 30 seconds
 * - Without API Key: 5 requests per 30 seconds
 *
 * @requirement REQ-CVE-001 - NVD API rate limiting compliance
 * @design DES-EPIC2-002 - Rate Limiter component
 */

/**
 * Rate limiter configuration options
 */
export interface RateLimiterOptions {
  /**
   * Maximum number of tokens in the bucket
   * @default 50 (with API key) or 5 (without)
   */
  maxTokens: number;

  /**
   * Time window in milliseconds for token refill
   * @default 30000 (30 seconds)
   */
  windowMs: number;

  /**
   * Number of tokens to refill per window
   * @default maxTokens
   */
  refillTokens?: number;
}

/**
 * Rate limit status information
 */
export interface RateLimitStatus {
  /** Available tokens */
  availableTokens: number;
  /** Maximum tokens */
  maxTokens: number;
  /** Milliseconds until next refill */
  msUntilRefill: number;
  /** Whether a request can be made now */
  canProceed: boolean;
  /** Estimated wait time if cannot proceed (ms) */
  waitTimeMs: number;
}

/**
 * Token Bucket Rate Limiter
 *
 * @example
 * ```typescript
 * // With API key (50 req/30s)
 * const limiter = new RateLimiter({ maxTokens: 50, windowMs: 30000 });
 *
 * // Check if request can proceed
 * if (limiter.canProceed()) {
 *   limiter.consume();
 *   // make request
 * }
 *
 * // Or wait for token
 * await limiter.waitForToken();
 * // make request
 * ```
 */
export class RateLimiter {
  private tokens: number;
  private readonly maxTokens: number;
  private readonly windowMs: number;
  private readonly refillTokens: number;
  private lastRefillTime: number;
  private refillInterval: ReturnType<typeof setInterval> | null = null;

  constructor(options: RateLimiterOptions) {
    this.maxTokens = options.maxTokens;
    this.windowMs = options.windowMs;
    this.refillTokens = options.refillTokens ?? options.maxTokens;
    this.tokens = this.maxTokens;
    this.lastRefillTime = Date.now();
  }

  /**
   * Create a rate limiter configured for NVD API with API key
   * @returns Rate limiter with 50 req/30s limit
   */
  static withApiKey(): RateLimiter {
    return new RateLimiter({ maxTokens: 50, windowMs: 30000 });
  }

  /**
   * Create a rate limiter configured for NVD API without API key
   * @returns Rate limiter with 5 req/30s limit
   */
  static withoutApiKey(): RateLimiter {
    return new RateLimiter({ maxTokens: 5, windowMs: 30000 });
  }

  /**
   * Create appropriate rate limiter based on whether API key is provided
   * @param hasApiKey - Whether an API key is available
   * @returns Configured rate limiter
   */
  static forNVD(hasApiKey: boolean): RateLimiter {
    return hasApiKey ? RateLimiter.withApiKey() : RateLimiter.withoutApiKey();
  }

  /**
   * Refill tokens based on elapsed time
   */
  private refill(): void {
    const now = Date.now();
    const elapsed = now - this.lastRefillTime;

    if (elapsed >= this.windowMs) {
      // Calculate how many full windows have passed
      const windowsPassed = Math.floor(elapsed / this.windowMs);
      const tokensToAdd = windowsPassed * this.refillTokens;

      this.tokens = Math.min(this.maxTokens, this.tokens + tokensToAdd);
      this.lastRefillTime = now - (elapsed % this.windowMs);
    }
  }

  /**
   * Check if a request can proceed without waiting
   * @returns True if tokens are available
   */
  canProceed(): boolean {
    this.refill();
    return this.tokens > 0;
  }

  /**
   * Consume a token for a request
   * @returns True if token was consumed, false if no tokens available
   */
  consume(): boolean {
    this.refill();

    if (this.tokens > 0) {
      this.tokens--;
      return true;
    }

    return false;
  }

  /**
   * Try to acquire a token, consuming it if available
   * Alias for consume() for clearer semantics
   * @returns True if token was acquired
   */
  tryAcquire(): boolean {
    return this.consume();
  }

  /**
   * Wait for a token to become available, then consume it
   * @param timeoutMs - Maximum time to wait (default: 2 * windowMs)
   * @returns Promise that resolves when token is acquired
   * @throws Error if timeout is exceeded
   */
  async waitForToken(timeoutMs?: number): Promise<void> {
    const timeout = timeoutMs ?? this.windowMs * 2;
    const startTime = Date.now();

    while (!this.consume()) {
      const elapsed = Date.now() - startTime;
      if (elapsed >= timeout) {
        throw new Error(
          `Rate limit timeout: waited ${elapsed}ms for token (max: ${timeout}ms)`
        );
      }

      // Calculate optimal wait time
      const status = this.getStatus();
      const waitTime = Math.min(status.waitTimeMs, timeout - elapsed, 100);

      await this.sleep(waitTime);
    }
  }

  /**
   * Get current rate limit status
   * @returns Current status including available tokens and wait time
   */
  getStatus(): RateLimitStatus {
    this.refill();

    const now = Date.now();
    const elapsed = now - this.lastRefillTime;
    const msUntilRefill = Math.max(0, this.windowMs - elapsed);

    // Calculate wait time if no tokens available
    let waitTimeMs = 0;
    if (this.tokens === 0) {
      // Time until next refill
      waitTimeMs = msUntilRefill;
    }

    return {
      availableTokens: this.tokens,
      maxTokens: this.maxTokens,
      msUntilRefill,
      canProceed: this.tokens > 0,
      waitTimeMs,
    };
  }

  /**
   * Reset the rate limiter to initial state
   */
  reset(): void {
    this.tokens = this.maxTokens;
    this.lastRefillTime = Date.now();
  }

  /**
   * Start automatic token refill (for long-running processes)
   * @param callback - Optional callback when tokens are refilled
   */
  startAutoRefill(callback?: (tokens: number) => void): void {
    if (this.refillInterval) {
      return; // Already running
    }

    this.refillInterval = setInterval(() => {
      const oldTokens = this.tokens;
      this.refill();

      if (callback && this.tokens > oldTokens) {
        callback(this.tokens);
      }
    }, this.windowMs);
  }

  /**
   * Stop automatic token refill
   */
  stopAutoRefill(): void {
    if (this.refillInterval) {
      clearInterval(this.refillInterval);
      this.refillInterval = null;
    }
  }

  /**
   * Dispose of the rate limiter
   */
  dispose(): void {
    this.stopAutoRefill();
  }

  /**
   * Sleep for specified milliseconds
   */
  private sleep(ms: number): Promise<void> {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }
}

/**
 * Decorator for rate-limited async functions
 *
 * @example
 * ```typescript
 * const limiter = RateLimiter.forNVD(true);
 *
 * const rateLimitedFetch = withRateLimit(limiter, async (url: string) => {
 *   return fetch(url);
 * });
 * ```
 */
export function withRateLimit<T extends (...args: unknown[]) => Promise<unknown>>(
  limiter: RateLimiter,
  fn: T
): T {
  return (async (...args: Parameters<T>): Promise<ReturnType<T>> => {
    await limiter.waitForToken();
    return fn(...args) as ReturnType<T>;
  }) as T;
}

/**
 * Rate limiter pool for managing multiple limiters
 *
 * @example
 * ```typescript
 * const pool = new RateLimiterPool();
 *
 * // Get or create a limiter for NVD API
 * const nvdLimiter = pool.get('nvd', () => RateLimiter.forNVD(true));
 * ```
 */
export class RateLimiterPool {
  private limiters = new Map<string, RateLimiter>();

  /**
   * Get or create a rate limiter by key
   * @param key - Unique identifier for the limiter
   * @param factory - Factory function to create limiter if not exists
   * @returns The rate limiter
   */
  get(key: string, factory: () => RateLimiter): RateLimiter {
    let limiter = this.limiters.get(key);

    if (!limiter) {
      limiter = factory();
      this.limiters.set(key, limiter);
    }

    return limiter;
  }

  /**
   * Check if a limiter exists for the given key
   */
  has(key: string): boolean {
    return this.limiters.has(key);
  }

  /**
   * Remove a limiter by key
   */
  remove(key: string): boolean {
    const limiter = this.limiters.get(key);
    if (limiter) {
      limiter.dispose();
      this.limiters.delete(key);
      return true;
    }
    return false;
  }

  /**
   * Get all limiter keys
   */
  keys(): string[] {
    return Array.from(this.limiters.keys());
  }

  /**
   * Dispose all limiters
   */
  dispose(): void {
    for (const limiter of this.limiters.values()) {
      limiter.dispose();
    }
    this.limiters.clear();
  }
}
