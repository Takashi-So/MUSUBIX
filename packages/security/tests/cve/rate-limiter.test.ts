/**
 * @fileoverview Rate Limiter Unit Tests
 * @module @nahisaho/musubix-security/tests/cve/rate-limiter.test
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  RateLimiter,
  RateLimiterPool,
  withRateLimit,
} from '../../src/cve/rate-limiter.js';

describe('RateLimiter', () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('constructor', () => {
    it('should initialize with maxTokens', () => {
      const limiter = new RateLimiter({ maxTokens: 10, windowMs: 1000 });
      const status = limiter.getStatus();
      expect(status.availableTokens).toBe(10);
      expect(status.maxTokens).toBe(10);
    });

    it('should use maxTokens as default refillTokens', () => {
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
      
      // Consume all tokens
      for (let i = 0; i < 5; i++) {
        limiter.consume();
      }
      expect(limiter.getStatus().availableTokens).toBe(0);

      // Advance time by one window
      vi.advanceTimersByTime(1000);
      
      // Should refill all tokens
      expect(limiter.getStatus().availableTokens).toBe(5);
    });

    it('should accept custom refillTokens', () => {
      const limiter = new RateLimiter({
        maxTokens: 10,
        windowMs: 1000,
        refillTokens: 2,
      });
      
      // Consume all tokens
      for (let i = 0; i < 10; i++) {
        limiter.consume();
      }
      expect(limiter.getStatus().availableTokens).toBe(0);

      // Advance one window - should only refill 2
      vi.advanceTimersByTime(1000);
      expect(limiter.getStatus().availableTokens).toBe(2);

      // Advance another window - should add 2 more
      vi.advanceTimersByTime(1000);
      expect(limiter.getStatus().availableTokens).toBe(4);
    });
  });

  describe('static factory methods', () => {
    it('should create limiter with API key (50 req/30s)', () => {
      const limiter = RateLimiter.withApiKey();
      const status = limiter.getStatus();
      expect(status.maxTokens).toBe(50);
    });

    it('should create limiter without API key (5 req/30s)', () => {
      const limiter = RateLimiter.withoutApiKey();
      const status = limiter.getStatus();
      expect(status.maxTokens).toBe(5);
    });

    it('should create appropriate limiter via forNVD', () => {
      const withKey = RateLimiter.forNVD(true);
      const withoutKey = RateLimiter.forNVD(false);
      
      expect(withKey.getStatus().maxTokens).toBe(50);
      expect(withoutKey.getStatus().maxTokens).toBe(5);
    });
  });

  describe('canProceed', () => {
    it('should return true when tokens available', () => {
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
      expect(limiter.canProceed()).toBe(true);
    });

    it('should return false when no tokens available', () => {
      const limiter = new RateLimiter({ maxTokens: 1, windowMs: 1000 });
      limiter.consume();
      expect(limiter.canProceed()).toBe(false);
    });

    it('should return true after window elapses', () => {
      const limiter = new RateLimiter({ maxTokens: 1, windowMs: 1000 });
      limiter.consume();
      expect(limiter.canProceed()).toBe(false);
      
      vi.advanceTimersByTime(1000);
      expect(limiter.canProceed()).toBe(true);
    });
  });

  describe('consume', () => {
    it('should consume token and return true', () => {
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
      const result = limiter.consume();
      
      expect(result).toBe(true);
      expect(limiter.getStatus().availableTokens).toBe(4);
    });

    it('should return false when no tokens available', () => {
      const limiter = new RateLimiter({ maxTokens: 1, windowMs: 1000 });
      limiter.consume();
      
      const result = limiter.consume();
      expect(result).toBe(false);
    });

    it('should consume all tokens', () => {
      const limiter = new RateLimiter({ maxTokens: 3, windowMs: 1000 });
      
      expect(limiter.consume()).toBe(true);
      expect(limiter.consume()).toBe(true);
      expect(limiter.consume()).toBe(true);
      expect(limiter.consume()).toBe(false);
    });
  });

  describe('tryAcquire', () => {
    it('should be alias for consume', () => {
      const limiter = new RateLimiter({ maxTokens: 2, windowMs: 1000 });
      
      expect(limiter.tryAcquire()).toBe(true);
      expect(limiter.tryAcquire()).toBe(true);
      expect(limiter.tryAcquire()).toBe(false);
    });
  });

  describe('waitForToken', () => {
    it('should resolve immediately when tokens available', async () => {
      vi.useRealTimers(); // Need real timers for async
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
      
      await expect(limiter.waitForToken()).resolves.toBeUndefined();
      expect(limiter.getStatus().availableTokens).toBe(4);
    });

    it('should wait for token to become available', async () => {
      vi.useRealTimers();
      const limiter = new RateLimiter({ maxTokens: 1, windowMs: 50 });
      limiter.consume();
      
      const startTime = Date.now();
      await limiter.waitForToken();
      const elapsed = Date.now() - startTime;
      
      // Should have waited approximately windowMs
      expect(elapsed).toBeGreaterThanOrEqual(40);
    });

    it('should throw on timeout', async () => {
      vi.useRealTimers();
      const limiter = new RateLimiter({ maxTokens: 1, windowMs: 10000 });
      limiter.consume();
      
      await expect(limiter.waitForToken(50)).rejects.toThrow('Rate limit timeout');
    });
  });

  describe('getStatus', () => {
    it('should return complete status', () => {
      const limiter = new RateLimiter({ maxTokens: 10, windowMs: 5000 });
      limiter.consume();
      
      const status = limiter.getStatus();
      
      expect(status.availableTokens).toBe(9);
      expect(status.maxTokens).toBe(10);
      expect(status.canProceed).toBe(true);
      expect(status.waitTimeMs).toBe(0);
    });

    it('should calculate wait time when no tokens', () => {
      const limiter = new RateLimiter({ maxTokens: 1, windowMs: 5000 });
      limiter.consume();
      
      const status = limiter.getStatus();
      
      expect(status.canProceed).toBe(false);
      expect(status.waitTimeMs).toBeGreaterThan(0);
      expect(status.waitTimeMs).toBeLessThanOrEqual(5000);
    });

    it('should update msUntilRefill', () => {
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 5000 });
      
      vi.advanceTimersByTime(2000);
      
      const status = limiter.getStatus();
      expect(status.msUntilRefill).toBeLessThanOrEqual(3000);
    });
  });

  describe('reset', () => {
    it('should reset tokens to max', () => {
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
      
      for (let i = 0; i < 5; i++) {
        limiter.consume();
      }
      expect(limiter.getStatus().availableTokens).toBe(0);
      
      limiter.reset();
      expect(limiter.getStatus().availableTokens).toBe(5);
    });
  });

  describe('token refill over multiple windows', () => {
    it('should refill correctly over multiple windows', () => {
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
      
      // Consume all tokens
      for (let i = 0; i < 5; i++) {
        limiter.consume();
      }
      expect(limiter.getStatus().availableTokens).toBe(0);
      
      // Advance 3 windows
      vi.advanceTimersByTime(3000);
      
      // Should refill to max (not more than max)
      expect(limiter.getStatus().availableTokens).toBe(5);
    });

    it('should not exceed maxTokens on refill', () => {
      const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
      
      // Don't consume anything, advance time
      vi.advanceTimersByTime(10000);
      
      expect(limiter.getStatus().availableTokens).toBe(5);
    });
  });
});

describe('RateLimiterPool', () => {
  describe('get', () => {
    it('should create new limiter if not exists', () => {
      const pool = new RateLimiterPool();
      const limiter = pool.get('test', () => new RateLimiter({ maxTokens: 5, windowMs: 1000 }));
      
      expect(limiter).toBeInstanceOf(RateLimiter);
    });

    it('should return existing limiter', () => {
      const pool = new RateLimiterPool();
      const limiter1 = pool.get('test', () => new RateLimiter({ maxTokens: 5, windowMs: 1000 }));
      const limiter2 = pool.get('test', () => new RateLimiter({ maxTokens: 10, windowMs: 1000 }));
      
      expect(limiter1).toBe(limiter2);
      expect(limiter1.getStatus().maxTokens).toBe(5); // Original, not replaced
    });

    it('should manage multiple limiters', () => {
      const pool = new RateLimiterPool();
      const limiter1 = pool.get('api1', () => new RateLimiter({ maxTokens: 5, windowMs: 1000 }));
      const limiter2 = pool.get('api2', () => new RateLimiter({ maxTokens: 10, windowMs: 1000 }));
      
      expect(limiter1).not.toBe(limiter2);
      expect(limiter1.getStatus().maxTokens).toBe(5);
      expect(limiter2.getStatus().maxTokens).toBe(10);
    });
  });

  describe('has', () => {
    it('should return true for existing key', () => {
      const pool = new RateLimiterPool();
      pool.get('test', () => new RateLimiter({ maxTokens: 5, windowMs: 1000 }));
      
      expect(pool.has('test')).toBe(true);
    });

    it('should return false for non-existing key', () => {
      const pool = new RateLimiterPool();
      
      expect(pool.has('nonexistent')).toBe(false);
    });
  });

  describe('remove', () => {
    it('should remove existing limiter', () => {
      const pool = new RateLimiterPool();
      pool.get('test', () => new RateLimiter({ maxTokens: 5, windowMs: 1000 }));
      
      const result = pool.remove('test');
      
      expect(result).toBe(true);
      expect(pool.has('test')).toBe(false);
    });

    it('should return false for non-existing key', () => {
      const pool = new RateLimiterPool();
      
      expect(pool.remove('nonexistent')).toBe(false);
    });
  });

  describe('keys', () => {
    it('should return all limiter keys', () => {
      const pool = new RateLimiterPool();
      pool.get('api1', () => new RateLimiter({ maxTokens: 5, windowMs: 1000 }));
      pool.get('api2', () => new RateLimiter({ maxTokens: 10, windowMs: 1000 }));
      
      expect(pool.keys()).toEqual(expect.arrayContaining(['api1', 'api2']));
      expect(pool.keys()).toHaveLength(2);
    });
  });

  describe('dispose', () => {
    it('should dispose all limiters', () => {
      const pool = new RateLimiterPool();
      pool.get('api1', () => new RateLimiter({ maxTokens: 5, windowMs: 1000 }));
      pool.get('api2', () => new RateLimiter({ maxTokens: 10, windowMs: 1000 }));
      
      pool.dispose();
      
      expect(pool.keys()).toHaveLength(0);
    });
  });
});

describe('withRateLimit', () => {
  it('should wrap async function with rate limiting', async () => {
    const limiter = new RateLimiter({ maxTokens: 5, windowMs: 1000 });
    let callCount = 0;
    
    const mockFn = async (x: number): Promise<number> => {
      callCount++;
      return x * 2;
    };
    
    const rateLimited = withRateLimit(limiter, mockFn);
    
    const result = await rateLimited(5);
    
    expect(result).toBe(10);
    expect(callCount).toBe(1);
    expect(limiter.getStatus().availableTokens).toBe(4);
  });

  it('should consume token for each call', async () => {
    const limiter = new RateLimiter({ maxTokens: 3, windowMs: 10000 });
    const mockFn = async () => 'result';
    const rateLimited = withRateLimit(limiter, mockFn);
    
    await rateLimited();
    await rateLimited();
    await rateLimited();
    
    expect(limiter.getStatus().availableTokens).toBe(0);
  });
});
