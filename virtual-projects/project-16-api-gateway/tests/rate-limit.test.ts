// Tests for Rate Limiting
// REQ-RATE-001, REQ-RATE-002, REQ-RATE-003, REQ-RATE-004

import { describe, it, expect } from 'vitest';
import {
  createRateLimitBucket,
  checkRateLimit,
  getRateLimitStatus,
  cleanExpiredRequests,
  TIER_LIMITS,
} from '../src/domain/rate-limit.js';

describe('RateLimit', () => {
  describe('createRateLimitBucket', () => {
    it('should create bucket with default tier', () => {
      const bucket = createRateLimitBucket('client-1');

      expect(bucket.clientId).toBe('client-1');
      expect(bucket.tier).toBe('free');
      expect(bucket.requests).toEqual([]);
    });

    it('should create bucket with custom tier', () => {
      const bucket = createRateLimitBucket('client-1', 'premium');

      expect(bucket.tier).toBe('premium');
    });
  });

  describe('TIER_LIMITS', () => {
    it('should have correct tier limits', () => {
      expect(TIER_LIMITS.free).toBe(100);
      expect(TIER_LIMITS.standard).toBe(1000);
      expect(TIER_LIMITS.premium).toBe(10000);
    });
  });

  describe('checkRateLimit', () => {
    it('should allow request when under limit', () => {
      const bucket = createRateLimitBucket('client-1');
      const now = Date.now();

      const { result, bucket: newBucket } = checkRateLimit(bucket, now);

      expect(result.allowed).toBe(true);
      expect(result.remaining).toBe(99); // 100 - 1
      expect(result.limit).toBe(100);
      expect(newBucket.requests).toHaveLength(1);
    });

    it('should deny request when at limit', () => {
      let bucket = createRateLimitBucket('client-1');
      const now = Date.now();

      // Fill up to limit
      for (let i = 0; i < 100; i++) {
        const { bucket: newBucket } = checkRateLimit(bucket, now + i);
        bucket = newBucket;
      }

      // Next request should be denied
      const { result } = checkRateLimit(bucket, now + 100);

      expect(result.allowed).toBe(false);
      expect(result.remaining).toBe(0);
      expect(result.retryAfterSeconds).toBeDefined();
      expect(result.retryAfterSeconds!).toBeGreaterThan(0);
    });

    it('should use tier-specific limits', () => {
      const bucket = createRateLimitBucket('client-1', 'premium');
      const now = Date.now();

      const { result } = checkRateLimit(bucket, now);

      expect(result.limit).toBe(10000);
      expect(result.remaining).toBe(9999);
    });
  });

  describe('cleanExpiredRequests', () => {
    it('should remove expired requests', () => {
      let bucket = createRateLimitBucket('client-1', 'free', 1000); // 1 second window
      const now = Date.now();

      // Add some requests
      bucket = {
        ...bucket,
        requests: [now - 2000, now - 500, now - 100], // One expired, two valid
      };

      const cleaned = cleanExpiredRequests(bucket, now);

      expect(cleaned.requests).toHaveLength(2);
      expect(cleaned.requests).toContain(now - 500);
      expect(cleaned.requests).toContain(now - 100);
    });
  });

  describe('getRateLimitStatus', () => {
    it('should return status without recording', () => {
      let bucket = createRateLimitBucket('client-1');
      const now = Date.now();

      // Add some requests
      bucket = {
        ...bucket,
        requests: [now - 1000, now - 500, now - 100],
      };

      const status = getRateLimitStatus(bucket, now);

      expect(status.allowed).toBe(true);
      expect(status.remaining).toBe(97); // 100 - 3
      expect(bucket.requests).toHaveLength(3); // Not modified
    });

    it('should return exhausted status', () => {
      let bucket = createRateLimitBucket('client-1');
      const now = Date.now();

      // Fill with 100 requests
      const requests = Array.from({ length: 100 }, (_, i) => now - i * 100);
      bucket = { ...bucket, requests };

      const status = getRateLimitStatus(bucket, now);

      expect(status.allowed).toBe(false);
      expect(status.remaining).toBe(0);
      expect(status.retryAfterSeconds).toBeDefined();
    });
  });

  describe('sliding window behavior', () => {
    it('should allow requests as old ones expire', () => {
      const windowMs = 10000; // 10 seconds
      let bucket = createRateLimitBucket('client-1', 'free', windowMs);

      const startTime = Date.now();

      // Fill to limit at start
      for (let i = 0; i < 100; i++) {
        const { bucket: newBucket } = checkRateLimit(bucket, startTime + i);
        bucket = newBucket;
      }

      // Should be at limit
      let { result } = checkRateLimit(bucket, startTime + 100);
      expect(result.allowed).toBe(false);

      // After window passes, should have room again
      const afterWindow = startTime + windowMs + 1000;
      ({ result } = checkRateLimit(bucket, afterWindow));
      expect(result.allowed).toBe(true);
    });
  });
});
