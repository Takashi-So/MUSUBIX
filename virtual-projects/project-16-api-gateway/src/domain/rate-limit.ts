// REQ-RATE-001, REQ-RATE-002, REQ-RATE-003, REQ-RATE-004: Rate Limiting
// Traces to: DES-RATE-001, DES-RATE-002, DES-RATE-003, DES-RATE-004

/**
 * Rate limit tier
 * @requirement REQ-RATE-004
 */
export type RateLimitTier = 'free' | 'standard' | 'premium';

/**
 * Tier limits configuration (requests per hour)
 * @requirement REQ-RATE-004
 */
export const TIER_LIMITS: Record<RateLimitTier, number> = {
  free: 100,
  standard: 1000,
  premium: 10000,
};

/**
 * Rate limit bucket for sliding window
 * @requirement REQ-RATE-001, REQ-RATE-002
 */
export interface RateLimitBucket {
  clientId: string;
  tier: RateLimitTier;
  requests: number[];
  windowSizeMs: number;
}

/**
 * Create rate limit bucket
 * @requirement REQ-RATE-001
 */
export function createRateLimitBucket(
  clientId: string,
  tier: RateLimitTier = 'free',
  windowSizeMs: number = 3600000 // 1 hour
): RateLimitBucket {
  return {
    clientId,
    tier,
    requests: [],
    windowSizeMs,
  };
}

/**
 * Clean expired requests from bucket
 * @requirement REQ-RATE-002
 */
export function cleanExpiredRequests(
  bucket: RateLimitBucket,
  now: number = Date.now()
): RateLimitBucket {
  const cutoff = now - bucket.windowSizeMs;
  return {
    ...bucket,
    requests: bucket.requests.filter((ts) => ts > cutoff),
  };
}

/**
 * Rate limit check result
 * @requirement REQ-RATE-003
 */
export interface RateLimitResult {
  allowed: boolean;
  remaining: number;
  limit: number;
  retryAfterSeconds?: number;
}

/**
 * Check if request is allowed and record it
 * @requirement REQ-RATE-001, REQ-RATE-002, REQ-RATE-003
 */
export function checkRateLimit(
  bucket: RateLimitBucket,
  now: number = Date.now()
): { result: RateLimitResult; bucket: RateLimitBucket } {
  // Clean expired requests
  const cleaned = cleanExpiredRequests(bucket, now);
  const limit = TIER_LIMITS[cleaned.tier];

  if (cleaned.requests.length >= limit) {
    // Rate limit exceeded
    const oldestRequest = Math.min(...cleaned.requests);
    const retryAfterMs = oldestRequest + bucket.windowSizeMs - now;
    const retryAfterSeconds = Math.ceil(retryAfterMs / 1000);

    return {
      result: {
        allowed: false,
        remaining: 0,
        limit,
        retryAfterSeconds: Math.max(1, retryAfterSeconds),
      },
      bucket: cleaned,
    };
  }

  // Request allowed, record it
  const newBucket: RateLimitBucket = {
    ...cleaned,
    requests: [...cleaned.requests, now],
  };

  return {
    result: {
      allowed: true,
      remaining: limit - newBucket.requests.length,
      limit,
    },
    bucket: newBucket,
  };
}

/**
 * Get current rate limit status without recording
 * @requirement REQ-RATE-003
 */
export function getRateLimitStatus(
  bucket: RateLimitBucket,
  now: number = Date.now()
): RateLimitResult {
  const cleaned = cleanExpiredRequests(bucket, now);
  const limit = TIER_LIMITS[cleaned.tier];
  const remaining = Math.max(0, limit - cleaned.requests.length);

  if (remaining === 0) {
    const oldestRequest = Math.min(...cleaned.requests);
    const retryAfterMs = oldestRequest + bucket.windowSizeMs - now;
    const retryAfterSeconds = Math.ceil(retryAfterMs / 1000);
    return {
      allowed: false,
      remaining: 0,
      limit,
      retryAfterSeconds: Math.max(1, retryAfterSeconds),
    };
  }

  return {
    allowed: true,
    remaining,
    limit,
  };
}
