// REQ-CACHE-001, REQ-CACHE-002, REQ-CACHE-003: Response Caching
// Traces to: DES-CACHE-001, DES-CACHE-002, DES-CACHE-003

/**
 * Cache entry
 * @requirement REQ-CACHE-001
 */
export interface CacheEntry {
  key: string;
  value: unknown;
  contentType: string;
  createdAt: Date;
  expiresAt: Date;
  etag?: string;
}

/**
 * Create cache entry
 * @requirement REQ-CACHE-001
 */
export function createCacheEntry(
  key: string,
  value: unknown,
  ttlSeconds: number,
  contentType: string = 'application/json',
  now: Date = new Date()
): CacheEntry {
  if (!key) {
    throw new Error('Cache key is required');
  }
  if (ttlSeconds <= 0) {
    throw new Error('TTL must be positive');
  }

  const expiresAt = new Date(now.getTime() + ttlSeconds * 1000);

  return {
    key,
    value,
    contentType,
    createdAt: now,
    expiresAt,
    etag: generateEtag(value),
  };
}

/**
 * Generate simple ETag from value
 */
function generateEtag(value: unknown): string {
  const str = JSON.stringify(value);
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = (hash << 5) - hash + char;
    hash = hash & hash;
  }
  return `"${Math.abs(hash).toString(16)}"`;
}

/**
 * Check if cache entry is expired
 * @requirement REQ-CACHE-002
 */
export function isCacheExpired(entry: CacheEntry, now: Date = new Date()): boolean {
  return now > entry.expiresAt;
}

/**
 * Generate cache key from request
 * @requirement REQ-CACHE-001
 */
export function generateCacheKey(
  method: string,
  path: string,
  queryParams?: Record<string, string>
): string {
  let key = `${method}:${path}`;
  if (queryParams && Object.keys(queryParams).length > 0) {
    const sortedParams = Object.keys(queryParams)
      .sort()
      .map((k) => `${k}=${queryParams[k]}`)
      .join('&');
    key += `?${sortedParams}`;
  }
  return key;
}

/**
 * In-memory cache store
 * @requirement REQ-CACHE-001
 */
export interface CacheStore {
  entries: Map<string, CacheEntry>;
}

/**
 * Create cache store
 */
export function createCacheStore(): CacheStore {
  return { entries: new Map() };
}

/**
 * Get cache entry
 * @requirement REQ-CACHE-002
 */
export function getCache(
  store: CacheStore,
  key: string,
  now: Date = new Date()
): CacheEntry | null {
  const entry = store.entries.get(key);
  if (!entry) {
    return null;
  }
  if (isCacheExpired(entry, now)) {
    store.entries.delete(key);
    return null;
  }
  return entry;
}

/**
 * Set cache entry
 * @requirement REQ-CACHE-001
 */
export function setCache(store: CacheStore, entry: CacheEntry): void {
  store.entries.set(entry.key, entry);
}

/**
 * Invalidate cache by key
 * @requirement REQ-CACHE-003
 */
export function invalidateCache(store: CacheStore, key: string): boolean {
  return store.entries.delete(key);
}

/**
 * Invalidate cache by pattern
 * @requirement REQ-CACHE-003
 */
export function invalidateCachePattern(store: CacheStore, pattern: string): number {
  const regex = new RegExp(pattern.replace(/\*/g, '.*'));
  let count = 0;
  for (const key of store.entries.keys()) {
    if (regex.test(key)) {
      store.entries.delete(key);
      count++;
    }
  }
  return count;
}
