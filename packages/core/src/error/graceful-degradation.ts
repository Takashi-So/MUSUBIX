/**
 * Graceful Degradation
 * 
 * Handles errors gracefully with fallback strategies
 * 
 * @packageDocumentation
 * @module error/graceful-degradation
 * 
 * @see REQ-ERR-001 - Graceful Degradation
 * @see Article V - Safety Assurance
 */

/**
 * Degradation level
 */
export type DegradationLevel = 
  | 'full'        // All features available
  | 'reduced'     // Some features disabled
  | 'minimal'     // Only essential features
  | 'offline'     // No external dependencies
  | 'emergency';  // Absolute minimum

/**
 * Service status
 */
export type ServiceStatus = 'healthy' | 'degraded' | 'unavailable' | 'unknown';

/**
 * Fallback strategy
 */
export type FallbackStrategy = 
  | 'cache'       // Use cached data
  | 'default'     // Use default values
  | 'retry'       // Retry with backoff
  | 'alternative' // Use alternative service
  | 'skip'        // Skip the operation
  | 'queue'       // Queue for later
  | 'manual';     // Require manual intervention

/**
 * Service health check result
 */
export interface HealthCheckResult {
  /** Service name */
  service: string;
  /** Status */
  status: ServiceStatus;
  /** Response time (ms) */
  responseTime?: number;
  /** Last successful check */
  lastSuccess?: Date;
  /** Error message if any */
  error?: string;
  /** Additional details */
  details?: Record<string, unknown>;
}

/**
 * Service configuration
 */
export interface ServiceConfig {
  /** Service name */
  name: string;
  /** Health check function */
  healthCheck: () => Promise<boolean>;
  /** Fallback strategies in order of preference */
  fallbackStrategies: FallbackStrategy[];
  /** Cache TTL (ms) */
  cacheTtl?: number;
  /** Retry attempts */
  retryAttempts?: number;
  /** Retry delay (ms) */
  retryDelay?: number;
  /** Alternative service */
  alternative?: string;
  /** Priority (higher = more important) */
  priority: number;
  /** Required for minimal operation */
  required: boolean;
}

/**
 * Fallback action
 */
export interface FallbackAction<T = unknown> {
  /** Strategy used */
  strategy: FallbackStrategy;
  /** Execute fallback */
  execute: () => Promise<T>;
  /** Description */
  description: string;
}

/**
 * Degradation event
 */
export interface DegradationEvent {
  /** Event ID */
  id: string;
  /** Timestamp */
  timestamp: Date;
  /** Service affected */
  service: string;
  /** Previous level */
  previousLevel: DegradationLevel;
  /** New level */
  newLevel: DegradationLevel;
  /** Reason */
  reason: string;
  /** Fallback used */
  fallbackUsed?: FallbackStrategy;
  /** Recovery time estimate */
  estimatedRecovery?: Date;
}

/**
 * Operation result with degradation info
 */
export interface DegradedResult<T> {
  /** Result value */
  value: T;
  /** Was degraded */
  degraded: boolean;
  /** Degradation level */
  level: DegradationLevel;
  /** Strategy used */
  strategy?: FallbackStrategy;
  /** Original error */
  originalError?: Error;
  /** Warnings */
  warnings: string[];
}

/**
 * Graceful degradation config
 */
export interface GracefulDegradationConfig {
  /** Services configuration */
  services: ServiceConfig[];
  /** Health check interval (ms) */
  healthCheckInterval: number;
  /** Cache provider */
  cacheProvider?: CacheProvider;
  /** Queue provider */
  queueProvider?: QueueProvider;
  /** Event handler */
  onDegradation?: (event: DegradationEvent) => void;
  /** Recovery handler */
  onRecovery?: (service: string, level: DegradationLevel) => void;
  /** Auto-recovery enabled */
  autoRecovery: boolean;
  /** Max queue size */
  maxQueueSize: number;
}

/**
 * Cache provider interface
 */
export interface CacheProvider {
  get<T>(key: string): Promise<T | null>;
  set<T>(key: string, value: T, ttl?: number): Promise<void>;
  delete(key: string): Promise<void>;
  clear(): Promise<void>;
}

/**
 * Queue provider interface
 */
export interface QueueProvider {
  enqueue<T>(item: T): Promise<string>;
  dequeue<T>(): Promise<T | null>;
  size(): Promise<number>;
  clear(): Promise<void>;
}

/**
 * In-memory cache provider
 */
export class MemoryCacheProvider implements CacheProvider {
  private cache = new Map<string, { value: unknown; expires: number }>();

  async get<T>(key: string): Promise<T | null> {
    const entry = this.cache.get(key);
    if (!entry) return null;
    if (entry.expires && entry.expires < Date.now()) {
      this.cache.delete(key);
      return null;
    }
    return entry.value as T;
  }

  async set<T>(key: string, value: T, ttl?: number): Promise<void> {
    this.cache.set(key, {
      value,
      expires: ttl ? Date.now() + ttl : 0,
    });
  }

  async delete(key: string): Promise<void> {
    this.cache.delete(key);
  }

  async clear(): Promise<void> {
    this.cache.clear();
  }
}

/**
 * In-memory queue provider
 */
export class MemoryQueueProvider implements QueueProvider {
  private queue: Array<{ id: string; item: unknown }> = [];
  private counter = 0;

  async enqueue<T>(item: T): Promise<string> {
    const id = `q-${Date.now()}-${++this.counter}`;
    this.queue.push({ id, item });
    return id;
  }

  async dequeue<T>(): Promise<T | null> {
    const entry = this.queue.shift();
    return entry ? (entry.item as T) : null;
  }

  async size(): Promise<number> {
    return this.queue.length;
  }

  async clear(): Promise<void> {
    this.queue = [];
  }
}

/**
 * Default configuration
 */
export const DEFAULT_DEGRADATION_CONFIG: GracefulDegradationConfig = {
  services: [],
  healthCheckInterval: 30000,
  autoRecovery: true,
  maxQueueSize: 1000,
};

/**
 * Graceful Degradation Manager
 */
export class GracefulDegradation {
  private config: GracefulDegradationConfig;
  private serviceStatus: Map<string, HealthCheckResult>;
  private currentLevel: DegradationLevel = 'full';
  private events: DegradationEvent[] = [];
  private eventCounter = 0;
  private healthCheckTimer?: NodeJS.Timeout;
  private cache: CacheProvider;
  private queue: QueueProvider;

  constructor(config?: Partial<GracefulDegradationConfig>) {
    this.config = { ...DEFAULT_DEGRADATION_CONFIG, ...config };
    this.serviceStatus = new Map();
    this.cache = config?.cacheProvider ?? new MemoryCacheProvider();
    this.queue = config?.queueProvider ?? new MemoryQueueProvider();

    // Initialize service status
    for (const service of this.config.services) {
      this.serviceStatus.set(service.name, {
        service: service.name,
        status: 'unknown',
      });
    }
  }

  /**
   * Start health monitoring
   */
  start(): void {
    this.runHealthChecks();
    this.healthCheckTimer = setInterval(
      () => this.runHealthChecks(),
      this.config.healthCheckInterval
    );
  }

  /**
   * Stop health monitoring
   */
  stop(): void {
    if (this.healthCheckTimer) {
      clearInterval(this.healthCheckTimer);
      this.healthCheckTimer = undefined;
    }
  }

  /**
   * Register a service
   */
  registerService(service: ServiceConfig): void {
    this.config.services.push(service);
    this.serviceStatus.set(service.name, {
      service: service.name,
      status: 'unknown',
    });
  }

  /**
   * Execute operation with graceful degradation
   */
  async execute<T>(
    serviceName: string,
    operation: () => Promise<T>,
    options?: {
      cacheKey?: string;
      defaultValue?: T;
      timeout?: number;
    }
  ): Promise<DegradedResult<T>> {
    const service = this.config.services.find((s) => s.name === serviceName);
    const status = this.serviceStatus.get(serviceName);

    // Try normal operation if service is healthy
    if (!status || status.status === 'healthy' || status.status === 'unknown') {
      try {
        const value = await this.withTimeout(operation, options?.timeout ?? 30000);
        
        // Cache successful result
        if (options?.cacheKey) {
          await this.cache.set(options.cacheKey, value, service?.cacheTtl);
        }
        
        return {
          value,
          degraded: false,
          level: this.currentLevel,
          warnings: [],
        };
      } catch (error) {
        // Service failed, try fallback
        return this.executeFallback(serviceName, error as Error, options);
      }
    }

    // Service is not healthy, go straight to fallback
    return this.executeFallback(
      serviceName, 
      new Error(`Service ${serviceName} is ${status.status}`),
      options
    );
  }

  /**
   * Execute fallback strategy
   */
  private async executeFallback<T>(
    serviceName: string,
    error: Error,
    options?: {
      cacheKey?: string;
      defaultValue?: T;
      timeout?: number;
    }
  ): Promise<DegradedResult<T>> {
    const service = this.config.services.find((s) => s.name === serviceName);
    const strategies = service?.fallbackStrategies ?? ['default'];
    const warnings: string[] = [`Primary operation failed: ${error.message}`];

    for (const strategy of strategies) {
      try {
        const result = await this.executeStrategy<T>(
          serviceName, 
          strategy, 
          options
        );
        
        if (result !== null) {
          return {
            value: result,
            degraded: true,
            level: this.currentLevel,
            strategy,
            originalError: error,
            warnings,
          };
        }
      } catch (e) {
        warnings.push(`Fallback ${strategy} failed: ${(e as Error).message}`);
      }
    }

    // All fallbacks failed
    throw new Error(
      `All fallback strategies failed for ${serviceName}. ` +
      `Warnings: ${warnings.join('; ')}`
    );
  }

  /**
   * Execute a specific strategy
   */
  private async executeStrategy<T>(
    serviceName: string,
    strategy: FallbackStrategy,
    options?: {
      cacheKey?: string;
      defaultValue?: T;
    }
  ): Promise<T | null> {
    const service = this.config.services.find((s) => s.name === serviceName);

    switch (strategy) {
      case 'cache':
        if (options?.cacheKey) {
          const cached = await this.cache.get<T>(options.cacheKey);
          if (cached !== null) return cached;
        }
        return null;

      case 'default':
        if (options?.defaultValue !== undefined) {
          return options.defaultValue;
        }
        return null;

      case 'retry':
        // Retry logic would go here, but we've already failed
        // This is more of a pre-failure strategy
        return null;

      case 'alternative':
        if (service?.alternative) {
          const altService = this.config.services.find(
            (s) => s.name === service.alternative
          );
          if (altService) {
            // Would execute alternative service here
            // For now, return null
          }
        }
        return null;

      case 'skip':
        // Skip returns null to indicate operation skipped
        return null;

      case 'queue':
        // Queue for later processing
        if (await this.queue.size() < this.config.maxQueueSize) {
          await this.queue.enqueue({
            service: serviceName,
            timestamp: new Date(),
            options,
          });
        }
        return null;

      case 'manual':
        // Require manual intervention
        return null;

      default:
        return null;
    }
  }

  /**
   * Run health checks on all services
   */
  async runHealthChecks(): Promise<Map<string, HealthCheckResult>> {
    const results = new Map<string, HealthCheckResult>();

    for (const service of this.config.services) {
      const result = await this.checkServiceHealth(service);
      results.set(service.name, result);
      
      const previousStatus = this.serviceStatus.get(service.name);
      this.serviceStatus.set(service.name, result);

      // Handle status changes
      if (previousStatus?.status !== result.status) {
        if (result.status === 'unavailable' || result.status === 'degraded') {
          this.handleServiceDegradation(service, result, previousStatus?.status);
        } else if (result.status === 'healthy' && previousStatus?.status !== 'healthy') {
          this.handleServiceRecovery(service);
        }
      }
    }

    // Recalculate overall degradation level
    this.recalculateLevel();

    return results;
  }

  /**
   * Check health of a single service
   */
  private async checkServiceHealth(service: ServiceConfig): Promise<HealthCheckResult> {
    const startTime = Date.now();
    
    try {
      const healthy = await this.withTimeout(service.healthCheck, 5000);
      const responseTime = Date.now() - startTime;
      
      return {
        service: service.name,
        status: healthy ? 'healthy' : 'degraded',
        responseTime,
        lastSuccess: healthy ? new Date() : undefined,
      };
    } catch (error) {
      return {
        service: service.name,
        status: 'unavailable',
        responseTime: Date.now() - startTime,
        error: (error as Error).message,
      };
    }
  }

  /**
   * Handle service degradation
   */
  private handleServiceDegradation(
    service: ServiceConfig,
    result: HealthCheckResult,
    _previousStatus?: ServiceStatus
  ): void {
    const previousLevel = this.currentLevel;
    
    const event: DegradationEvent = {
      id: `deg-${Date.now()}-${++this.eventCounter}`,
      timestamp: new Date(),
      service: service.name,
      previousLevel,
      newLevel: this.currentLevel,
      reason: result.error ?? `Service ${service.name} is ${result.status}`,
    };

    this.events.push(event);
    this.config.onDegradation?.(event);
  }

  /**
   * Handle service recovery
   */
  private handleServiceRecovery(service: ServiceConfig): void {
    this.config.onRecovery?.(service.name, this.currentLevel);
    
    // Process queued items for this service
    if (this.config.autoRecovery) {
      this.processQueue(service.name).catch(() => {});
    }
  }

  /**
   * Process queued items
   */
  private async processQueue(serviceName: string): Promise<void> {
    let processed = 0;
    const maxProcess = 10;

    while (processed < maxProcess) {
      const item = await this.queue.dequeue<{ service: string }>();
      if (!item) break;
      if (item.service === serviceName) {
        // Would re-execute the queued operation here
        processed++;
      } else {
        // Re-queue if not for this service
        await this.queue.enqueue(item);
      }
    }
  }

  /**
   * Recalculate overall degradation level
   */
  private recalculateLevel(): void {
    const statuses = [...this.serviceStatus.values()];
    
    // Count unavailable required services
    const unavailableRequired = this.config.services.filter(
      (s) => s.required && this.serviceStatus.get(s.name)?.status === 'unavailable'
    );

    // Count total unavailable
    const totalUnavailable = statuses.filter(
      (s) => s.status === 'unavailable'
    ).length;

    // Count degraded
    const totalDegraded = statuses.filter(
      (s) => s.status === 'degraded'
    ).length;

    // Determine level
    if (unavailableRequired.length > 0) {
      this.currentLevel = 'emergency';
    } else if (totalUnavailable > statuses.length / 2) {
      this.currentLevel = 'offline';
    } else if (totalUnavailable > 0) {
      this.currentLevel = 'minimal';
    } else if (totalDegraded > 0) {
      this.currentLevel = 'reduced';
    } else {
      this.currentLevel = 'full';
    }
  }

  /**
   * Get current degradation level
   */
  getLevel(): DegradationLevel {
    return this.currentLevel;
  }

  /**
   * Get service status
   */
  getServiceStatus(serviceName: string): HealthCheckResult | undefined {
    return this.serviceStatus.get(serviceName);
  }

  /**
   * Get all service statuses
   */
  getAllStatuses(): Map<string, HealthCheckResult> {
    return new Map(this.serviceStatus);
  }

  /**
   * Get degradation events
   */
  getEvents(limit?: number): DegradationEvent[] {
    const events = [...this.events].sort(
      (a, b) => b.timestamp.getTime() - a.timestamp.getTime()
    );
    return limit ? events.slice(0, limit) : events;
  }

  /**
   * Check if a feature is available at current level
   */
  isFeatureAvailable(requiredLevel: DegradationLevel): boolean {
    const levels: DegradationLevel[] = ['full', 'reduced', 'minimal', 'offline', 'emergency'];
    return levels.indexOf(this.currentLevel) <= levels.indexOf(requiredLevel);
  }

  /**
   * Cache a value
   */
  async cacheValue<T>(key: string, value: T, ttl?: number): Promise<void> {
    await this.cache.set(key, value, ttl);
  }

  /**
   * Get cached value
   */
  async getCachedValue<T>(key: string): Promise<T | null> {
    return this.cache.get<T>(key);
  }

  /**
   * Clear cache
   */
  async clearCache(): Promise<void> {
    await this.cache.clear();
  }

  /**
   * Execute with timeout
   */
  private async withTimeout<T>(
    operation: () => Promise<T>,
    timeout: number
  ): Promise<T> {
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        reject(new Error(`Operation timed out after ${timeout}ms`));
      }, timeout);

      operation()
        .then((result) => {
          clearTimeout(timer);
          resolve(result);
        })
        .catch((error) => {
          clearTimeout(timer);
          reject(error);
        });
    });
  }
}

/**
 * Create graceful degradation instance
 */
export function createGracefulDegradation(
  config?: Partial<GracefulDegradationConfig>
): GracefulDegradation {
  return new GracefulDegradation(config);
}

/**
 * Retry with exponential backoff
 */
export async function retryWithBackoff<T>(
  operation: () => Promise<T>,
  options?: {
    maxAttempts?: number;
    initialDelay?: number;
    maxDelay?: number;
    backoffFactor?: number;
  }
): Promise<T> {
  const maxAttempts = options?.maxAttempts ?? 3;
  const initialDelay = options?.initialDelay ?? 1000;
  const maxDelay = options?.maxDelay ?? 30000;
  const backoffFactor = options?.backoffFactor ?? 2;

  let lastError: Error | undefined;
  let delay = initialDelay;

  for (let attempt = 1; attempt <= maxAttempts; attempt++) {
    try {
      return await operation();
    } catch (error) {
      lastError = error as Error;
      
      if (attempt < maxAttempts) {
        await new Promise((resolve) => setTimeout(resolve, delay));
        delay = Math.min(delay * backoffFactor, maxDelay);
      }
    }
  }

  throw lastError ?? new Error('Operation failed after retries');
}

/**
 * Circuit breaker
 */
export class CircuitBreaker {
  private failures = 0;
  private lastFailure?: Date;
  private state: 'closed' | 'open' | 'half-open' = 'closed';

  constructor(
    private readonly threshold: number = 5,
    private readonly resetTimeout: number = 60000
  ) {}

  async execute<T>(operation: () => Promise<T>): Promise<T> {
    if (this.state === 'open') {
      if (this.shouldAttemptReset()) {
        this.state = 'half-open';
      } else {
        throw new Error('Circuit breaker is open');
      }
    }

    try {
      const result = await operation();
      this.onSuccess();
      return result;
    } catch (error) {
      this.onFailure();
      throw error;
    }
  }

  private shouldAttemptReset(): boolean {
    if (!this.lastFailure) return true;
    return Date.now() - this.lastFailure.getTime() > this.resetTimeout;
  }

  private onSuccess(): void {
    this.failures = 0;
    this.state = 'closed';
  }

  private onFailure(): void {
    this.failures++;
    this.lastFailure = new Date();
    
    if (this.failures >= this.threshold) {
      this.state = 'open';
    }
  }

  getState(): 'closed' | 'open' | 'half-open' {
    return this.state;
  }

  reset(): void {
    this.failures = 0;
    this.lastFailure = undefined;
    this.state = 'closed';
  }
}
