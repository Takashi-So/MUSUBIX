/**
 * Lazy Loading Module
 *
 * Provides lazy loading for heavy modules to improve CLI startup time.
 *
 * @packageDocumentation
 * @module cli/lazy-loader
 * @see REQ-NFR-002 - Command response performance
 * @see DES-NFR-002 - Performance optimization design
 */

/**
 * Lazy loader state
 */
interface LazyState<T> {
  loaded: boolean;
  value?: T;
  loading?: Promise<T>;
}

/**
 * Create a lazy loader for a module
 *
 * @param loader - Function that loads the module
 * @returns Proxy that loads the module on first access
 *
 * @example
 * ```typescript
 * const heavyModule = createLazyLoader(() => import('./heavy-module'));
 * // Module is not loaded yet
 *
 * const result = await heavyModule.doSomething();
 * // Module is loaded on first access
 * ```
 */
export function createLazyLoader<T>(loader: () => Promise<T>): () => Promise<T> {
  const state: LazyState<T> = { loaded: false };

  return async (): Promise<T> => {
    if (state.loaded && state.value !== undefined) {
      return state.value;
    }

    if (state.loading) {
      return state.loading;
    }

    state.loading = loader().then((value) => {
      state.value = value;
      state.loaded = true;
      state.loading = undefined;
      return value;
    });

    return state.loading;
  };
}

/**
 * Create a synchronous lazy loader
 *
 * @param loader - Function that creates the value
 * @returns Function that returns the value, loading it on first access
 */
export function createSyncLazyLoader<T>(loader: () => T): () => T {
  let loaded = false;
  let value: T;

  return (): T => {
    if (!loaded) {
      value = loader();
      loaded = true;
    }
    return value;
  };
}

/**
 * Lazy module registry for managing multiple lazy-loaded modules
 */
export class LazyModuleRegistry {
  private modules: Map<string, () => Promise<unknown>> = new Map();
  private loaded: Map<string, unknown> = new Map();

  /**
   * Register a module for lazy loading
   */
  register<T>(name: string, loader: () => Promise<T>): void {
    this.modules.set(name, loader);
  }

  /**
   * Get a lazy-loaded module
   */
  async get<T>(name: string): Promise<T> {
    // Return cached module if already loaded
    if (this.loaded.has(name)) {
      return this.loaded.get(name) as T;
    }

    // Get loader
    const loader = this.modules.get(name);
    if (!loader) {
      throw new Error(`Module not registered: ${name}`);
    }

    // Load and cache
    const module = await loader();
    this.loaded.set(name, module);
    return module as T;
  }

  /**
   * Check if a module is registered
   */
  has(name: string): boolean {
    return this.modules.has(name);
  }

  /**
   * Check if a module is already loaded
   */
  isLoaded(name: string): boolean {
    return this.loaded.has(name);
  }

  /**
   * Preload specific modules
   */
  async preload(names: string[]): Promise<void> {
    await Promise.all(names.map((name) => this.get(name)));
  }

  /**
   * Clear all loaded modules (for testing)
   */
  clear(): void {
    this.loaded.clear();
  }

  /**
   * Get list of registered modules
   */
  getRegisteredModules(): string[] {
    return Array.from(this.modules.keys());
  }

  /**
   * Get list of loaded modules
   */
  getLoadedModules(): string[] {
    return Array.from(this.loaded.keys());
  }
}

/**
 * Global lazy module registry
 */
export const globalLazyRegistry = new LazyModuleRegistry();

/**
 * Decorator-like function for lazy property initialization
 */
export function lazyProperty<T>(initializer: () => T): { get: () => T } {
  let initialized = false;
  let value: T;

  return {
    get: (): T => {
      if (!initialized) {
        value = initializer();
        initialized = true;
      }
      return value;
    },
  };
}

/**
 * Lazy initialization wrapper for classes
 *
 * @example
 * ```typescript
 * class HeavyService {
 *   private data = lazyInit(() => this.loadData());
 *
 *   getData() {
 *     return this.data.value;
 *   }
 *
 *   private loadData() {
 *     // Expensive operation
 *     return { ... };
 *   }
 * }
 * ```
 */
export function lazyInit<T>(initializer: () => T): { value: T } {
  const prop = lazyProperty(initializer);
  return {
    get value(): T {
      return prop.get();
    },
  };
}

/**
 * Batch loader for loading multiple items with deduplication
 */
export class BatchLoader<K, V> {
  private pending: Map<K, Promise<V>> = new Map();
  private cache: Map<K, V> = new Map();
  private batchFn: (keys: K[]) => Promise<Map<K, V>>;
  private batchDelay: number;
  private batchKeys: K[] = [];
  private batchTimer: ReturnType<typeof setTimeout> | null = null;
  private batchResolvers: Map<K, { resolve: (v: V) => void; reject: (e: Error) => void }> =
    new Map();

  constructor(batchFn: (keys: K[]) => Promise<Map<K, V>>, batchDelay: number = 10) {
    this.batchFn = batchFn;
    this.batchDelay = batchDelay;
  }

  /**
   * Load a single item (batched with other loads)
   */
  async load(key: K): Promise<V> {
    // Return from cache
    if (this.cache.has(key)) {
      return this.cache.get(key)!;
    }

    // Return pending request
    if (this.pending.has(key)) {
      return this.pending.get(key)!;
    }

    // Add to batch
    return new Promise<V>((resolve, reject) => {
      this.batchKeys.push(key);
      this.batchResolvers.set(key, { resolve, reject });

      if (!this.batchTimer) {
        this.batchTimer = setTimeout(() => this.executeBatch(), this.batchDelay);
      }
    });
  }

  private async executeBatch(): Promise<void> {
    const keys = [...this.batchKeys];
    const resolvers = new Map(this.batchResolvers);

    this.batchKeys = [];
    this.batchResolvers.clear();
    this.batchTimer = null;

    try {
      const results = await this.batchFn(keys);

      for (const key of keys) {
        const resolver = resolvers.get(key);
        if (resolver) {
          const value = results.get(key);
          if (value !== undefined) {
            this.cache.set(key, value);
            resolver.resolve(value);
          } else {
            resolver.reject(new Error(`Value not found for key: ${key}`));
          }
        }
      }
    } catch (error) {
      for (const key of keys) {
        const resolver = resolvers.get(key);
        if (resolver) {
          resolver.reject(error instanceof Error ? error : new Error(String(error)));
        }
      }
    }
  }

  /**
   * Load multiple items
   */
  async loadMany(keys: K[]): Promise<V[]> {
    return Promise.all(keys.map((key) => this.load(key)));
  }

  /**
   * Clear the cache
   */
  clearCache(): void {
    this.cache.clear();
  }

  /**
   * Prime the cache with a value
   */
  prime(key: K, value: V): void {
    this.cache.set(key, value);
  }
}
