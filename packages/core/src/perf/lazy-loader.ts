/**
 * Lazy Loader - Deferred module loading
 *
 * @module perf/lazy-loader
 * @traces DES-PERF-001, REQ-PERF-001
 * @pattern Proxy / Virtual Proxy
 */

import { LazyNotLoadedError } from './types.js';

/**
 * Module cache for lazy-loaded modules
 */
const moduleCache = new Map<string, unknown>();

/**
 * Pending loads to prevent duplicate loading
 */
const pendingLoads = new Map<string, Promise<unknown>>();

/**
 * Create a lazy-loaded module proxy
 *
 * This creates a proxy that will throw an error if accessed before loading.
 * Use `lazyLoad` for async access.
 *
 * @param importFn - Function that returns import promise
 * @param moduleId - Unique identifier for the module
 * @returns Proxy object that throws if accessed before loading
 *
 * @example
 * ```typescript
 * const validators = lazyImport(
 *   () => import('./validators/index.js'),
 *   'validators'
 * );
 *
 * // Later, when needed:
 * await ensureLoaded('validators');
 * validators.validateEARS(text);
 * ```
 */
export function lazyImport<T extends object>(
  importFn: () => Promise<T>,
  moduleId: string
): T {
  // Register the import function for later loading
  if (!pendingLoads.has(moduleId) && !moduleCache.has(moduleId)) {
    // Store the import function for deferred execution
    Object.defineProperty(lazyImport, `__import_${moduleId}`, {
      value: importFn,
      configurable: true,
    });
  }

  return new Proxy({} as T, {
    get(_, prop) {
      const cached = moduleCache.get(moduleId);
      if (cached) {
        return (cached as Record<string | symbol, unknown>)[prop];
      }
      throw new LazyNotLoadedError(moduleId, prop);
    },
    has(_, prop) {
      const cached = moduleCache.get(moduleId);
      if (cached) {
        return prop in (cached as object);
      }
      return false;
    },
    ownKeys() {
      const cached = moduleCache.get(moduleId);
      if (cached) {
        return Reflect.ownKeys(cached as object);
      }
      return [];
    },
  });
}

/**
 * Asynchronously load a lazy module
 *
 * @param importFn - Function that returns import promise
 * @param moduleId - Optional module ID for caching
 * @returns Loaded module
 *
 * @example
 * ```typescript
 * const validators = await lazyLoad(
 *   () => import('./validators/index.js'),
 *   'validators'
 * );
 * validators.validateEARS(text);
 * ```
 */
export async function lazyLoad<T>(
  importFn: () => Promise<T>,
  moduleId?: string
): Promise<T> {
  // If we have a moduleId, check cache first
  if (moduleId) {
    const cached = moduleCache.get(moduleId);
    if (cached) {
      return cached as T;
    }

    // Check if already loading
    const pending = pendingLoads.get(moduleId);
    if (pending) {
      return pending as Promise<T>;
    }

    // Start loading
    const loadPromise = importFn().then((module) => {
      moduleCache.set(moduleId, module);
      pendingLoads.delete(moduleId);
      return module;
    });

    pendingLoads.set(moduleId, loadPromise);
    return loadPromise;
  }

  // No moduleId, just load directly
  return importFn();
}

/**
 * Ensure a lazy module is loaded
 *
 * @param moduleId - Module ID to ensure is loaded
 * @returns Promise that resolves when module is loaded
 */
export async function ensureLoaded(moduleId: string): Promise<void> {
  if (moduleCache.has(moduleId)) {
    return;
  }

  const pending = pendingLoads.get(moduleId);
  if (pending) {
    await pending;
    return;
  }

  // Try to get the registered import function
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const importFn = (lazyImport as any)[`__import_${moduleId}`];
  if (typeof importFn === 'function') {
    await lazyLoad(importFn as () => Promise<unknown>, moduleId);
  } else {
    throw new Error(`Module '${moduleId}' has no registered import function`);
  }
}

/**
 * Check if a module is loaded
 *
 * @param moduleId - Module ID to check
 * @returns True if module is loaded
 */
export function isLoaded(moduleId: string): boolean {
  return moduleCache.has(moduleId);
}

/**
 * Preload modules for better performance
 *
 * @param moduleIds - Module IDs to preload
 * @returns Promise that resolves when all modules are loaded
 */
export async function preloadModules(moduleIds: string[]): Promise<void> {
  await Promise.all(moduleIds.map(ensureLoaded));
}

/**
 * Clear module cache (useful for testing)
 *
 * @param moduleId - Optional specific module to clear
 */
export function clearModuleCache(moduleId?: string): void {
  if (moduleId) {
    moduleCache.delete(moduleId);
    pendingLoads.delete(moduleId);
  } else {
    moduleCache.clear();
    pendingLoads.clear();
  }
}

/**
 * Get module cache stats
 */
export function getModuleCacheStats(): { loaded: number; pending: number; moduleIds: string[] } {
  return {
    loaded: moduleCache.size,
    pending: pendingLoads.size,
    moduleIds: Array.from(moduleCache.keys()),
  };
}

/**
 * Create a lazy loader for a specific module
 *
 * @param importFn - Import function
 * @param moduleId - Module ID
 * @returns Object with sync proxy and async loader
 */
export function createLazyModule<T extends object>(
  importFn: () => Promise<T>,
  moduleId: string
): { proxy: T; load: () => Promise<T>; isLoaded: () => boolean } {
  const proxy = lazyImport(importFn, moduleId);

  return {
    proxy,
    load: () => lazyLoad(importFn, moduleId),
    isLoaded: () => isLoaded(moduleId),
  };
}
