/**
 * Lazy Loader module tests
 *
 * @see REQ-NFR-002 - Command response performance
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  createLazyLoader,
  createSyncLazyLoader,
  LazyModuleRegistry,
  globalLazyRegistry,
  lazyProperty,
  lazyInit,
  BatchLoader,
} from './lazy-loader.js';

describe('createLazyLoader', () => {
  it('should not load until accessed', async () => {
    const loader = vi.fn().mockResolvedValue({ value: 42 });
    const lazy = createLazyLoader(loader);

    expect(loader).not.toHaveBeenCalled();

    const result = await lazy();

    expect(loader).toHaveBeenCalledTimes(1);
    expect(result).toEqual({ value: 42 });
  });

  it('should cache the loaded value', async () => {
    const loader = vi.fn().mockResolvedValue('loaded');
    const lazy = createLazyLoader(loader);

    await lazy();
    await lazy();
    await lazy();

    expect(loader).toHaveBeenCalledTimes(1);
  });

  it('should handle concurrent access', async () => {
    let resolveLoader: (value: string) => void;
    const loader = vi.fn().mockImplementation(
      () =>
        new Promise<string>((resolve) => {
          resolveLoader = resolve;
        })
    );
    const lazy = createLazyLoader(loader);

    const promise1 = lazy();
    const promise2 = lazy();
    const promise3 = lazy();

    resolveLoader!('result');

    const [r1, r2, r3] = await Promise.all([promise1, promise2, promise3]);

    expect(loader).toHaveBeenCalledTimes(1);
    expect(r1).toBe('result');
    expect(r2).toBe('result');
    expect(r3).toBe('result');
  });
});

describe('createSyncLazyLoader', () => {
  it('should not load until accessed', () => {
    const loader = vi.fn().mockReturnValue(42);
    const lazy = createSyncLazyLoader(loader);

    expect(loader).not.toHaveBeenCalled();

    const result = lazy();

    expect(loader).toHaveBeenCalledTimes(1);
    expect(result).toBe(42);
  });

  it('should cache the loaded value', () => {
    const loader = vi.fn().mockReturnValue('cached');
    const lazy = createSyncLazyLoader(loader);

    lazy();
    lazy();
    lazy();

    expect(loader).toHaveBeenCalledTimes(1);
  });
});

describe('LazyModuleRegistry', () => {
  let registry: LazyModuleRegistry;

  beforeEach(() => {
    registry = new LazyModuleRegistry();
  });

  it('should register and get modules', async () => {
    registry.register('test-module', async () => ({ api: 'v1' }));

    const module = await registry.get<{ api: string }>('test-module');

    expect(module.api).toBe('v1');
  });

  it('should throw for unregistered modules', async () => {
    await expect(registry.get('unknown')).rejects.toThrow('Module not registered');
  });

  it('should cache loaded modules', async () => {
    const loader = vi.fn().mockResolvedValue({ loaded: true });
    registry.register('cached', loader);

    await registry.get('cached');
    await registry.get('cached');

    expect(loader).toHaveBeenCalledTimes(1);
  });

  it('should check if module is registered', () => {
    registry.register('exists', async () => ({}));

    expect(registry.has('exists')).toBe(true);
    expect(registry.has('not-exists')).toBe(false);
  });

  it('should check if module is loaded', async () => {
    registry.register('lazy', async () => ({}));

    expect(registry.isLoaded('lazy')).toBe(false);

    await registry.get('lazy');

    expect(registry.isLoaded('lazy')).toBe(true);
  });

  it('should preload multiple modules', async () => {
    const loader1 = vi.fn().mockResolvedValue('m1');
    const loader2 = vi.fn().mockResolvedValue('m2');

    registry.register('mod1', loader1);
    registry.register('mod2', loader2);

    await registry.preload(['mod1', 'mod2']);

    expect(registry.isLoaded('mod1')).toBe(true);
    expect(registry.isLoaded('mod2')).toBe(true);
  });

  it('should clear loaded modules', async () => {
    registry.register('to-clear', async () => 'value');
    await registry.get('to-clear');

    expect(registry.isLoaded('to-clear')).toBe(true);

    registry.clear();

    expect(registry.isLoaded('to-clear')).toBe(false);
  });

  it('should list registered modules', () => {
    registry.register('a', async () => ({}));
    registry.register('b', async () => ({}));

    const modules = registry.getRegisteredModules();

    expect(modules).toContain('a');
    expect(modules).toContain('b');
  });

  it('should list loaded modules', async () => {
    registry.register('a', async () => ({}));
    registry.register('b', async () => ({}));

    await registry.get('a');

    const loaded = registry.getLoadedModules();

    expect(loaded).toContain('a');
    expect(loaded).not.toContain('b');
  });
});

describe('globalLazyRegistry', () => {
  it('should be a singleton LazyModuleRegistry', () => {
    expect(globalLazyRegistry).toBeInstanceOf(LazyModuleRegistry);
  });
});

describe('lazyProperty', () => {
  it('should not initialize until accessed', () => {
    const initializer = vi.fn().mockReturnValue('lazy-value');
    const prop = lazyProperty(initializer);

    expect(initializer).not.toHaveBeenCalled();

    const value = prop.get();

    expect(initializer).toHaveBeenCalledTimes(1);
    expect(value).toBe('lazy-value');
  });

  it('should cache the value', () => {
    const initializer = vi.fn().mockReturnValue({ data: true });
    const prop = lazyProperty(initializer);

    prop.get();
    prop.get();
    prop.get();

    expect(initializer).toHaveBeenCalledTimes(1);
  });
});

describe('lazyInit', () => {
  it('should provide lazy value property', () => {
    const initializer = vi.fn().mockReturnValue({ initialized: true });
    const lazy = lazyInit(initializer);

    expect(initializer).not.toHaveBeenCalled();

    const value = lazy.value;

    expect(initializer).toHaveBeenCalledTimes(1);
    expect(value).toEqual({ initialized: true });
  });
});

describe('BatchLoader', () => {
  it('should batch multiple loads', async () => {
    const batchFn = vi.fn().mockImplementation(async (keys: string[]) => {
      const result = new Map<string, string>();
      for (const key of keys) {
        result.set(key, `value-${key}`);
      }
      return result;
    });

    const loader = new BatchLoader(batchFn, 5);

    const [r1, r2, r3] = await Promise.all([
      loader.load('a'),
      loader.load('b'),
      loader.load('c'),
    ]);

    expect(batchFn).toHaveBeenCalledTimes(1);
    expect(batchFn).toHaveBeenCalledWith(['a', 'b', 'c']);
    expect(r1).toBe('value-a');
    expect(r2).toBe('value-b');
    expect(r3).toBe('value-c');
  });

  it('should cache results', async () => {
    const batchFn = vi.fn().mockImplementation(async (keys: string[]) => {
      const result = new Map<string, string>();
      for (const key of keys) {
        result.set(key, `value-${key}`);
      }
      return result;
    });

    const loader = new BatchLoader(batchFn, 5);

    await loader.load('key1');
    await loader.load('key1'); // Should be cached

    expect(batchFn).toHaveBeenCalledTimes(1);
  });

  it('should load many at once', async () => {
    const batchFn = vi.fn().mockImplementation(async (keys: number[]) => {
      const result = new Map<number, number>();
      for (const key of keys) {
        result.set(key, key * 2);
      }
      return result;
    });

    const loader = new BatchLoader(batchFn, 5);

    const results = await loader.loadMany([1, 2, 3]);

    expect(results).toEqual([2, 4, 6]);
  });

  it('should handle errors', async () => {
    const batchFn = vi.fn().mockRejectedValue(new Error('Batch failed'));

    const loader = new BatchLoader(batchFn, 5);

    await expect(loader.load('key')).rejects.toThrow('Batch failed');
  });

  it('should clear cache', async () => {
    const batchFn = vi.fn().mockImplementation(async (keys: string[]) => {
      const result = new Map<string, number>();
      for (const key of keys) {
        result.set(key, Math.random());
      }
      return result;
    });

    const loader = new BatchLoader(batchFn, 5);

    const first = await loader.load('key');
    loader.clearCache();
    const second = await loader.load('key');

    expect(first).not.toBe(second);
    expect(batchFn).toHaveBeenCalledTimes(2);
  });

  it('should allow priming cache', async () => {
    const batchFn = vi.fn();
    const loader = new BatchLoader(batchFn, 5);

    loader.prime('key', 'primed-value');

    const result = await loader.load('key');

    expect(result).toBe('primed-value');
    expect(batchFn).not.toHaveBeenCalled();
  });
});
