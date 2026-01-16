// Search Provider Factory Tests
// TSK-DR-006

import { describe, it, expect, beforeEach } from 'vitest';
import { SearchProviderFactory } from './provider-factory.js';
import { MockSearchProvider } from '../test/mocks/mock-search-provider.js';
import { AllProvidersFailedError } from '../types/errors.js';
import type { SERPQuery } from '../types/index.js';

describe('SearchProviderFactory', () => {
  let factory: SearchProviderFactory;
  let query: SERPQuery;

  beforeEach(() => {
    factory = new SearchProviderFactory();
    query = {
      keywords: 'test query',
      topK: 5,
      timestamp: Date.now(),
      iteration: 0,
    };
  });

  it('should register providers', () => {
    const provider = new MockSearchProvider('TestProvider');
    factory.register(provider);
    
    expect(factory.getProviderNames()).toContain('TestProvider');
    expect(factory.getProvider('TestProvider')).toBe(provider);
  });

  it('should search with primary provider', async () => {
    const provider = new MockSearchProvider('Primary');
    provider.setResults([
      { title: 'Result 1', url: 'https://example.com/1', snippet: 'Snippet 1', relevance: 0.9 },
    ]);
    
    factory.register(provider);
    const results = await factory.search(query);
    
    expect(results).toHaveLength(1);
    expect(results[0].title).toBe('Result 1');
    expect(provider.getCallCount()).toBe(1);
  });

  it('should fallback to secondary provider when primary fails', async () => {
    const primary = new MockSearchProvider('Primary');
    const secondary = new MockSearchProvider('Secondary');
    
    primary.setShouldFail(true);
    secondary.setResults([
      { title: 'Fallback Result', url: 'https://example.com/fallback', snippet: 'Fallback', relevance: 0.8 },
    ]);
    
    factory.register(primary, { maxRetries: 2 }); // Reduce retries for faster test
    factory.register(secondary);
    
    const results = await factory.search(query);
    
    expect(results).toHaveLength(1);
    expect(results[0].title).toBe('Fallback Result');
    expect(primary.getCallCount()).toBe(3); // 1 initial + 2 retries
    expect(secondary.getCallCount()).toBe(1);
  }, 10000); // 10s timeout

  it('should throw AllProvidersFailedError when all providers fail', async () => {
    const provider1 = new MockSearchProvider('Provider1');
    const provider2 = new MockSearchProvider('Provider2');
    
    provider1.setShouldFail(true);
    provider2.setShouldFail(true);
    
    factory.register(provider1, { maxRetries: 1 }); // Reduce retries for faster test
    factory.register(provider2, { maxRetries: 1 });
    
    await expect(factory.search(query)).rejects.toThrow(AllProvidersFailedError);
  }, 10000); // 10s timeout

  it('should skip unavailable providers', async () => {
    const unavailable = new MockSearchProvider('Unavailable');
    const available = new MockSearchProvider('Available');
    
    unavailable.setAvailable(false);
    available.setResults([
      { title: 'Available Result', url: 'https://example.com/available', snippet: 'Available', relevance: 0.9 },
    ]);
    
    factory.register(unavailable);
    factory.register(available);
    
    const results = await factory.search(query);
    
    expect(results).toHaveLength(1);
    expect(results[0].title).toBe('Available Result');
    expect(unavailable.getCallCount()).toBe(0); // Not called because unavailable
    expect(available.getCallCount()).toBe(1);
  });

  it('should skip disabled providers', async () => {
    const disabled = new MockSearchProvider('Disabled');
    const enabled = new MockSearchProvider('Enabled');
    
    disabled.setResults([
      { title: 'Disabled Result', url: 'https://example.com/disabled', snippet: 'Disabled', relevance: 0.9 },
    ]);
    enabled.setResults([
      { title: 'Enabled Result', url: 'https://example.com/enabled', snippet: 'Enabled', relevance: 0.9 },
    ]);
    
    factory.register(disabled);
    factory.register(enabled);
    factory.setProviderEnabled('Disabled', false);
    
    const results = await factory.search(query);
    
    expect(results).toHaveLength(1);
    expect(results[0].title).toBe('Enabled Result');
  });

  it('should get provider status', async () => {
    const provider1 = new MockSearchProvider('Provider1');
    
    factory.register(provider1);
    
    const status = await factory.getProviderStatus();
    
    expect(status).toHaveLength(1);
    expect(status[0]).toEqual({ name: 'Provider1', enabled: true, available: true });
  });

  it('should clear all providers', () => {
    const provider = new MockSearchProvider('Test');
    factory.register(provider);
    
    expect(factory.getProviderNames()).toHaveLength(1);
    
    factory.clear();
    
    expect(factory.getProviderNames()).toHaveLength(0);
  });

  it('should retry with exponential backoff on failure', async () => {
    const provider = new MockSearchProvider('RetryTest');
    let callCount = 0;
    
    // Fail first 2 attempts, succeed on 3rd
    provider.setShouldFail(true);
    const originalSearch = provider.search.bind(provider);
    provider.search = async (q) => {
      callCount++;
      if (callCount <= 2) {
        throw new Error('Simulated failure');
      }
      provider.setShouldFail(false);
      return originalSearch(q);
    };
    
    provider.setResults([
      { title: 'Success', url: 'https://example.com/success', snippet: 'Success', relevance: 0.9 },
    ]);
    
    factory.register(provider, { maxRetries: 3 });
    
    const results = await factory.search(query);
    
    expect(results).toHaveLength(1);
    expect(callCount).toBe(3); // Failed twice, succeeded on 3rd
  }, 10000); // 10s timeout
});
