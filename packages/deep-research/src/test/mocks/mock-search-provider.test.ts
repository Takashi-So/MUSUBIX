// Mock Search Provider Tests
// TSK-DR-028

import { describe, it, expect, beforeEach } from 'vitest';
import { MockSearchProvider, createMockSearchResults } from '../mocks/mock-search-provider.js';

describe('MockSearchProvider', () => {
  let mockSearch: MockSearchProvider;

  beforeEach(() => {
    mockSearch = new MockSearchProvider();
  });

  it('should return empty results when no results set', async () => {
    const results = await mockSearch.search({
      keywords: 'test',
      timestamp: Date.now(),
      iteration: 1,
    });

    expect(results).toEqual([]);
  });

  it('should return mock results when set', async () => {
    const mockResults = createMockSearchResults(3);
    mockSearch.setResults(mockResults);

    const results = await mockSearch.search({
      keywords: 'test',
      timestamp: Date.now(),
      iteration: 1,
    });

    expect(results).toHaveLength(3);
    expect(results[0].title).toBe('Mock Result 1');
  });

  it('should respect topK parameter', async () => {
    const mockResults = createMockSearchResults(10);
    mockSearch.setResults(mockResults);

    const results = await mockSearch.search({
      keywords: 'test',
      topK: 3,
      timestamp: Date.now(),
      iteration: 1,
    });

    expect(results).toHaveLength(3);
  });

  it('should track call history', async () => {
    await mockSearch.search({
      keywords: 'query 1',
      timestamp: Date.now(),
      iteration: 1,
    });
    await mockSearch.search({
      keywords: 'query 2',
      timestamp: Date.now(),
      iteration: 2,
    });

    expect(mockSearch.getCallCount()).toBe(2);
    expect(mockSearch.wasQueryMade('query 1')).toBe(true);
  });

  it('should simulate failures when configured', async () => {
    mockSearch.setShouldFail(true);

    await expect(
      mockSearch.search({
        keywords: 'test',
        timestamp: Date.now(),
        iteration: 1,
      })
    ).rejects.toThrow('Simulated failure');
  });

  it('should check availability', async () => {
    expect(await mockSearch.isAvailable()).toBe(true);

    mockSearch.setAvailable(false);
    expect(await mockSearch.isAvailable()).toBe(false);
  });
});

describe('createMockSearchResults', () => {
  it('should create specified number of results', () => {
    const results = createMockSearchResults(5);
    expect(results).toHaveLength(5);
  });

  it('should create results with decreasing relevance', () => {
    const results = createMockSearchResults(3);
    expect(results[0].relevance).toBeGreaterThan(results[1].relevance!);
    expect(results[1].relevance).toBeGreaterThan(results[2].relevance!);
  });
});
