// Brave Search Provider Tests
// TSK-DR-008

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { BraveProvider } from './brave-provider.js';
import type { SERPQuery } from '../types/index.js';

// Mock fetch globally
global.fetch = vi.fn();

describe('BraveProvider', () => {
  let provider: BraveProvider;
  let mockFetch: ReturnType<typeof vi.fn>;
  const TEST_API_KEY = 'test-api-key-123';

  beforeEach(() => {
    provider = new BraveProvider(TEST_API_KEY, 5000);
    mockFetch = global.fetch as ReturnType<typeof vi.fn>;
    mockFetch.mockClear();
  });

  describe('constructor', () => {
    it('should throw error if API key is empty', () => {
      expect(() => new BraveProvider('')).toThrow('Brave API key is required');
    });

    it('should throw error if API key is whitespace', () => {
      expect(() => new BraveProvider('   ')).toThrow('Brave API key is required');
    });
  });

  describe('search', () => {
    it('should search and return results', async () => {
      const query: SERPQuery = {
        keywords: 'TypeScript tutorial',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          web: {
            results: [
              {
                title: 'TypeScript Handbook',
                url: 'https://example.com/ts-handbook',
                description: 'Official TypeScript documentation',
              },
              {
                title: 'Learn TypeScript',
                url: 'https://example.com/learn-ts',
                description: 'TypeScript tutorial for beginners',
              },
            ],
          },
        }),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(2);
      expect(results[0].title).toBe('TypeScript Handbook');
      expect(results[0].url).toBe('https://example.com/ts-handbook');
      expect(results[0].relevance).toBeGreaterThan(0.5);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('api.search.brave.com'),
        expect.objectContaining({
          headers: expect.objectContaining({
            'X-Subscription-Token': TEST_API_KEY,
          }),
        })
      );
    });

    it('should handle empty results', async () => {
      const query: SERPQuery = {
        keywords: 'nonexistent query',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ web: { results: [] } }),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(0);
    });

    it('should throw error on rate limit', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 429,
        statusText: 'Too Many Requests',
      });

      await expect(provider.search(query)).rejects.toThrow('rate limit exceeded');
    });

    it('should throw error on failed search', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        statusText: 'Internal Server Error',
      });

      await expect(provider.search(query)).rejects.toThrow('Brave Search failed');
    });

    it('should respect topK parameter', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 3,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          web: {
            results: [
              { title: 'R1', url: 'https://example.com/1', description: 'D1' },
              { title: 'R2', url: 'https://example.com/2', description: 'D2' },
            ],
          },
        }),
      });

      const results = await provider.search(query);

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('count=3'),
        expect.any(Object)
      );
      expect(results).toHaveLength(2);
    });

    it('should calculate higher relevance for items with extra data', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 2,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          web: {
            results: [
              {
                title: 'Rich Result',
                url: 'https://example.com/rich',
                description: 'Has extra data',
                extra_snippets: ['snippet1', 'snippet2'],
                deep_results: ['deep1'],
              },
              {
                title: 'Basic Result',
                url: 'https://example.com/basic',
                description: 'No extra data',
              },
            ],
          },
        }),
      });

      const results = await provider.search(query);

      expect(results[0].relevance).toBeGreaterThan(results[1].relevance);
    });
  });

  describe('isAvailable', () => {
    it('should return true when Brave Search is available', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
      });

      const available = await provider.isAvailable();

      expect(available).toBe(true);
    });

    it('should return true on rate limit (service is up)', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 429,
      });

      const available = await provider.isAvailable();

      expect(available).toBe(true);
    });

    it('should return false when Brave Search is unavailable', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      const available = await provider.isAvailable();

      expect(available).toBe(false);
    });

    it('should return false for 5xx errors', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 503,
      });

      const available = await provider.isAvailable();

      expect(available).toBe(false);
    });
  });
});
