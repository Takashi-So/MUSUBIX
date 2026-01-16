// DuckDuckGo Search Provider Tests
// TSK-DR-009

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { DuckDuckGoProvider } from './duckduckgo-provider.js';
import type { SERPQuery } from '../types/index.js';

// Mock fetch globally
global.fetch = vi.fn();

describe('DuckDuckGoProvider', () => {
  let provider: DuckDuckGoProvider;
  let mockFetch: ReturnType<typeof vi.fn>;

  beforeEach(() => {
    provider = new DuckDuckGoProvider(5000);
    mockFetch = global.fetch as ReturnType<typeof vi.fn>;
    mockFetch.mockClear();
  });

  describe('search', () => {
    it('should search and return results with abstract', async () => {
      const query: SERPQuery = {
        keywords: 'TypeScript',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          Heading: 'TypeScript',
          Abstract: 'TypeScript is a strongly typed programming language',
          AbstractURL: 'https://www.typescriptlang.org/',
          RelatedTopics: [
            {
              FirstURL: 'https://example.com/ts-intro',
              Text: 'TypeScript Introduction - Learn the basics',
            },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results.length).toBeGreaterThan(0);
      expect(results[0].title).toBe('TypeScript');
      expect(results[0].url).toBe('https://www.typescriptlang.org/');
      expect(results[0].relevance).toBe(0.95);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('api.duckduckgo.com'),
        expect.any(Object)
      );
    });

    it('should parse related topics', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          RelatedTopics: [
            {
              FirstURL: 'https://example.com/1',
              Text: 'Topic 1 - Description',
            },
            {
              FirstURL: 'https://example.com/2',
              Text: 'Topic 2 - Description',
            },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(2);
      expect(results[0].title).toBe('Topic 1');
      expect(results[1].title).toBe('Topic 2');
    });

    it('should parse nested topics', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          RelatedTopics: [
            {
              Topics: [
                {
                  FirstURL: 'https://example.com/nested1',
                  Text: 'Nested Topic 1',
                },
                {
                  FirstURL: 'https://example.com/nested2',
                  Text: 'Nested Topic 2',
                },
              ],
            },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(2);
      expect(results[0].url).toBe('https://example.com/nested1');
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
        json: async () => ({}),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(0);
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

      await expect(provider.search(query)).rejects.toThrow('DuckDuckGo search failed');
    });

    it('should respect topK parameter', async () => {
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
          RelatedTopics: [
            { FirstURL: 'https://example.com/1', Text: 'T1' },
            { FirstURL: 'https://example.com/2', Text: 'T2' },
            { FirstURL: 'https://example.com/3', Text: 'T3' },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(2);
    });

    it('should extract title from text with dash separator', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          RelatedTopics: [
            {
              FirstURL: 'https://example.com/1',
              Text: 'Main Title - Some description here',
            },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results[0].title).toBe('Main Title');
    });

    it('should truncate long text as title', async () => {
      const query: SERPQuery = {
        keywords: 'test',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      const longText = 'A'.repeat(100);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          RelatedTopics: [
            {
              FirstURL: 'https://example.com/1',
              Text: longText,
            },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results[0].title.length).toBeLessThan(65);
      expect(results[0].title).toContain('...');
    });
  });

  describe('isAvailable', () => {
    it('should return true when DuckDuckGo is available', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
      });

      const available = await provider.isAvailable();

      expect(available).toBe(true);
    });

    it('should return false when DuckDuckGo is unavailable', async () => {
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
