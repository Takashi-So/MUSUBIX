// Jina AI Provider Tests
// TSK-DR-007

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { JinaProvider } from './jina-provider.js';
import type { SERPQuery, WebReadRequest } from '../types/index.js';

// Mock fetch globally
global.fetch = vi.fn();

describe('JinaProvider', () => {
  let provider: JinaProvider;
  let mockFetch: ReturnType<typeof vi.fn>;

  beforeEach(() => {
    provider = new JinaProvider(5000);
    mockFetch = global.fetch as ReturnType<typeof vi.fn>;
    mockFetch.mockClear();
  });

  describe('search', () => {
    it('should search and return results', async () => {
      const query: SERPQuery = {
        keywords: 'TypeScript authentication',
        topK: 5,
        timestamp: Date.now(),
        iteration: 0,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          data: [
            {
              title: 'TypeScript Auth Guide',
              url: 'https://example.com/ts-auth',
              snippet: 'Learn TypeScript authentication',
            },
            {
              title: 'Auth Best Practices',
              url: 'https://example.com/best-practices',
              snippet: 'Best practices for auth',
            },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(2);
      expect(results[0].title).toBe('TypeScript Auth Guide');
      expect(results[0].url).toBe('https://example.com/ts-auth');
      expect(results[0].relevance).toBeGreaterThan(0.5);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('s.jina.ai'),
        expect.objectContaining({
          headers: expect.objectContaining({
            Accept: 'application/json',
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
        json: async () => ({ data: [] }),
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

      await expect(provider.search(query)).rejects.toThrow('Jina AI search failed');
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
          data: [
            { title: 'R1', url: 'https://example.com/1', snippet: 'S1' },
            { title: 'R2', url: 'https://example.com/2', snippet: 'S2' },
            { title: 'R3', url: 'https://example.com/3', snippet: 'S3' },
          ],
        }),
      });

      const results = await provider.search(query);

      expect(results).toHaveLength(2);
    });
  });

  describe('read', () => {
    it('should read web content', async () => {
      const request: WebReadRequest = {
        url: 'https://example.com/article',
        timeout: 5000,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          title: 'Test Article',
          content: 'This is a test article with some meaningful content that should be extracted as facts.\n\nAnother paragraph with more information about the topic.',
          author: 'John Doe',
          publishedDate: '2024-01-01',
        }),
      });

      const content = await provider.read(request);

      expect(content.url).toBe('https://example.com/article');
      expect(content.title).toBe('Test Article');
      expect(content.content).toContain('test article');
      expect(content.extractedFacts.length).toBeGreaterThan(0);
    });

    it('should handle read errors', async () => {
      const request: WebReadRequest = {
        url: 'https://example.com/not-found',
        timeout: 5000,
      };

      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 404,
        statusText: 'Not Found',
      });

      await expect(provider.read(request)).rejects.toThrow('Jina AI reader failed');
    });

    it('should extract title from URL when not provided', async () => {
      const request: WebReadRequest = {
        url: 'https://example.com/my-article-title',
        timeout: 5000,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({
          content: 'Article content',
        }),
      });

      const content = await provider.read(request);

      expect(content.title).toContain('My Article Title');
    });
  });

  describe('isAvailable', () => {
    it('should return true when Jina AI is available', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
      });

      const available = await provider.isAvailable();

      expect(available).toBe(true);
    });

    it('should return false when Jina AI is unavailable', async () => {
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
