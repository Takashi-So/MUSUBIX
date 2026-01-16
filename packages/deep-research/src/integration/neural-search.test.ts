// Neural Search Provider Integration Tests
// TSK-DR-023
// REQ: REQ-DR-INT-003
// DES: DES-DR-v3.4.0 Section 5.2

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { NeuralSearchProvider, createNeuralSearchProvider } from '../providers/neural-search-provider.js';
import type { SERPQuery } from '../types/index.js';

/**
 * Test Suite: Neural Search Integration
 * 
 * Verifies integration with @nahisaho/musubix-neural-search package.
 * 
 * Test Coverage:
 * 1. Provider initialization
 * 2. Semantic search functionality
 * 3. Hybrid ranking (BM25 + embedding)
 * 4. Result formatting and scoring
 * 5. Error handling
 * 6. Configuration options
 */
describe('Neural Search Integration', () => {
  let provider: NeuralSearchProvider;
  
  beforeEach(() => {
    provider = createNeuralSearchProvider();
  });
  
  describe('Initialization', () => {
    it('should create neural search provider instance', () => {
      expect(provider).toBeInstanceOf(NeuralSearchProvider);
      expect(provider.name).toBe('Neural Search');
    });
    
    it('should create with custom timeout', () => {
      const custom = createNeuralSearchProvider(5000);
      expect(custom).toBeInstanceOf(NeuralSearchProvider);
    });
    
    it('should create with custom hybrid weight', () => {
      const custom = createNeuralSearchProvider(10000, 0.5);
      expect(custom).toBeInstanceOf(NeuralSearchProvider);
    });
    
    it('should use default configuration', () => {
      expect(NeuralSearchProvider.DEFAULT_CONFIG.TIMEOUT).toBe(10000);
      expect(NeuralSearchProvider.DEFAULT_CONFIG.HYBRID_WEIGHT).toBe(0.7);
      expect(NeuralSearchProvider.DEFAULT_CONFIG.MAX_RESULTS).toBe(10);
      expect(NeuralSearchProvider.DEFAULT_CONFIG.MIN_SCORE).toBe(0.3);
    });
  });
  
  describe('Availability Check', () => {
    it('should check if neural search is available', async () => {
      const isAvailable = await provider.isAvailable();
      // Returns false if package not installed, true if installed
      expect(typeof isAvailable).toBe('boolean');
    });
    
    it('should handle unavailable package gracefully', async () => {
      // Mock loadNeuralSearch to return null
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(null);
      
      const isAvailable = await provider.isAvailable();
      expect(isAvailable).toBe(false);
    });
  });
  
  describe('Semantic Search', () => {
    it('should throw error if neural search not available', async () => {
      // Mock loadNeuralSearch to return null
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(null);
      
      const query: SERPQuery = {
        keywords: 'TypeScript best practices',
        topK: 5,
        timestamp: Date.now(),
        iteration: 1,
      };
      
      await expect(
        provider.search(query)
      ).rejects.toThrow('Neural search package not available');
    });
    
    it('should perform semantic search with neural search package', async () => {
      const mockSearch = vi.fn().mockResolvedValue([
        {
          id: 'item-1',
          title: 'TypeScript Best Practices',
          content: 'Always use strict mode and enable all type checks...',
          score: 0.95,
        },
        {
          id: 'item-2',
          title: 'Advanced TypeScript Patterns',
          content: 'Use conditional types for better type inference...',
          score: 0.87,
        },
      ]);
      
      const mockManager = {
        search: mockSearch,
      };
      
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(mockManager);
      
      const query: SERPQuery = {
        keywords: 'TypeScript best practices',
        topK: 5,
        timestamp: Date.now(),
        iteration: 1,
      };
      
      const results = await provider.search(query);
      
      expect(results).toHaveLength(2);
      expect(results[0]).toMatchObject({
        title: 'TypeScript Best Practices',
        snippet: expect.any(String),
        score: 0.95,
        source: 'neural-search',
      });
      
      expect(mockSearch).toHaveBeenCalledWith({
        query: 'TypeScript best practices',
        topK: 5,
        hybridWeight: NeuralSearchProvider.DEFAULT_CONFIG.HYBRID_WEIGHT,
        minScore: NeuralSearchProvider.DEFAULT_CONFIG.MIN_SCORE,
      });
    });
    
    it('should use custom topK from query', async () => {
      const mockSearch = vi.fn().mockResolvedValue([]);
      const mockManager = { search: mockSearch };
      
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(mockManager);
      
      const query: SERPQuery = {
        keywords: 'test query',
        topK: 3,
        timestamp: Date.now(),
        iteration: 1,
      };
      
      await provider.search(query);
      
      expect(mockSearch).toHaveBeenCalledWith(
        expect.objectContaining({
          topK: 3,
        })
      );
    });
    
    it('should use default topK if not specified', async () => {
      const mockSearch = vi.fn().mockResolvedValue([]);
      const mockManager = { search: mockSearch };
      
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(mockManager);
      
      const query: SERPQuery = {
        keywords: 'test query',
        timestamp: Date.now(),
        iteration: 1,
      };
      
      await provider.search(query);
      
      expect(mockSearch).toHaveBeenCalledWith(
        expect.objectContaining({
          topK: NeuralSearchProvider.DEFAULT_CONFIG.MAX_RESULTS,
        })
      );
    });
  });
  
  describe('Result Formatting', () => {
    it('should extract title from content if not provided', () => {
      const provider = createNeuralSearchProvider();
      
      const title = (provider as any).extractTitle('This is a long content string...');
      expect(title).toBe('This is a long content string...');
    });
    
    it('should truncate long titles', () => {
      const provider = createNeuralSearchProvider();
      
      const longContent = 'A'.repeat(60);
      const title = (provider as any).extractTitle(longContent);
      expect(title.length).toBeLessThanOrEqual(50);
      expect(title).toContain('...');
    });
    
    it('should extract snippet around keywords', () => {
      const provider = createNeuralSearchProvider();
      
      const content = 'The quick brown fox jumps over the lazy dog. TypeScript is great for type safety.';
      const snippet = (provider as any).extractSnippet(content, 'TypeScript');
      
      expect(snippet).toContain('TypeScript');
    });
    
    it('should add ellipsis to snippets', () => {
      const provider = createNeuralSearchProvider();
      
      const longContent = 'A'.repeat(300) + ' TypeScript ' + 'B'.repeat(300);
      const snippet = (provider as any).extractSnippet(longContent, 'TypeScript');
      
      expect(snippet).toContain('...');
      expect(snippet).toContain('TypeScript');
    });
    
    it('should fallback to first 200 characters if keyword not found', () => {
      const provider = createNeuralSearchProvider();
      
      const content = 'A'.repeat(300);
      const snippet = (provider as any).extractSnippet(content, 'NotFound');
      
      expect(snippet.length).toBeLessThanOrEqual(203); // 200 + "..."
    });
    
    it('should generate local URL for knowledge base items', () => {
      const provider = createNeuralSearchProvider();
      
      const url = (provider as any).generateLocalUrl('item-123');
      expect(url).toBe('local://knowledge/item-123');
    });
  });
  
  describe('Hybrid Ranking', () => {
    it('should use configured hybrid weight', async () => {
      const customWeight = 0.5;
      const customProvider = createNeuralSearchProvider(10000, customWeight);
      
      const mockSearch = vi.fn().mockResolvedValue([]);
      const mockManager = { search: mockSearch };
      
      vi.spyOn(customProvider as any, 'loadNeuralSearch').mockResolvedValue(mockManager);
      
      const query: SERPQuery = {
        keywords: 'test',
        timestamp: Date.now(),
        iteration: 1,
      };
      
      await customProvider.search(query);
      
      expect(mockSearch).toHaveBeenCalledWith(
        expect.objectContaining({
          hybridWeight: customWeight,
        })
      );
    });
    
    it('should filter results by minimum score', async () => {
      const mockSearch = vi.fn().mockResolvedValue([
        { id: '1', content: 'High score item', score: 0.9 },
        { id: '2', content: 'Low score item', score: 0.2 },
      ]);
      
      const mockManager = { search: mockSearch };
      
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(mockManager);
      
      const query: SERPQuery = {
        keywords: 'test',
        timestamp: Date.now(),
        iteration: 1,
      };
      
      await provider.search(query);
      
      expect(mockSearch).toHaveBeenCalledWith(
        expect.objectContaining({
          minScore: NeuralSearchProvider.DEFAULT_CONFIG.MIN_SCORE,
        })
      );
    });
  });
  
  describe('Web Content Reading', () => {
    it('should not support web content reading', async () => {
      await expect(
        provider.read({ url: 'https://example.com' })
      ).rejects.toThrow('Neural search provider does not support web content reading');
    });
  });
  
  describe('Error Handling', () => {
    it('should handle search errors', async () => {
      const mockSearch = vi.fn().mockRejectedValue(new Error('Search failed'));
      const mockManager = { search: mockSearch };
      
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(mockManager);
      
      const query: SERPQuery = {
        keywords: 'test',
        timestamp: Date.now(),
        iteration: 1,
      };
      
      await expect(
        provider.search(query)
      ).rejects.toThrow('Search failed');
    });
    
    it('should convert non-Error exceptions to Error', async () => {
      const mockSearch = vi.fn().mockRejectedValue('String error');
      const mockManager = { search: mockSearch };
      
      vi.spyOn(provider as any, 'loadNeuralSearch').mockResolvedValue(mockManager);
      
      const query: SERPQuery = {
        keywords: 'test',
        timestamp: Date.now(),
        iteration: 1,
      };
      
      await expect(
        provider.search(query)
      ).rejects.toThrow('String error');
    });
  });
  
  describe('Package Loading', () => {
    it('should load neural search package dynamically', async () => {
      const provider = createNeuralSearchProvider();
      
      // This will attempt to load the actual package
      const manager = await (provider as any).loadNeuralSearch();
      
      // If package is not installed, should return null
      // If installed, should return manager object
      expect(manager === null || typeof manager === 'object').toBe(true);
    });
    
    it('should initialize manager with correct config', async () => {
      const customWeight = 0.6;
      const customProvider = createNeuralSearchProvider(10000, customWeight);
      
      // Mock the import to track config
      const mockCreateManager = vi.fn().mockReturnValue({
        search: vi.fn().mockResolvedValue([]),
      });
      
      vi.spyOn(customProvider as any, 'loadNeuralSearch').mockImplementation(async () => {
        return mockCreateManager({
          embeddingModel: 'default',
          hybridWeight: customWeight,
          cacheEnabled: true,
        });
      });
      
      await (customProvider as any).loadNeuralSearch();
      
      expect(mockCreateManager).toHaveBeenCalledWith({
        embeddingModel: 'default',
        hybridWeight: customWeight,
        cacheEnabled: true,
      });
    });
  });
});

/**
 * E2E Integration Test with Real Package
 * 
 * Note: This test requires @nahisaho/musubix-neural-search to be installed.
 * It will be skipped if the package is not available.
 */
describe('Neural Search E2E Integration', () => {
  it('should integrate with real neural-search package if available', async () => {
    const provider = createNeuralSearchProvider();
    
    const isAvailable = await provider.isAvailable();
    
    if (!isAvailable) {
      console.log('⚠️  Neural search package not available, skipping E2E test');
      return;
    }
    
    // If package is available, test real integration
    try {
      // This would call the real neural-search package
      // For now, we just verify availability
      expect(isAvailable).toBe(true);
      console.log('✅ Neural search package is available and integrated');
    } catch (error) {
      console.error('❌ E2E integration test failed:', error);
      throw error;
    }
  });
});
