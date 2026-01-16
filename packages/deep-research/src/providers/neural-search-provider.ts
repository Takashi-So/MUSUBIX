// Neural Search Provider
// TSK-DR-023
// REQ: REQ-DR-INT-003
// DES: DES-DR-v3.4.0 Section 5.2

import type { SearchProvider, SERPQuery, SearchResult, WebReadRequest, WebContent } from '../types/index.js';

/**
 * Neural Search Provider
 * 
 * Integrates with @nahisaho/musubix-neural-search for semantic code search.
 * 
 * Features:
 * - Embedding-based semantic search
 * - Hybrid ranking (BM25 + vector similarity)
 * - Context-aware scoring
 * - Learning-based pruning
 * - Local knowledge base search
 * 
 * REQ: REQ-DR-INT-003 - Neural Search integration
 * DES: DES-DR-v3.4.0 Section 5.2 - Neural Search integration pattern
 */
export class NeuralSearchProvider implements SearchProvider {
  name = 'Neural Search';
  
  private readonly hybridWeight: number; // Weight for BM25 vs embedding scores
  
  /**
   * Configuration for hybrid ranking
   */
  static readonly DEFAULT_CONFIG = {
    TIMEOUT: 10000,
    HYBRID_WEIGHT: 0.7, // 0.7 = 70% embedding, 30% BM25
    MAX_RESULTS: 10,
    MIN_SCORE: 0.3,
  } as const;
  
  constructor(
    _timeout: number = NeuralSearchProvider.DEFAULT_CONFIG.TIMEOUT,
    hybridWeight: number = NeuralSearchProvider.DEFAULT_CONFIG.HYBRID_WEIGHT
  ) {
    this.hybridWeight = hybridWeight;
  }
  
  /**
   * Search using neural semantic search
   */
  async search(query: SERPQuery): Promise<SearchResult[]> {
    console.log(`🔍 Neural Search: "${query.keywords}" (semantic)...`);
    
    try {
      // Check if neural-search package is available
      const neuralSearch = await this.loadNeuralSearch();
      
      if (!neuralSearch) {
        throw new Error('Neural search package not available');
      }
      
      // Perform semantic search
      const searchResults = await neuralSearch.search({
        query: query.keywords,
        topK: query.topK || NeuralSearchProvider.DEFAULT_CONFIG.MAX_RESULTS,
        hybridWeight: this.hybridWeight,
        minScore: NeuralSearchProvider.DEFAULT_CONFIG.MIN_SCORE,
      });
      
      // Convert to SearchResult format
      const results: SearchResult[] = searchResults.map((result: any) => ({
        title: result.title || this.extractTitle(result.content),
        url: result.url || this.generateLocalUrl(result.id),
        snippet: this.extractSnippet(result.content, query.keywords),
        score: result.score,
        source: 'neural-search',
      }));
      
      console.log(`✅ Neural Search returned ${results.length} results`);
      
      return results;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`❌ Neural Search failed:`, err.message);
      throw err;
    }
  }
  
  /**
   * Read web content (not applicable for neural search, delegates to JinaProvider)
   */
  async read(_request: WebReadRequest): Promise<WebContent> {
    // Neural search works with local knowledge base, not web content
    // This method should not be called for neural search
    throw new Error('Neural search provider does not support web content reading');
  }
  
  /**
   * Extract title from content
   */
  private extractTitle(content: string): string {
    // Extract first line or first 50 characters as title
    const firstLine = content.split('\n')[0];
    return firstLine.length > 50 ? firstLine.substring(0, 47) + '...' : firstLine;
  }
  
  /**
   * Extract snippet around keywords
   */
  private extractSnippet(content: string, keywords: string): string {
    const maxLength = 200;
    
    // Try to find keyword in content
    const lowerContent = content.toLowerCase();
    const lowerKeywords = keywords.toLowerCase();
    const index = lowerContent.indexOf(lowerKeywords);
    
    if (index !== -1) {
      // Extract snippet around keyword
      const start = Math.max(0, index - 50);
      const end = Math.min(content.length, index + 150);
      let snippet = content.substring(start, end);
      
      // Add ellipsis
      if (start > 0) snippet = '...' + snippet;
      if (end < content.length) snippet = snippet + '...';
      
      return snippet;
    }
    
    // Fallback: return first maxLength characters
    return content.length > maxLength 
      ? content.substring(0, maxLength - 3) + '...'
      : content;
  }
  
  /**
   * Generate local URL for knowledge base item
   */
  private generateLocalUrl(id: string): string {
    return `local://knowledge/${id}`;
  }
  
  /**
   * Load neural-search package dynamically
   */
  private async loadNeuralSearch(): Promise<any> {
    try {
      // Try to import the package (dynamic import, may not be installed)
      const module = await import('@nahisaho/musubix-neural-search' as any);
      
      // Create enhanced neural search manager
      const { createEnhancedNeuralSearchManager } = module;
      
      if (!createEnhancedNeuralSearchManager) {
        console.warn('⚠️  createEnhancedNeuralSearchManager not found in module');
        return null;
      }
      
      // Initialize neural search manager
      const manager = createEnhancedNeuralSearchManager({
        embeddingModel: 'default',
        hybridWeight: this.hybridWeight,
        cacheEnabled: true,
      });
      
      return manager;
    } catch (error) {
      // Package not installed or not available
      console.warn('⚠️  @nahisaho/musubix-neural-search not available');
      return null;
    }
  }
  
  /**
   * Check if neural search is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      const neuralSearch = await this.loadNeuralSearch();
      return neuralSearch !== null;
    } catch (error) {
      return false;
    }
  }
}

/**
 * Create a neural search provider instance
 */
export function createNeuralSearchProvider(
  timeout?: number,
  hybridWeight?: number
): NeuralSearchProvider {
  return new NeuralSearchProvider(timeout, hybridWeight);
}
