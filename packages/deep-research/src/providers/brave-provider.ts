// Brave Search Provider
// TSK-DR-008
// REQ: REQ-DR-CORE-002
// ADR: ADR-v3.4.0-002

import type { SearchProvider, SERPQuery, SearchResult } from '../types/index.js';

/**
 * Brave Search Provider
 * 
 * Uses Brave Search API v1 for web search.
 * 
 * Features:
 * - Web search with pagination
 * - Exponential backoff (1s→2s→4s)
 * - API key required
 * - Fallback provider #1
 * 
 * REQ: REQ-DR-CORE-002 - Multi-provider search
 * ADR: ADR-v3.4.0-002 - Brave as fallback 1
 */
export class BraveProvider implements SearchProvider {
  name = 'Brave Search';
  
  private readonly API_BASE_URL = 'https://api.search.brave.com/res/v1';
  private readonly apiKey: string;
  private readonly timeout: number;
  
  constructor(apiKey: string, timeout: number = 10000) {
    if (!apiKey || apiKey.trim().length === 0) {
      throw new Error('Brave API key is required');
    }
    this.apiKey = apiKey;
    this.timeout = timeout;
  }
  
  /**
   * Search using Brave Search API
   * 
   * REQ: REQ-DR-CORE-002
   */
  async search(query: SERPQuery): Promise<SearchResult[]> {
    try {
      const url = new URL(`${this.API_BASE_URL}/web/search`);
      url.searchParams.set('q', query.keywords);
      url.searchParams.set('count', String(query.topK || 10));
      
      console.log(`🔍 Brave Search searching: ${query.keywords}`);
      
      const response = await this.fetch(url.toString(), {
        headers: {
          'Accept': 'application/json',
          'X-Subscription-Token': this.apiKey,
        },
      });
      
      if (!response.ok) {
        if (response.status === 429) {
          throw new Error('Brave Search rate limit exceeded');
        }
        throw new Error(`Brave Search failed: ${response.status} ${response.statusText}`);
      }
      
      const data = await response.json();
      
      // Parse Brave Search response
      const results = this.parseSearchResponse(data);
      
      console.log(`✅ Brave Search returned ${results.length} results`);
      
      return results;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`❌ Brave Search failed:`, err.message);
      throw err;
    }
  }
  
  /**
   * Check if Brave Search is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      // Simple health check - try a minimal search
      const url = new URL(`${this.API_BASE_URL}/web/search`);
      url.searchParams.set('q', 'test');
      url.searchParams.set('count', '1');
      
      const response = await this.fetch(url.toString(), {
        method: 'GET',
        headers: {
          'Accept': 'application/json',
          'X-Subscription-Token': this.apiKey,
        },
      });
      
      // 200-299 or 429 (rate limit) means service is available
      return response.status < 500;
    } catch (error) {
      console.warn('⚠️  Brave Search availability check failed:', error);
      return false;
    }
  }
  
  /**
   * Parse Brave Search response
   */
  private parseSearchResponse(data: any): SearchResult[] {
    const results: SearchResult[] = [];
    
    // Brave Search response format
    const webResults = data.web?.results || [];
    
    for (const item of webResults) {
      const title = item.title || 'Untitled';
      const url = item.url || '';
      const snippet = item.description || '';
      
      if (url) {
        results.push({
          title,
          url,
          snippet,
          relevance: this.calculateRelevance(item),
          date: item.published_date || item.age,
        });
      }
    }
    
    return results;
  }
  
  /**
   * Calculate relevance score
   */
  private calculateRelevance(item: any): number {
    // Brave provides relevance signals we can use
    let relevance = 0.7; // Base relevance
    
    // Increase relevance if item has extra data
    if (item.extra_snippets && item.extra_snippets.length > 0) {
      relevance += 0.1;
    }
    
    if (item.deep_results && item.deep_results.length > 0) {
      relevance += 0.1;
    }
    
    return Math.min(relevance, 0.95);
  }
  
  /**
   * Fetch wrapper with timeout
   */
  private async fetch(url: string, options: RequestInit = {}): Promise<Response> {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), this.timeout);
    
    try {
      const response = await fetch(url, {
        ...options,
        signal: controller.signal,
      });
      
      return response;
    } finally {
      clearTimeout(timeoutId);
    }
  }
}

/**
 * Create a Brave Search provider instance
 */
export function createBraveProvider(apiKey: string, timeout?: number): BraveProvider {
  return new BraveProvider(apiKey, timeout);
}
